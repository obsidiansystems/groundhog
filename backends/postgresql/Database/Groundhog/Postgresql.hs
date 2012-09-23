{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, FlexibleContexts, OverloadedStrings, TypeFamilies #-}
module Database.Groundhog.Postgresql
    ( withPostgresqlPool
    , withPostgresqlConn
    , runPostgresqlPool
    , runPostgresqlConn
    , Postgresql
    , module Database.Groundhog
    ) where

import Database.Groundhog
import Database.Groundhog.Core
import Database.Groundhog.Generic
import Database.Groundhog.Generic.Migration hiding (MigrationPack(..))
import qualified Database.Groundhog.Generic.Migration as GM
import Database.Groundhog.Generic.Sql.String
import qualified Database.Groundhog.Generic.PersistBackendHelpers as H

import qualified Database.PostgreSQL.Simple as PG
import qualified Database.PostgreSQL.Simple.BuiltinTypes as PG
import qualified Database.PostgreSQL.Simple.Internal as PG
import qualified Database.PostgreSQL.Simple.ToField as PGTF
import qualified Database.PostgreSQL.Simple.FromField as PGFF
import qualified Database.PostgreSQL.Simple.Types as PG
import Database.PostgreSQL.Simple.Ok (Ok (..))
import qualified Database.PostgreSQL.LibPQ as LibPQ

import Control.Arrow ((***))
import Control.Exception (throw)
import Control.Monad (forM, liftM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Control (MonadBaseControl)
import Control.Monad.Trans.Reader (ask)
import Data.ByteString.Char8 (ByteString, pack, unpack)
import Data.Either (partitionEithers)
import Data.Function (on)
import Data.Int (Int64)
import Data.IORef
import Data.List (groupBy, intercalate)
import Data.Monoid
import Data.Conduit.Pool
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Time.LocalTime (localTimeToUTC, utc)

-- typical operations for connection: OPEN, BEGIN, COMMIT, ROLLBACK, CLOSE
newtype Postgresql = Postgresql PG.Connection

instance DbDescriptor Postgresql where
  type AutoKeyType Postgresql = Int64

instance (MonadBaseControl IO m, MonadIO m) => PersistBackend (DbPersist Postgresql m) where
  {-# SPECIALIZE instance PersistBackend (DbPersist Postgresql IO) #-}
  type PhantomDb (DbPersist Postgresql m) = Postgresql
  insert v = insert' v
  insertBy u v = H.insertBy escapeS queryRawTyped' u v
  insertByAll v = H.insertByAll escapeS queryRawTyped' v
  replace k v = H.replace escapeS queryRawTyped' executeRaw' insertIntoConstructorTable k v
  select options = H.select escapeS queryRawTyped' "" renderCond' options
  selectAll = H.selectAll escapeS queryRawTyped'
  get k = H.get escapeS queryRawTyped' k
  getBy k = H.getBy escapeS queryRawTyped' k
  update upds cond = H.update escapeS executeRaw' renderCond' upds cond
  delete cond = H.delete escapeS executeRaw' renderCond' cond
  deleteByKey k = H.deleteByKey escapeS executeRaw' k
  count cond = H.count escapeS queryRawTyped' renderCond' cond
  countAll fakeV = H.countAll escapeS queryRawTyped' fakeV
  project p options = H.project escapeS queryRawTyped' "" renderCond' p options
  migrate fakeV = migrate' fakeV

  executeRaw _ query ps = executeRaw' (fromString query) ps
  queryRaw _ query ps f = queryRaw' (fromString query) ps f

  insertList l = insertList' l
  getList k = getList' k

--{-# SPECIALIZE withPostgresqlPool :: String -> Int -> (Pool Postgresql -> IO a) -> IO a #-}
withPostgresqlPool :: (MonadBaseControl IO m, MonadIO m)
               => String
               -> Int -- ^ number of connections to open
               -> (Pool Postgresql -> m a)
               -> m a
withPostgresqlPool s connCount f = liftIO (createPool (open' s) close' 1 20 connCount) >>= f

{-# SPECIALIZE withPostgresqlConn :: String -> (Postgresql -> IO a) -> IO a #-}
{-# INLINE withPostgresqlConn #-}
withPostgresqlConn :: (MonadBaseControl IO m, MonadIO m)
               => String
               -> (Postgresql -> m a)
               -> m a
withPostgresqlConn s = bracket (liftIO $ open' s) (liftIO . close')

{-# SPECIALIZE runPostgresqlPool :: DbPersist Postgresql IO a -> Pool Postgresql -> IO a #-}
runPostgresqlPool :: (MonadBaseControl IO m, MonadIO m) => DbPersist Postgresql m a -> Pool Postgresql -> m a
runPostgresqlPool f pconn = withResource pconn $ runPostgresqlConn f

{-# SPECIALIZE runPostgresqlConn :: DbPersist Postgresql IO a -> Postgresql -> IO a #-}
{-# INLINE runPostgresqlConn #-}
runPostgresqlConn :: (MonadBaseControl IO m, MonadIO m) => DbPersist Postgresql m a -> Postgresql -> m a
runPostgresqlConn f conn@(Postgresql c) = do
  liftIO $ PG.begin c
  x <- onException (runDbPersist f conn) (liftIO $ PG.rollback c)
  liftIO $ PG.commit c
  return x

open' :: String -> IO Postgresql
open' s = do
  conn <- PG.connectPostgreSQL $ pack s
  PG.execute_ conn $ getStatement "SET client_min_messages TO WARNING"
  return $ Postgresql conn

close' :: Postgresql -> IO ()
close' (Postgresql conn) = PG.close conn

{-# SPECIALIZE insert' :: PersistEntity v => v -> DbPersist Postgresql IO (AutoKey v) #-}
{-# INLINE insert' #-}
insert' :: (PersistEntity v, MonadBaseControl IO m, MonadIO m) => v -> DbPersist Postgresql m (AutoKey v)
insert' v = do
  -- constructor number and the rest of the field values
  vals <- toEntityPersistValues' v
  let e = entityDef v
  let name = persistName v
  let constructorNum = fromPrimitivePersistValue proxy (head vals)

  liftM fst $ if isSimple (constructors e)
    then do
      let constr = head $ constructors e
      let query = insertIntoConstructorTable False name constr
      case constrAutoKeyName constr of
        Nothing -> executeRaw' query (tail vals) >> pureFromPersistValue []
        Just _  -> do
          x <- queryRaw' query (tail vals) id
          case x of
            Just xs -> pureFromPersistValue xs
            Nothing -> pureFromPersistValue []
    else do
      let constr = constructors e !! constructorNum
      let cName = name ++ [delim] ++ constrName constr
      let query = "INSERT INTO " <> escapeS (fromString name) <> "(discr)VALUES(?)RETURNING(id)"
      rowid <- queryRaw' query (take 1 vals) getKey
      let cQuery = insertIntoConstructorTable True cName constr
      executeRaw' cQuery $ rowid:(tail vals)
      pureFromPersistValue [rowid]

insertIntoConstructorTable :: Bool -> String -> ConstructorDef -> StringS
insertIntoConstructorTable withId tName c = "INSERT INTO " <> escapeS (fromString tName) <> "(" <> fieldNames <> ")VALUES(" <> placeholders <> ")" <> returning where
  (fields, returning) = case constrAutoKeyName c of
    Just idName | withId    -> ((idName, dbType (0 :: Int64)):constrParams c, mempty)
                | otherwise -> (constrParams c, "RETURNING(" <> escapeS (fromString idName) <> ")")
    _                       -> (constrParams c, mempty)
  fieldNames   = renderFields escapeS fields
  placeholders = renderFields (const $ fromChar '?') fields

insertList' :: forall m a.(MonadBaseControl IO m, MonadIO m, PersistField a) => [a] -> DbPersist Postgresql m Int64
insertList' (l :: [a]) = do
  let mainName = "List" <> delim' <> delim' <> fromString (persistName (undefined :: a))
  k <- queryRaw' ("INSERT INTO " <> escapeS mainName <> " DEFAULT VALUES RETURNING(id)") [] getKey
  let valuesName = mainName <> delim' <> "values"
  let fields = [("ord", dbType (0 :: Int)), ("value", dbType (undefined :: a))]
  let query = "INSERT INTO " <> escapeS valuesName <> "(id," <> renderFields escapeS fields <> ")VALUES(?," <> renderFields (const $ fromChar '?') fields <> ")"
  let go :: Int -> [a] -> DbPersist Postgresql m ()
      go n (x:xs) = do
       x' <- toPersistValues x
       executeRaw' query $ (k:) . (toPrimitivePersistValue proxy n:) . x' $ []
       go (n + 1) xs
      go _ [] = return ()
  go 0 l
  return $ fromPrimitivePersistValue proxy k
  
getList' :: forall m a.(MonadBaseControl IO m, MonadIO m, PersistField a) => Int64 -> DbPersist Postgresql m [a]
getList' k = do
  let mainName = "List" <> delim' <> delim' <> fromString (persistName (undefined :: a))
  let valuesName = mainName <> delim' <> "values"
  let value = ("value", dbType (undefined :: a))
  let query = "SELECT " <> renderFields escapeS [value] <> " FROM " <> escapeS valuesName <> " WHERE id=? ORDER BY ord"
  queryRaw' query [toPrimitivePersistValue proxy k] $ mapAllRows (liftM fst . fromPersistValues)

--TODO: consider removal
{-# SPECIALIZE getKey :: RowPopper (DbPersist Postgresql IO) -> DbPersist Postgresql IO PersistValue #-}
getKey :: MonadIO m => RowPopper (DbPersist Postgresql m) -> DbPersist Postgresql m PersistValue
getKey pop = pop >>= \(Just [k]) -> return k

----------

executeRaw' :: MonadIO m => StringS -> [PersistValue] -> DbPersist Postgresql m ()
executeRaw' query vals = do
  --liftIO $ print $ fromStringS query ""
  Postgresql conn <- DbPersist ask
  let stmt = getStatement query
  liftIO $ do
    _ <- PG.execute conn stmt (map P vals)
    return ()

renderCond' :: (PersistEntity v, Constructor c) => Cond v c -> Maybe (RenderS StringS)
renderCond' = renderCond proxy escapeS renderEquals renderNotEquals where
  renderEquals a b = a <> " IS NOT DISTINCT FROM " <> b
  renderNotEquals a b = a <> " IS DISTINCT FROM " <> b

escapeS :: StringS -> StringS
escapeS a = let q = fromChar '"' in q <> a <> q

delim' :: StringS
delim' = fromChar delim

toEntityPersistValues' :: (MonadBaseControl IO m, MonadIO m, PersistEntity v) => v -> DbPersist Postgresql m [PersistValue]
toEntityPersistValues' = liftM ($ []) . toEntityPersistValues

--- MIGRATION

migrate' :: (PersistEntity v, MonadBaseControl IO m, MonadIO m) => v -> Migration (DbPersist Postgresql m)
migrate' = migrateRecursively (migrateEntity migrationPack) (migrateList migrationPack)

migrationPack :: (MonadBaseControl IO m, MonadIO m) => GM.MigrationPack (DbPersist Postgresql m) DbType
migrationPack = GM.MigrationPack
  compareColumns
  compareRefs
  compareUniqs
  checkTable
  migTriggerOnDelete
  migTriggerOnUpdate
  GM.defaultMigConstr
  escape
  "SERIAL PRIMARY KEY UNIQUE"
  "INT8"
  mainTableId
  defaultPriority
  simplifyType
  (\uniques refs -> ([], map (\(UniqueDef' uName fields) -> AddUniqueConstraint uName fields) uniques ++ map AddReference refs))
  showColumn
  showAlterDb

showColumn :: Column DbType -> String
showColumn (Column n nu t def) = concat
    [ escape n
    , " "
    , showSqlType t
    , " "
    , if nu then "NULL" else "NOT NULL"
    , case def of
        Nothing -> ""
        Just s  -> " DEFAULT " ++ s
    ]

checkFunction :: (MonadBaseControl IO m, MonadIO m) => String -> DbPersist Postgresql m (Maybe String)
checkFunction name = do
  x <- queryRaw' "SELECT p.prosrc FROM pg_catalog.pg_namespace n INNER JOIN pg_catalog.pg_proc p ON p.pronamespace = n.oid WHERE n.nspname = 'public' AND p.proname = ?" [toPrimitivePersistValue proxy name] id
  case x of
    Nothing  -> return Nothing
    Just src -> return (fst $ fromPurePersistValues proxy src)

checkTrigger :: (MonadBaseControl IO m, MonadIO m) => String -> DbPersist Postgresql m (Maybe String)
checkTrigger name = do
  x <- queryRaw' "SELECT action_statement FROM information_schema.triggers WHERE trigger_name = ?" [toPrimitivePersistValue proxy name] id
  case x of
    Nothing  -> return Nothing
    Just src -> return (fst $ fromPurePersistValues proxy src)

-- it handles only delete operations. So far when list or tuple replace is not allowed, it is ok
migTriggerOnDelete :: (MonadBaseControl IO m, MonadIO m) => String -> [(String, String)] -> DbPersist Postgresql m (Bool, [AlterDB DbType])
migTriggerOnDelete name deletes = do
  let funcName = name
  let trigName = name
  func <- checkFunction funcName
  trig <- checkTrigger trigName
  let funcBody = "BEGIN " ++ concatMap snd deletes ++ "RETURN NEW;END;"
      addFunction = CreateOrReplaceFunction $ "CREATE OR REPLACE FUNCTION " ++ escape funcName ++ "() RETURNS trigger AS $$" ++ funcBody ++ "$$ LANGUAGE plpgsql"
      funcMig = case func of
        Nothing | null deletes -> []
        Nothing   -> [addFunction]
        Just body -> if null deletes -- remove old trigger if a datatype earlier had fields of ephemeral types
          then [DropFunction funcName]
          else if body == funcBody
            then []
            -- this can happen when an ephemeral field was added or removed.
            else [DropFunction funcName, addFunction]

      trigBody = "EXECUTE PROCEDURE " ++ escape funcName ++ "()"
      addTrigger = AddTriggerOnDelete trigName name trigBody
      (trigExisted, trigMig) = case trig of
        Nothing | null deletes -> (False, [])
        Nothing   -> (False, [addTrigger])
        Just body -> (True, if null deletes -- remove old trigger if a datatype earlier had fields of ephemeral types
          then [DropTrigger trigName name]
          else if body == trigBody
            then []
            -- this can happen when an ephemeral field was added or removed.
            else [DropTrigger trigName name, addTrigger])
  return (trigExisted, funcMig ++ trigMig)
      
-- | Table name and a  list of field names and according delete statements
-- assume that this function is called only for ephemeral fields
migTriggerOnUpdate :: (MonadBaseControl IO m, MonadIO m) => String -> String -> String -> DbPersist Postgresql m (Bool, [AlterDB DbType])
migTriggerOnUpdate name fieldName del = do
  let funcName = name ++ delim : fieldName
  let trigName = name ++ delim : fieldName
  func <- checkFunction funcName
  trig <- checkTrigger trigName
  let funcBody = "BEGIN " ++ del ++ "RETURN NEW;END;"
      addFunction = CreateOrReplaceFunction $ "CREATE OR REPLACE FUNCTION " ++ escape funcName ++ "() RETURNS trigger AS $$" ++ funcBody ++ "$$ LANGUAGE plpgsql"
      funcMig = case func of
        Nothing   -> [addFunction]
        Just body -> if body == funcBody
            then []
            -- this can happen when an ephemeral field was added or removed.
            else [DropFunction funcName, addFunction]

      trigBody = "EXECUTE PROCEDURE " ++ escape funcName ++ "()"
      addTrigger = AddTriggerOnUpdate trigName name fieldName trigBody
      (trigExisted, trigMig) = case trig of
        Nothing   -> (False, [addTrigger])
        Just body -> (True, if body == trigBody
            then []
            -- this can happen when an ephemeral field was added or removed.
            else [DropTrigger trigName name, addTrigger])
  return (trigExisted, funcMig ++ trigMig)
  
checkTable :: (MonadBaseControl IO m, MonadIO m) => String -> DbPersist Postgresql m (Maybe (Either [String] (TableInfo DbType)))
checkTable name = do
  table <- queryRaw' "SELECT * FROM information_schema.tables WHERE table_name=?" [toPrimitivePersistValue proxy name] id
  case table of
    Just _ -> do
      -- omit primary keys
      cols <- queryRaw' "SELECT c.column_name, c.is_nullable, c.udt_name, c.column_default FROM information_schema.columns c WHERE c.table_name=? AND c.column_name NOT IN (SELECT c.column_name FROM information_schema.table_constraints tc INNER JOIN information_schema.constraint_column_usage u ON tc.constraint_catalog = u.constraint_catalog AND tc.constraint_schema=u.constraint_schema AND tc.constraint_name=u.constraint_name INNER JOIN information_schema.columns c ON u.table_catalog=c.table_catalog AND u.table_schema=c.table_schema AND u.table_name=c.table_name AND u.column_name=c.column_name WHERE tc.constraint_type='PRIMARY KEY' AND tc.table_name=?) ORDER BY c.ordinal_position" [toPrimitivePersistValue proxy name, toPrimitivePersistValue proxy name] (mapAllRows $ return . getColumn name . fst . fromPurePersistValues proxy)
      let (col_errs, cols') = partitionEithers cols
      
      uniqRows <- queryRaw' "SELECT u.constraint_name, u.column_name FROM information_schema.table_constraints tc INNER JOIN information_schema.constraint_column_usage u ON tc.constraint_catalog=u.constraint_catalog AND tc.constraint_schema=u.constraint_schema AND tc.constraint_name=u.constraint_name WHERE u.table_name=? AND tc.constraint_type='UNIQUE' ORDER BY u.constraint_name, u.column_name" [toPrimitivePersistValue proxy name] (mapAllRows $ return . fst . fromPurePersistValues proxy)
      let mkUniq us = UniqueDef' (fst $ head us) (map snd us)
      let uniqs' = map mkUniq $ groupBy ((==) `on` fst) uniqRows
      references <- checkTableReferences name
      primaryKeyResult <- checkPrimaryKey name
      let (primaryKey, uniqs'') = case primaryKeyResult of
            (Left primaryKeyName) -> (primaryKeyName, uniqs')
            (Right u) -> (Nothing, u:uniqs')
      return $ Just $ case col_errs of
        []   -> Right $ TableInfo primaryKey cols' uniqs'' references
        errs -> Left errs
    Nothing -> return Nothing

checkPrimaryKey :: (MonadBaseControl IO m, MonadIO m) => String -> DbPersist Postgresql m (Either (Maybe String) UniqueDef')
checkPrimaryKey name = do
  uniqRows <- queryRaw' "SELECT u.constraint_name, u.column_name FROM information_schema.table_constraints tc INNER JOIN information_schema.constraint_column_usage u ON tc.constraint_catalog = u.constraint_catalog AND tc.constraint_schema=u.constraint_schema AND tc.constraint_name=u.constraint_name WHERE tc.constraint_type='PRIMARY KEY' AND tc.table_name=?" [toPrimitivePersistValue proxy name] (mapAllRows $ return . fst . fromPurePersistValues proxy)
  let mkUniq us = UniqueDef' (fst $ head us) (map snd us)
  return $ case uniqRows of
    [] -> Left Nothing
    [(_, primaryKeyName)] -> Left $ Just primaryKeyName
    us -> Right $ mkUniq us

getColumn :: String -> (String, String, String, Maybe String) -> Either String (Column DbType)
getColumn _ (column_name, is_nullable, udt_name, d) = case readSqlType udt_name of
      Left s -> Left s
      Right t -> Right $ Column column_name (is_nullable == "YES") t d

checkTableReferences :: (MonadBaseControl IO m, MonadIO m) => String -> DbPersist Postgresql m [(Maybe String, Reference)]
checkTableReferences tableName = do
  let sql = "SELECT c.conname, c.foreign_table || '', a_child.attname AS child, a_parent.attname AS parent FROM (SELECT r.confrelid::regclass AS foreign_table, r.conrelid, r.confrelid, unnest(r.conkey) AS conkey, unnest(r.confkey) AS confkey, r.conname FROM pg_catalog.pg_constraint r WHERE r.conrelid = ?::regclass AND r.contype = 'f') AS c INNER JOIN pg_attribute a_parent ON a_parent.attnum = c.confkey AND a_parent.attrelid = c.confrelid INNER JOIN pg_attribute a_child ON a_child.attnum = c.conkey AND a_child.attrelid = c.conrelid ORDER BY c.conname"
  x <- queryRaw' sql [toPrimitivePersistValue proxy $ escape tableName] $ mapAllRows (return . fst . fromPurePersistValues proxy)
  -- (refName, (parentTable, (childColumn, parentColumn)))
  let mkReference xs = (Just refName, (parentTable, map (snd . snd) xs)) where
        (refName, (parentTable, _)) = head xs
      references = map mkReference $ groupBy ((==) `on` fst) x
  return references

showAlterDb :: AlterDB DbType -> SingleMigration
showAlterDb (AddTable s) = Right [(False, defaultPriority, s)]
showAlterDb (AlterTable t _ _ _ alts) = Right $ map (showAlterTable t) alts
showAlterDb (DropTrigger trigName tName) = Right [(False, triggerPriority, "DROP TRIGGER " ++ escape trigName ++ " ON " ++ escape tName)]
showAlterDb (AddTriggerOnDelete trigName tName body) = Right [(False, triggerPriority, "CREATE TRIGGER " ++ escape trigName ++ " AFTER DELETE ON " ++ escape tName ++ " FOR EACH ROW " ++ body)]
showAlterDb (AddTriggerOnUpdate trigName tName fName body) = Right [(False, triggerPriority, "CREATE TRIGGER " ++ escape trigName ++ " AFTER UPDATE OF " ++ escape fName ++ " ON " ++ escape tName ++ " FOR EACH ROW " ++ body)]
showAlterDb (CreateOrReplaceFunction s) = Right [(False, functionPriority, s)]
showAlterDb (DropFunction funcName) = Right [(False, functionPriority, "DROP FUNCTION " ++ escape funcName ++ "()")]
                 
showAlterTable :: String -> AlterTable -> (Bool, Int, String)
showAlterTable table (AlterColumn alt) = showAlterColumn table alt
showAlterTable table (AddUniqueConstraint cname cols) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , escape table
  , " ADD CONSTRAINT "
  , escape cname
  , " UNIQUE("
  , intercalate "," $ map escape cols
  , ")"
  ])
showAlterTable table (DropConstraint cname) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , escape table
  , " DROP CONSTRAINT "
  , escape cname
  ])
showAlterTable table (AddReference (tName, columns)) = (False, referencePriority, concat
  [ "ALTER TABLE "
  , escape table
  , " ADD FOREIGN KEY("
  , our
  , ") REFERENCES "
  , escape tName
  , "("
  , foreign
  , ")"
  ]) where
  (our, foreign) = f *** f $ unzip columns
  f = intercalate ", " . map escape
showAlterTable table (DropReference name) = (False, defaultPriority,
    "ALTER TABLE " ++ escape table ++ " DROP CONSTRAINT " ++ name)

showAlterColumn :: String -> AlterColumn' -> (Bool, Int, String)
showAlterColumn table (n, Type t) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , escape table
  , " ALTER COLUMN "
  , escape n
  , " TYPE "
  , showSqlType t
  ])
showAlterColumn table (n, IsNull) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , escape table
  , " ALTER COLUMN "
  , escape n
  , " DROP NOT NULL"
  ])
showAlterColumn table (n, NotNull) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , escape table
  , " ALTER COLUMN "
  , escape n
  , " SET NOT NULL"
  ])
showAlterColumn table (_, Add col) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , escape table
  , " ADD COLUMN "
  , showColumn col
  ])
showAlterColumn table (n, Drop) = (True, defaultPriority, concat
  [ "ALTER TABLE "
  , escape table
  , " DROP COLUMN "
  , escape n
  ])
showAlterColumn table (n, AddPrimaryKey) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , escape table
  , " ADD COLUMN "
  , escape n
  , " SERIAL PRIMARY KEY UNIQUE"
  ])
showAlterColumn table (n, Default s) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , escape table
  , " ALTER COLUMN "
  , escape n
  , " SET DEFAULT "
  , s
  ])
showAlterColumn table (n, NoDefault) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , escape table
  , " ALTER COLUMN "
  , escape n
  , " DROP DEFAULT"
  ])
showAlterColumn table (n, UpdateValue s) = (False, defaultPriority, concat
  [ "UPDATE "
  , escape table
  , " SET "
  , escape n
  , "="
  , s
  , " WHERE "
  , escape n
  , " IS NULL"
  ])
    
readSqlType :: String -> Either String DbType
readSqlType "int4" = Right $ DbInt32
readSqlType "int8" = Right $ DbInt64
readSqlType "varchar" = Right $ DbString
readSqlType "date" = Right $ DbDay
readSqlType "bool" = Right $ DbBool
readSqlType "timestamp" = Right $ DbDayTime
readSqlType "timestamptz" = Right $ DbDayTimeZoned
readSqlType "float4" = Right $ DbReal
readSqlType "float8" = Right $ DbReal
readSqlType "bytea" = Right $ DbBlob
readSqlType "time" = Right $ DbTime
readSqlType a = Left $ "Unknown type: " ++ a

showSqlType :: DbType -> String
showSqlType DbString = "VARCHAR"
showSqlType DbInt32 = "INT4"
showSqlType DbInt64 = "INT8"
showSqlType DbReal = "DOUBLE PRECISION"
showSqlType DbBool = "BOOLEAN"
showSqlType DbDay = "DATE"
showSqlType DbTime = "TIME"
showSqlType DbDayTime = "TIMESTAMP"
showSqlType DbDayTimeZoned = "TIMESTAMP WITH TIME ZONE"
showSqlType DbBlob = "BYTEA"
showSqlType (DbMaybe t) = showSqlType t
showSqlType (DbList _ _) = showSqlType DbInt64
showSqlType (DbEntity Nothing _) = showSqlType DbInt64
showSqlType t = error $ "showSqlType: DbType does not have corresponding database type: " ++ show t

compareColumns :: Column DbType -> Column DbType -> Bool
compareColumns = ((==) `on` f) where
  f col = col {colType = simplifyType (colType col)}

compareUniqs :: UniqueDef' -> UniqueDef' -> Bool
compareUniqs (UniqueDef' name1 cols1) (UniqueDef' name2 cols2) = name1 == name2 && haveSameElems (==) cols1 cols2

compareRefs :: (Maybe String, Reference) -> (Maybe String, Reference) -> Bool
compareRefs (_, (tbl1, pairs1)) (_, (tbl2, pairs2)) = unescape tbl1 == unescape tbl2 && haveSameElems (==) pairs1 pairs2 where
  unescape name = if head name == '"' && last name == '"' then tail $ init name else name

-- | Converts complex datatypes that reference other data to id type DbInt64. Does not handle DbEmbedded
simplifyType :: DbType -> DbType
simplifyType (DbEntity Nothing _) = DbInt64
simplifyType (DbList _ _) = DbInt64
simplifyType x = x

defaultPriority :: Int
defaultPriority = 0

referencePriority :: Int
referencePriority = 1

functionPriority :: Int
functionPriority = 2

triggerPriority :: Int
triggerPriority = 3

mainTableId :: String
mainTableId = "id"

--- MAIN

-- It is used to escape table names and columns, which can include only symbols allowed in Haskell datatypes and '$' delimiter. We need it mostly to support names that coincide with SQL keywords
escape :: String -> String
escape s = '\"' : s ++ "\""
  
getStatement :: StringS -> PG.Query
getStatement sql = PG.Query $ T.encodeUtf8 $ T.pack $ fromStringS sql ""

queryRawTyped' :: (MonadBaseControl IO m, MonadIO m) => StringS -> [DbType] -> [PersistValue] -> (RowPopper (DbPersist Postgresql m) -> DbPersist Postgresql m a) -> DbPersist Postgresql m a
queryRawTyped' query _ vals f = queryRaw' query vals f

queryRaw' :: (MonadBaseControl IO m, MonadIO m) => StringS -> [PersistValue] -> (RowPopper (DbPersist Postgresql m) -> DbPersist Postgresql m a) -> DbPersist Postgresql m a
queryRaw' query vals f = do
  Postgresql conn <- DbPersist ask
  rawquery <- liftIO $ PG.formatQuery conn (getStatement query) (map P vals)
  -- Take raw connection
  (ret, rowRef, rowCount, getters) <- liftIO $ PG.withConnection conn $ \rawconn -> do
    -- Execute query
    mret <- LibPQ.exec rawconn rawquery
    case mret of
      Nothing -> do
        merr <- LibPQ.errorMessage rawconn
        fail $ case merr of
                 Nothing -> "Postgresql.withStmt': unknown error"
                 Just e  -> "Postgresql.withStmt': " ++ unpack e
      Just ret -> do
        -- Check result status
        status <- LibPQ.resultStatus ret
        case status of
          LibPQ.TuplesOk -> return ()
          _ -> do
            msg <- LibPQ.resStatus status
            fail $ "Postgresql.withStmt': bad result status " ++
                   show status ++ " (" ++ show msg ++ ")"

        -- Get number and type of columns
        cols <- LibPQ.nfields ret
        getters <- forM [0..cols-1] $ \col -> do
          oid <- LibPQ.ftype ret col
          case PG.oid2builtin oid of
            Nothing -> fail $ "Postgresql.withStmt': could not " ++
                              "recognize Oid of column " ++
                              show (let LibPQ.Col i = col in i) ++
                              " (counting from zero)"
            Just bt -> return $ getGetter bt $
                       PG.Field ret col $
                       PG.builtin2typname bt
        -- Ready to go!
        rowRef   <- newIORef (LibPQ.Row 0)
        rowCount <- LibPQ.ntuples ret
        return (ret, rowRef, rowCount, getters)

  f $ liftIO $ do
    row <- atomicModifyIORef rowRef (\r -> (r+1, r))
    if row == rowCount
      then return Nothing
      else liftM Just $ forM (zip getters [0..]) $ \(getter, col) -> do
        mbs <-  {-# SCC "getvalue'" #-} LibPQ.getvalue' ret row col
        case mbs of
          Nothing -> return PersistNull
          Just bs -> bs `seq` case getter mbs of
            Errors (exc:_) -> throw exc
            Errors [] -> error "Got an Errors, but no exceptions"
            Ok v  -> return v
    
-- | Avoid orphan instances.
newtype P = P PersistValue

instance PGTF.ToField P where
    toField (P (PersistString t))        = PGTF.toField t
    toField (P (PersistByteString bs)) = PGTF.toField (PG.Binary bs)
    toField (P (PersistInt64 i))       = PGTF.toField i
    toField (P (PersistDouble d))      = PGTF.toField d
    toField (P (PersistBool b))        = PGTF.toField b
    toField (P (PersistDay d))         = PGTF.toField d
    toField (P (PersistTimeOfDay t))   = PGTF.toField t
    toField (P (PersistUTCTime t))     = PGTF.toField t
    toField (P (PersistZonedTime (ZT t))) = PGTF.toField t
    toField (P PersistNull)            = PGTF.toField PG.Null

type Getter a = PG.Field -> Maybe ByteString -> Ok a

convertPV :: PGFF.FromField a => (a -> b) -> Getter b
convertPV f = (fmap f .) . PGFF.fromField

-- FIXME: check if those are correct and complete.
getGetter :: PG.BuiltinType -> Getter PersistValue
getGetter PG.Bool                  = convertPV PersistBool
getGetter PG.ByteA                 = convertPV (PersistByteString . unBinary)
getGetter PG.Char                  = convertPV PersistString
getGetter PG.Name                  = convertPV PersistString
getGetter PG.Int8                  = convertPV PersistInt64
getGetter PG.Int2                  = convertPV PersistInt64
getGetter PG.Int4                  = convertPV PersistInt64
getGetter PG.Text                  = convertPV PersistString
getGetter PG.Xml                   = convertPV PersistString
getGetter PG.Float4                = convertPV PersistDouble
getGetter PG.Float8                = convertPV PersistDouble
getGetter PG.AbsTime               = convertPV PersistUTCTime
getGetter PG.RelTime               = convertPV PersistUTCTime
getGetter PG.Money                 = convertPV PersistDouble
getGetter PG.BpChar                = convertPV PersistString
getGetter PG.VarChar               = convertPV PersistString
getGetter PG.Date                  = convertPV PersistDay
getGetter PG.Time                  = convertPV PersistTimeOfDay
getGetter PG.Timestamp             = convertPV (PersistUTCTime . localTimeToUTC utc)
getGetter PG.TimestampTZ           = convertPV (PersistZonedTime . ZT)
getGetter PG.Bit                   = convertPV PersistInt64
getGetter PG.VarBit                = convertPV PersistInt64
getGetter PG.Numeric               = convertPV (PersistDouble . fromRational)
getGetter PG.Void                  = \_ _ -> Ok PersistNull
getGetter other   = error $ "Postgresql.getGetter: type " ++
                            show other ++ " not supported."

unBinary :: PG.Binary a -> a
unBinary (PG.Binary x) = x

proxy :: Proxy Postgresql
proxy = error "Proxy Postgresql"