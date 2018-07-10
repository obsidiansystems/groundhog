{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, FlexibleContexts, OverloadedStrings, TypeFamilies, MultiParamTypeClasses, TemplateHaskell #-}

module Database.Groundhog.Postgresql
    ( withPostgresqlPool
    , withPostgresqlConn
    , createPostgresqlPool
    , runDbConn
    , Postgresql(..)
    , PgTableAnalysis(..)
    , module Database.Groundhog
    , module Database.Groundhog.Generic.Sql.Functions
    , explicitType
    , castType
    , distinctOn
    -- other
    , showSqlType
    ) where

import Database.Groundhog
import Database.Groundhog.Core
import Database.Groundhog.Expression
import Database.Groundhog.Generic
import Database.Groundhog.Generic.Migration hiding (MigrationPack(..), colIsEquivalent)
import qualified Database.Groundhog.Generic.Migration as GM
import Database.Groundhog.Generic.Sql
import Database.Groundhog.Generic.Sql.Functions
import qualified Database.Groundhog.Generic.PersistBackendHelpers as H

import qualified Database.PostgreSQL.Simple as PG
import qualified Database.PostgreSQL.Simple.Internal as PG
import qualified Database.PostgreSQL.Simple.ToField as PGTF
import qualified Database.PostgreSQL.Simple.FromField as PGFF
import qualified Database.PostgreSQL.Simple.Types as PG
import Database.PostgreSQL.Simple.Ok (Ok (..))
import qualified Database.PostgreSQL.LibPQ as LibPQ

import Control.Arrow ((***), second)
import Control.Exception (throw)
import Control.Monad (forM, liftM, liftM2, (>=>))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Logger (MonadLogger, logDebugS)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Control (MonadBaseControl)
import Control.Monad.Trans.Reader (ask)
import Data.ByteString.Char8 (pack, unpack, copy)
import Data.Char (isAlphaNum, isSpace, toUpper)
import Data.Function (on)
import Data.Int (Int64)
import Data.IORef
import Data.List (groupBy, intercalate, isPrefixOf, stripPrefix)
import Data.Maybe (fromJust, fromMaybe, isJust, mapMaybe)
import Data.Monoid hiding ((<>))
import Data.Pool
import Data.Time.LocalTime (localTimeToUTC, utc)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Scientific (Scientific, fromFloatDigits)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Text.Read (readMaybe)

-- work around for no Semigroup instance og PG.Query prior to
-- postgresql-simple 0.5.3.0
import qualified Data.ByteString as B

-- typical operations for connection: OPEN, BEGIN, COMMIT, ROLLBACK, CLOSE
newtype Postgresql = Postgresql PG.Connection

instance DbDescriptor Postgresql where
  type AutoKeyType Postgresql = Int64
  type QueryRaw Postgresql = Snippet Postgresql
  backendName _ = "postgresql"

instance SqlDb Postgresql where
  append a b = mkExpr $ operator 50 "||" a b
  signum' x = mkExpr $ function "sign" [toExpr x]
  quotRem' x y = (mkExpr $ operator 70 "/" x y, mkExpr $ operator 70 "%" x y)
  equalsOperator a b = a <> " IS NOT DISTINCT FROM " <> b
  notEqualsOperator a b = a <> " IS DISTINCT FROM " <> b

instance FloatingSqlDb Postgresql where
  log' x = mkExpr $ function "ln" [toExpr x]
  logBase' b x = log (liftExpr x) / log (liftExpr b)


data PgTableAnalysis = PgTableAnalysis
  { _pgTableAnalysis_tables :: Set QualifiedName
  , _pgTableAnalysis_constraints :: Map QualifiedName (Map String (Set (Maybe String, String)))
  , _pgTableAnalysis_columns :: Map QualifiedName [Column]
  , _pgTableAnalysis_indices :: Map QualifiedName (Set (Maybe String, QualifiedName))
  , _pgTableAnalysis_references :: Map QualifiedName (Set (String, ((QualifiedName, String, String), (String, String))))
  } deriving (Eq, Show)

instance (MonadBaseControl IO m, MonadIO m, MonadLogger m) => PersistBackend (DbPersist Postgresql m) where
  type PhantomDb (DbPersist Postgresql m) = Postgresql
  type TableAnalysis (DbPersist Postgresql m) = PgTableAnalysis
  insert v = insert' v
  insert_ v = insert_' v
  insertBy u v = H.insertBy renderConfig queryRaw' True u v
  insertByAll v = H.insertByAll renderConfig queryRaw' True v
  replace k v = H.replace renderConfig queryRaw' executeRaw' (insertIntoConstructorTable False) k v
  replaceBy k v = H.replaceBy renderConfig executeRaw' k v
  select options = H.select renderConfig queryRaw' preColumns "" options
  selectAll = H.selectAll renderConfig queryRaw'
  get k = H.get renderConfig queryRaw' k
  getBy k = H.getBy renderConfig queryRaw' k
  update upds cond = H.update renderConfig executeRaw' upds cond
  delete cond = H.delete renderConfig executeRaw' cond
  deleteBy k = H.deleteBy renderConfig executeRaw' k
  deleteAll v = H.deleteAll renderConfig executeRaw' v
  count cond = H.count renderConfig queryRaw' cond
  countAll fakeV = H.countAll renderConfig queryRaw' fakeV
  project p options = H.project renderConfig queryRaw' preColumns "" p options
  migrate tableInfo fakeV = migrate' tableInfo fakeV

  executeRaw _ query ps = executeRaw' (fromString query) ps
  queryRaw _ query ps f = queryRaw' (fromString query) ps f

  insertList l = insertList' l
  getList k = getList' k

instance (MonadBaseControl IO m, MonadIO m, MonadLogger m) => SchemaAnalyzer (DbPersist Postgresql m) where
  schemaExists schema = queryRaw' "SELECT 1 FROM pg_catalog.pg_namespace WHERE nspname=?" [toPrimitivePersistValue proxy schema] (fmap isJust)
  getCurrentSchema = queryRaw' "SELECT current_schema()" [] (fmap (>>= fst . fromPurePersistValues proxy))
  listTables schema = queryRaw' "SELECT table_name FROM information_schema.tables WHERE table_schema=coalesce(?,current_schema())" [toPrimitivePersistValue proxy schema] (mapAllRows $ return . fst . fromPurePersistValues proxy)
  listTableTriggers name = queryRaw' "SELECT trigger_name FROM information_schema.triggers WHERE event_object_schema=coalesce(?,current_schema()) AND event_object_table=?" (toPurePersistValues proxy name []) (mapAllRows $ return . fst . fromPurePersistValues proxy)
  getTableAnalysis = getTableAnalysis'
  analyzeTable = analyzeTable'
  analyzeTrigger name = do
    x <- queryRaw' "SELECT action_statement FROM information_schema.triggers WHERE trigger_schema=coalesce(?,current_schema()) AND trigger_name=?" (toPurePersistValues proxy name []) id
    return $ case x of
      Nothing  -> Nothing
      Just src -> fst $ fromPurePersistValues proxy src
  analyzeFunction name = do
    let query = "SELECT arg_types.typname, arg_types.typndims, arg_types_te.typname, ret.typname, ret.typndims, ret_te.typname, p.prosrc\
\     FROM pg_catalog.pg_namespace n\
\     INNER JOIN pg_catalog.pg_proc p ON p.pronamespace = n.oid\
\     LEFT JOIN (SELECT oid, unnest(coalesce(proallargtypes, proargtypes)) as arg FROM pg_catalog.pg_proc) as args ON p.oid = args.oid\
\     LEFT JOIN pg_type arg_types ON arg_types.oid = args.arg\
\     LEFT JOIN pg_type arg_types_te ON arg_types_te.oid = arg_types.typelem\
\     INNER JOIN pg_type ret ON p.prorettype = ret.oid\
\     LEFT JOIN pg_type ret_te ON ret_te.oid = ret.typelem\
\     WHERE n.nspname = coalesce(?,current_schema()) AND p.proname = ?"
    result <- queryRaw' query (toPurePersistValues proxy name []) (mapAllRows $ return . fst . fromPurePersistValues proxy)
    let read' (typ, arr) = readSqlType typ (Nothing, Nothing, Nothing, Nothing, Nothing) arr
    return $ case result of
      []  -> Nothing
      ((_, (ret, src)):_) -> Just $ (Just $ map read' args, Just $ read' ret, src) where
        args = mapMaybe (\(typ, arr) -> fmap (\typ' -> (typ', arr)) typ) $ map fst result
  getMigrationPack tableInfo = do
    fmap (migrationPack tableInfo . fromJust) getCurrentSchema

withPostgresqlPool :: (MonadBaseControl IO m, MonadIO m)
                   => String -- ^ connection string
                   -> Int -- ^ number of connections to open
                   -> (Pool Postgresql -> m a)
                   -> m a
withPostgresqlPool s connCount f = createPostgresqlPool s connCount >>= f

withPostgresqlConn :: (MonadBaseControl IO m, MonadIO m)
                   => String -- ^ connection string
                   -> (Postgresql -> m a)
                   -> m a
withPostgresqlConn s = bracket (liftIO $ open' s) (liftIO . close')

createPostgresqlPool :: MonadIO m
                     => String -- ^ connection string
                     -> Int -- ^ number of connections to open
                     -> m (Pool Postgresql)
createPostgresqlPool s connCount = liftIO $ createPool (open' s) close' 1 20 connCount

-- Not sure of the best way to handle Semigroup/Monoid changes in ghc 8.4
-- here. It appears that the long SQL query text interferes with the use
-- of CPP here.
--
-- Manually copying over https://github.com/lpsmith/postgresql-simple/commit/44c0bb8dec3b71e8daefe104cf643c0c4fb26768#diff-75d19972de474bc8fa181e4733f3f0d6R94
-- but this is not really a good idea.
--
combine :: PG.Query -> PG.Query -> PG.Query
-- combine = (<>)
combine (PG.Query a) (PG.Query b) = PG.Query (B.append a b)


instance Savepoint Postgresql where
  withConnSavepoint name m (Postgresql c) = do
    let name' = fromString name
    liftIO $ PG.execute_ c $ "SAVEPOINT " `combine` name'
    x <- onException m (liftIO $ PG.execute_ c $ "ROLLBACK TO SAVEPOINT " `combine` name')
    liftIO $ PG.execute_ c $ "RELEASE SAVEPOINT" `combine` name'
    return x

instance ConnectionManager Postgresql Postgresql where
  withConn f conn@(Postgresql c) = do
    liftIO $ PG.begin c
    x <- onException (f conn) (liftIO $ PG.rollback c)
    liftIO $ PG.commit c
    return x
  withConnNoTransaction f conn = f conn

instance ConnectionManager (Pool Postgresql) Postgresql where
  withConn f pconn = withResource pconn (withConn f)
  withConnNoTransaction f pconn = withResource pconn (withConnNoTransaction f)

instance SingleConnectionManager Postgresql Postgresql

open' :: String -> IO Postgresql
open' s = do
  conn <- PG.connectPostgreSQL $ pack s
  PG.execute_ conn $ getStatement "SET client_min_messages TO WARNING"
  return $ Postgresql conn

close' :: Postgresql -> IO ()
close' (Postgresql conn) = PG.close conn

insert' :: (PersistEntity v, MonadBaseControl IO m, MonadIO m, MonadLogger m) => v -> DbPersist Postgresql m (AutoKey v)
insert' v = do
  -- constructor number and the rest of the field values
  vals <- toEntityPersistValues' v
  let e = entityDef proxy v
  let constructorNum = fromPrimitivePersistValue proxy (head vals)

  liftM fst $ if isSimple (constructors e)
    then do
      let constr = head $ constructors e
      let RenderS query vals' = insertIntoConstructorTable True False (tableName escapeS e constr) constr (tail vals)
      case constrAutoKeyName constr of
        Nothing -> executeRaw' query (vals' []) >> pureFromPersistValue []
        Just _  -> do
          x <- queryRaw' query (vals' []) id
          case x of
            Just xs -> pureFromPersistValue xs
            Nothing -> pureFromPersistValue []
    else do
      let constr = constructors e !! constructorNum
      let query = "INSERT INTO " <> mainTableName escapeS e <> "(discr)VALUES(?)RETURNING(id)"
      rowid <- queryRaw' query (take 1 vals) getKey
      let RenderS cQuery vals' = insertIntoConstructorTable False True (tableName escapeS e constr) constr (rowid:tail vals)
      executeRaw' cQuery (vals' [])
      pureFromPersistValue [rowid]

insert_' :: (PersistEntity v, MonadBaseControl IO m, MonadIO m, MonadLogger m) => v -> DbPersist Postgresql m ()
insert_' v = do
  -- constructor number and the rest of the field values
  vals <- toEntityPersistValues' v
  let e = entityDef proxy v
  let constructorNum = fromPrimitivePersistValue proxy (head vals)

  if isSimple (constructors e)
    then do
      let constr = head $ constructors e
      let RenderS query vals' = insertIntoConstructorTable False False (tableName escapeS e constr) constr (tail vals)
      executeRaw' query (vals' [])
    else do
      let constr = constructors e !! constructorNum
      let query = "INSERT INTO " <> mainTableName escapeS e <> "(discr)VALUES(?)RETURNING(id)"
      rowid <- queryRaw' query (take 1 vals) getKey
      let RenderS cQuery vals' = insertIntoConstructorTable False True (tableName escapeS e constr) constr (rowid:tail vals)
      executeRaw' cQuery (vals' [])

insertIntoConstructorTable :: Bool -> Bool -> Utf8 -> ConstructorDef -> [PersistValue] -> RenderS db r
insertIntoConstructorTable withRet withId tName c vals = RenderS query vals' where
  query = "INSERT INTO " <> tName <> columnsValues <> returning
  (fields, returning) = case constrAutoKeyName c of
    Just idName -> (fields', returning') where
      fields' = if withId then (idName, dbType proxy (0 :: Int64)):constrParams c else constrParams c
      returning' = if withRet then " RETURNING(" <> escapeS (fromString idName) <> ")" else mempty
    _           -> (constrParams c, mempty)
  columnsValues = case foldr (flatten escapeS) [] fields of
    [] -> " DEFAULT VALUES"
    xs -> "(" <> commasJoin xs <> ") VALUES(" <> placeholders <> ")"
  RenderS placeholders vals' = commasJoin $ map renderPersistValue vals

insertList' :: forall m a.(MonadBaseControl IO m, MonadIO m, MonadLogger m, PersistField a) => [a] -> DbPersist Postgresql m Int64
insertList' (l :: [a]) = do
  let mainName = "List" <> delim' <> delim' <> fromString (persistName (undefined :: a))
  k <- queryRaw' ("INSERT INTO " <> escapeS mainName <> " DEFAULT VALUES RETURNING(id)") [] getKey
  let valuesName = mainName <> delim' <> "values"
  let fields = [("ord", dbType proxy (0 :: Int)), ("value", dbType proxy (undefined :: a))]
  let query = "INSERT INTO " <> escapeS valuesName <> "(id," <> renderFields escapeS fields <> ")VALUES(?," <> renderFields (const $ fromChar '?') fields <> ")"
  let go :: Int -> [a] -> DbPersist Postgresql m ()
      go n (x:xs) = do
       x' <- toPersistValues x
       executeRaw' query $ (k:) . (toPrimitivePersistValue proxy n:) . x' $ []
       go (n + 1) xs
      go _ [] = return ()
  go 0 l
  return $ fromPrimitivePersistValue proxy k

getList' :: forall m a.(MonadBaseControl IO m, MonadIO m, MonadLogger m, PersistField a) => Int64 -> DbPersist Postgresql m [a]
getList' k = do
  let mainName = "List" <> delim' <> delim' <> fromString (persistName (undefined :: a))
  let valuesName = mainName <> delim' <> "values"
  let value = ("value", dbType proxy (undefined :: a))
  let query = "SELECT " <> renderFields escapeS [value] <> " FROM " <> escapeS valuesName <> " WHERE id=? ORDER BY ord"
  queryRaw' query [toPrimitivePersistValue proxy k] $ mapAllRows (liftM fst . fromPersistValues)

--TODO: consider removal
{-# SPECIALIZE getKey :: RowPopper (DbPersist Postgresql IO) -> DbPersist Postgresql IO PersistValue #-}
getKey :: MonadIO m => RowPopper (DbPersist Postgresql m) -> DbPersist Postgresql m PersistValue
getKey pop = pop >>= \(Just [k]) -> return k

----------

executeRaw' :: (MonadIO m, MonadLogger m) => Utf8 -> [PersistValue] -> DbPersist Postgresql m ()
executeRaw' query vals = do
  $logDebugS "SQL" $ fromString $ show (fromUtf8 query) ++ " " ++ show vals
  Postgresql conn <- DbPersist ask
  let stmt = getStatement query
  liftIO $ do
    _ <- PG.execute conn stmt (map P vals)
    return ()

renderConfig :: RenderConfig
renderConfig = RenderConfig {
    esc = escapeS
}

escapeS :: Utf8 -> Utf8
escapeS a = let q = fromChar '"' in q <> a <> q

delim' :: Utf8
delim' = fromChar delim

toEntityPersistValues' :: (MonadBaseControl IO m, MonadIO m, PersistEntity v, MonadLogger m) => v -> DbPersist Postgresql m [PersistValue]
toEntityPersistValues' = liftM ($ []) . toEntityPersistValues

--- MIGRATION

migrate' :: (PersistEntity v, MonadBaseControl IO m, MonadIO m, MonadLogger m) => TableAnalysis (DbPersist Postgresql m) -> v -> Migration (DbPersist Postgresql m)
migrate' tableInfo v = do
  migPack <- lift $ getMigrationPack tableInfo
  migrateRecursively (migrateSchema migPack) (migrateEntity tableInfo migPack) (migrateList tableInfo migPack) v

migrationPack :: (MonadBaseControl IO m, MonadIO m, MonadLogger m)
              => TableAnalysis (DbPersist Postgresql m)
              -> String
              -> GM.MigrationPack (DbPersist Postgresql m)
migrationPack tableInfo currentSchema = GM.MigrationPack
  compareTypes
  (compareRefs currentSchema)
  compareUniqs
  compareDefaults
  migTriggerOnDelete
  migTriggerOnUpdate
  (GM.defaultMigConstr tableInfo)
  escape
  "BIGSERIAL PRIMARY KEY UNIQUE"
  mainTableId
  defaultPriority
  (\uniques refs -> ([], map AddUnique uniques ++ map AddReference refs))
  showSqlType
  showColumn
  showAlterDb
  NoAction
  NoAction

showColumn :: Column -> String
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

migTriggerOnDelete :: (MonadBaseControl IO m, MonadIO m, MonadLogger m) => QualifiedName -> [(String, String)] -> DbPersist Postgresql m (Bool, [AlterDB])
migTriggerOnDelete tName deletes = do
  let funcName = tName
      trigName = tName
  func <- analyzeFunction funcName
  trig <- analyzeTrigger trigName
  let funcBody = "BEGIN " ++ concatMap snd deletes ++ "RETURN NEW;END;"
      addFunction = CreateOrReplaceFunction $ "CREATE OR REPLACE FUNCTION " ++ withSchema funcName ++ "() RETURNS trigger AS $$" ++ funcBody ++ "$$ LANGUAGE plpgsql"
      funcMig = case func of
        Nothing | null deletes -> []
        Nothing   -> [addFunction]
        Just (_, Just (DbOther (OtherTypeDef [Left "trigger"])), body) -> if null deletes -- remove old trigger if a datatype earlier had fields of ephemeral types
          then [DropFunction funcName]
          else if body == funcBody
            then []
            -- this can happen when an ephemeral field was added or removed.
            else [DropFunction funcName, addFunction]
        _ -> [] -- ignore same name functions which don't return a trigger.

      trigBody = "EXECUTE PROCEDURE " ++ withSchema funcName ++ "()"
      addTrigger = AddTriggerOnDelete trigName tName trigBody
      (trigExisted, trigMig) = case trig of
        Nothing | null deletes -> (False, [])
        Nothing   -> (False, [addTrigger])
        Just body -> (True, if null deletes -- remove old trigger if a datatype earlier had fields of ephemeral types
          then [DropTrigger trigName tName]
          else if body == trigBody
            then []
            -- this can happen when an ephemeral field was added or removed.
            else [DropTrigger trigName tName, addTrigger])
  return (trigExisted, funcMig ++ trigMig)

-- | Table name and a list of field names and according delete statements
-- assume that this function is called only for ephemeral fields
migTriggerOnUpdate :: (MonadBaseControl IO m, MonadIO m, MonadLogger m) => QualifiedName -> [(String, String)] -> DbPersist Postgresql m [(Bool, [AlterDB])]
migTriggerOnUpdate tName dels = forM dels $ \(fieldName, del) -> do
  let funcName = second (\name -> name ++ delim : fieldName) tName
  let trigName = second (\name -> name ++ delim : fieldName) tName
  func <- analyzeFunction funcName
  trig <- analyzeTrigger trigName
  let funcBody = "BEGIN " ++ del ++ "RETURN NEW;END;"
      addFunction = CreateOrReplaceFunction $ "CREATE OR REPLACE FUNCTION " ++ withSchema funcName ++ "() RETURNS trigger AS $$" ++ funcBody ++ "$$ LANGUAGE plpgsql"
      funcMig = case func of
        Nothing   -> [addFunction]
        Just (_, Just (DbOther (OtherTypeDef [Left "trigger"])), body) -> if body == funcBody
            then []
            -- this can happen when an ephemeral field was added or removed.
            else [DropFunction funcName, addFunction]
        _ -> []

      trigBody = "EXECUTE PROCEDURE " ++ withSchema funcName ++ "()"
      addTrigger = AddTriggerOnUpdate trigName tName (Just fieldName) trigBody
      (trigExisted, trigMig) = case trig of
        Nothing   -> (False, [addTrigger])
        Just body -> (True, if body == trigBody
            then []
            -- this can happen when an ephemeral field was added or removed.
            else [DropTrigger trigName tName, addTrigger])
  return (trigExisted, funcMig ++ trigMig)

getTableAnalysis' :: (MonadBaseControl IO m, MonadIO m, MonadLogger m) => DbPersist Postgresql m PgTableAnalysis
getTableAnalysis' = do
  tables <- queryRaw' "SELECT table_schema, table_name FROM information_schema.tables" (toPurePersistValues proxy () []) (mapAllRows $ return . fst . fromPurePersistValues proxy)
  let constraintQuery = "SELECT nr.nspname, r.relname, c.contype, c.conname, a.attname from pg_class r LEFT JOIN pg_namespace nr ON nr.oid = r.relnamespace LEFT JOIN pg_attribute a ON a.attrelid = r.oid, pg_constraint c LEFT JOIN pg_namespace nc ON nc.oid = c.connamespace, pg_depend d WHERE d.classid = 'pg_constraint'::regclass::oid AND d.refobjid = r.oid AND d.objid = c.oid AND d.refobjsubid = a.attnum"
      colQuery = "SELECT c.table_schema, c.table_name, c.column_name, c.is_nullable, c.udt_name, c.column_default, c.character_maximum_length, c.numeric_precision, c.numeric_scale, c.datetime_precision, c.interval_type, a.attndims AS array_dims, te.typname AS array_elem\
               \  FROM pg_catalog.pg_attribute a\
               \  INNER JOIN pg_catalog.pg_class cl ON cl.oid = a.attrelid\
               \  INNER JOIN pg_catalog.pg_namespace n ON n.oid = cl.relnamespace\
               \  INNER JOIN information_schema.columns c ON c.column_name = a.attname AND c.table_name = cl.relname AND c.table_schema = n.nspname\
               \  INNER JOIN pg_catalog.pg_type t ON t.oid = a.atttypid\
               \  LEFT JOIN pg_catalog.pg_type te ON te.oid = t.typelem\
               \  ORDER BY c.ordinal_position"
  tableInfo <- queryRaw' constraintQuery (toPurePersistValues proxy () []) (mapAllRows $ return . fst . fromPurePersistValues proxy)
  columnInfo <- queryRaw' colQuery (toPurePersistValues proxy () []) (mapAllRows $ return . (\(n,t,c) -> (n,t,getColumn c)) . fst . fromPurePersistValues proxy)
  let indexQuery = "WITH indexes as (\
                   \SELECT sch.nspname, tc.relname as tablename, ic.oid, ic.relname,\
                   \    ta.attnum, ta.attname, pg_get_indexdef(i.indexrelid, ia.attnum, true) as expr\
                   \  FROM pg_catalog.pg_index i\
                   \  INNER JOIN pg_catalog.pg_class ic ON ic.oid = i.indexrelid\
                   \  INNER JOIN pg_catalog.pg_class tc ON i.indrelid = tc.oid\
                   \  INNER JOIN pg_catalog.pg_attribute ia ON ia.attrelid=ic.oid\
                   \  LEFT JOIN pg_catalog.pg_attribute ta ON ta.attrelid=tc.oid AND ta.attnum = i.indkey[ia.attnum-1] AND NOT ta.attisdropped\
                   \  INNER JOIN pg_namespace sch ON sch.oid = tc.relnamespace\
                   \  WHERE ic.oid NOT IN (SELECT conindid FROM pg_catalog.pg_constraint)\
                   \    AND NOT i.indisprimary\
                   \    AND i.indisunique\
                   \  ORDER BY ic.relname, ia.attnum)\
                   \SELECT i.nspname, i.tablename, i.relname, i.attname, i.expr\
                   \  FROM indexes i\
                   \  INNER JOIN (SELECT oid FROM indexes\
                   \    GROUP BY oid\
                   \    HAVING every(attnum > 0 OR attnum IS NULL)) non_system ON i.oid = non_system.oid"
  indexInfo <- queryRaw' indexQuery (toPurePersistValues proxy () []) (mapAllRows $ return . fst . fromPurePersistValues proxy)
  let referencesQuery = "SELECT sch_child.nspname, cl_child.relname, c.conname, sch_parent.nspname, cl_parent.relname, c. confdeltype, c.confupdtype, a_child.attname AS child, a_parent.attname AS parent FROM\
                     \  (SELECT r.conrelid, r.confrelid, unnest(r.conkey) AS conkey, unnest(r.confkey) AS confkey, r.conname, r.confupdtype, r.confdeltype\
                     \    FROM pg_catalog.pg_constraint r WHERE r.contype = 'f'\
                     \  ) AS c\
                     \  INNER JOIN pg_attribute a_parent ON a_parent.attnum = c.confkey AND a_parent.attrelid = c.confrelid\
                     \  INNER JOIN pg_class cl_parent ON cl_parent.oid = c.confrelid\
                     \  INNER JOIN pg_namespace sch_parent ON sch_parent.oid = cl_parent.relnamespace\
                     \  INNER JOIN pg_attribute a_child ON a_child.attnum = c.conkey AND a_child.attrelid = c.conrelid\
                     \  INNER JOIN pg_class cl_child ON cl_child.oid = c.conrelid\
                     \  INNER JOIN pg_namespace sch_child ON sch_child.oid = cl_child.relnamespace\
                     \  ORDER BY c.conname"
  referencesInfo <- queryRaw' referencesQuery (toPurePersistValues proxy () []) $ mapAllRows (return . fst . fromPurePersistValues proxy)
  return $ PgTableAnalysis
    { _pgTableAnalysis_tables = Set.fromList tables
    , _pgTableAnalysis_columns = Map.fromListWith (++) [((nspname, relname),[col]) | (nspname, relname, col) <- columnInfo]
    , _pgTableAnalysis_constraints = Map.fromListWith (Map.unionWith Set.union) $
        [((nspname,relname), Map.singleton contype (Set.singleton (conname, attname))) | (nspname, relname, contype, conname, attname) <- tableInfo]
    , _pgTableAnalysis_indices = Map.fromListWith Set.union [((nspname, relname), Set.singleton idx) | (nspname, relname, idx) <- indexInfo]
    , _pgTableAnalysis_references = Map.fromListWith Set.union [((nspname, relname), Set.singleton ref) | (nspname, relname, ref) <- referencesInfo]
    }

analyzeTable' :: (MonadBaseControl IO m, MonadIO m, MonadLogger m)
              => TableAnalysis (DbPersist Postgresql m)
              -> QualifiedName
              -> DbPersist Postgresql m (Maybe TableInfo)
analyzeTable' info rawName = do
  curSchemas <- queryRaw' "SELECT current_schema()" (toPurePersistValues proxy () []) (mapAllRows $ return . fst . fromPurePersistValues proxy)
  let curSchema = case curSchemas of
        [] -> error "Database.Groundhog.Postgresql.analyzeTable': \"SELECT current_schema()\" didn't return any rows."
        (x:_) -> x
      name = case rawName of
        (Nothing, nameTable) -> (Just curSchema, nameTable)
        (Just _, _) -> rawName
  case Set.member name (_pgTableAnalysis_tables info) of
    True -> do
      let mTableConstraintInfo = Map.lookup name (_pgTableAnalysis_constraints info)
          uniqConstraints = fromMaybe [] $ do
            tableInfo <- mTableConstraintInfo
            uniqs <- Map.lookup "u" tableInfo
            return (Set.toList uniqs)
          uniqPrimary = fromMaybe [] $ do
            tableInfo <- mTableConstraintInfo
            primary <- Map.lookup "p" tableInfo
            return (Set.toList primary)
      -- indexes with system columns like oid are omitted
          cols = Map.findWithDefault [] name (_pgTableAnalysis_columns info)
          uniqIndexes = fromMaybe [] $ do
            indexInfo <- Map.lookup name (_pgTableAnalysis_indices info)
            return (Set.toList indexInfo)
      let mkUniqs typ = map (\us -> UniqueDef (fst $ head us) typ (map snd us)) . groupBy ((==) `on` fst)
          isAutoincremented = case filter (\c -> colName c `elem` map snd uniqPrimary) cols of
                                [c] -> colType c `elem` [DbInt32, DbInt64] && maybe False ("nextval" `isPrefixOf`) (colDefault c)
                                _ -> False
      let uniqs = mkUniqs UniqueConstraint (map (second Left) uniqConstraints)
               ++ mkUniqs UniqueIndex (map (second $ \(col, expr) -> maybe (Right expr) Left col) uniqIndexes)
               ++ mkUniqs (UniquePrimary isAutoincremented) (map (second Left) uniqPrimary)
      references <- analyzeTableReferences info name
      return $ Just $ TableInfo cols uniqs references
    False -> return Nothing

getColumn :: ((String, String, String, Maybe String), (Maybe Int, Maybe Int, Maybe Int, Maybe Int, Maybe String), (Int, Maybe String)) -> Column
getColumn ((column_name, is_nullable, udt_name, d), modifiers, arr_info) = Column column_name (is_nullable == "YES") t d where
  t = readSqlType udt_name modifiers arr_info

analyzeTableReferences :: (MonadBaseControl IO m, MonadIO m, MonadLogger m) => PgTableAnalysis -> QualifiedName -> DbPersist Postgresql m [(Maybe String, Reference)]
analyzeTableReferences info tName = do
  let x = fromMaybe [] $ do
        refs <- Map.lookup tName (_pgTableAnalysis_references info)
        return (Set.toList refs)
  -- (refName, ((parentTableSchema, parentTable, onDelete, onUpdate), (childColumn, parentColumn)))
  let mkReference xs = (Just refName, Reference parentTable pairs (mkAction onDelete) (mkAction onUpdate)) where
        pairs = map (snd . snd) xs
        (refName, ((parentTable, onDelete, onUpdate), _)) = head xs
        mkAction c = Just $ case c of
          "a" -> NoAction
          "r" -> Restrict
          "c" -> Cascade
          "n" -> SetNull
          "d" -> SetDefault
          _ -> error $ "unknown reference action type: " ++ c
      references = map mkReference $ groupBy ((==) `on` fst) x
  return references

showAlterDb :: AlterDB -> SingleMigration
showAlterDb (AddTable s) = Right [(False, defaultPriority, s)]
showAlterDb (AlterTable t _ _ _ alts) = Right $ concatMap (showAlterTable $ withSchema t) alts
showAlterDb (DropTrigger trigName tName) = Right [(False, triggerPriority, "DROP TRIGGER " ++ withSchema trigName ++ " ON " ++ withSchema tName)]
showAlterDb (AddTriggerOnDelete trigName tName body) = Right [(False, triggerPriority, "CREATE TRIGGER " ++ withSchema trigName ++ " AFTER DELETE ON " ++ withSchema tName ++ " FOR EACH ROW " ++ body)]
showAlterDb (AddTriggerOnUpdate trigName tName fName body) = Right [(False, triggerPriority, "CREATE TRIGGER " ++ withSchema trigName ++ " AFTER UPDATE OF " ++ fName' ++ " ON " ++ withSchema tName ++ " FOR EACH ROW " ++ body)] where
    fName' = maybe (error $ "showAlterDb: AddTriggerOnUpdate does not have fieldName for trigger " ++ show trigName) escape fName
showAlterDb (CreateOrReplaceFunction s) = Right [(False, functionPriority, s)]
showAlterDb (DropFunction funcName) = Right [(False, functionPriority, "DROP FUNCTION " ++ withSchema funcName ++ "()")]
showAlterDb (CreateSchema sch ifNotExists) = Right [(False, schemaPriority, "CREATE SCHEMA " ++ ifNotExists' ++ escape sch)] where
  ifNotExists' = if ifNotExists then "IF NOT EXISTS " else ""

showAlterTable :: String -> AlterTable -> [(Bool, Int, String)]
showAlterTable table (AddColumn col) = [(False, defaultPriority, concat
  [ "ALTER TABLE "
  , table
  , " ADD COLUMN "
  , showColumn col
  ])]
showAlterTable table (DropColumn name) = [(True, defaultPriority, concat
  [ "ALTER TABLE "
  , table
  , " DROP COLUMN "
  , escape name
  ])]
showAlterTable table (AlterColumn col alts) = map (showAlterColumn table $ colName col) alts
showAlterTable table (AddUnique (UniqueDef uName UniqueConstraint cols)) = [(False, defaultPriority, concat
  [ "ALTER TABLE "
  , table
  , " ADD"
  , maybe "" ((" CONSTRAINT " ++) . escape) uName
  , " UNIQUE("
  , intercalate "," $ map (either escape id) cols
  , ")"
  ])]
showAlterTable table (AddUnique (UniqueDef uName UniqueIndex cols)) = [(False, defaultPriority, concat
  [ "CREATE UNIQUE INDEX "
  , maybe "" escape uName
  , " ON "
  , table
  , "("
  , intercalate "," $ map (either escape id) cols
  , ")"
  ])]
showAlterTable table (AddUnique (UniqueDef uName (UniquePrimary _) cols)) = [(False, defaultPriority, concat
  [ "ALTER TABLE "
  , table
  , " ADD"
  , maybe "" ((" CONSTRAINT " ++) . escape) uName
  , " PRIMARY KEY("
  , intercalate "," $ map (either escape id) cols
  , ")"
  ])]
showAlterTable table (DropConstraint uName) = [(False, defaultPriority, concat
  [ "ALTER TABLE "
  , table
  , " DROP CONSTRAINT "
  , escape uName
  ])]
showAlterTable _ (DropIndex uName) = [(False, defaultPriority, concat
  [ "DROP INDEX "
  , escape uName
  ])]
showAlterTable table (AddReference (Reference tName columns onDelete onUpdate)) = [(False, referencePriority, concat
  [ "ALTER TABLE "
  , table
  , " ADD FOREIGN KEY("
  , our
  , ") REFERENCES "
  , withSchema tName
  , "("
  , foreign
  , ")"
  , maybe "" ((" ON DELETE " ++) . showReferenceAction) onDelete
  , maybe "" ((" ON UPDATE " ++) . showReferenceAction) onUpdate
  ])] where
  (our, foreign) = f *** f $ unzip columns
  f = intercalate ", " . map escape
showAlterTable table (DropReference name) = [(False, defaultPriority,
    "ALTER TABLE " ++ table ++ " DROP CONSTRAINT " ++ escape name)]

showAlterColumn :: String -> String -> AlterColumn -> (Bool, Int, String)
showAlterColumn table n (Type t) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , table
  , " ALTER COLUMN "
  , escape n
  , " TYPE "
  , showSqlType t
  ])
showAlterColumn table n IsNull = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , table
  , " ALTER COLUMN "
  , escape n
  , " DROP NOT NULL"
  ])
showAlterColumn table n NotNull = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , table
  , " ALTER COLUMN "
  , escape n
  , " SET NOT NULL"
  ])

showAlterColumn table n (Default s) = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , table
  , " ALTER COLUMN "
  , escape n
  , " SET DEFAULT "
  , s
  ])
showAlterColumn table n NoDefault = (False, defaultPriority, concat
  [ "ALTER TABLE "
  , table
  , " ALTER COLUMN "
  , escape n
  , " DROP DEFAULT"
  ])
showAlterColumn table n (UpdateValue s) = (False, defaultPriority, concat
  [ "UPDATE "
  , table
  , " SET "
  , escape n
  , "="
  , s
  , " WHERE "
  , escape n
  , " IS NULL"
  ])

-- | udt_name, character_maximum_length, numeric_precision, numeric_scale, datetime_precision, interval_type
readSqlType :: String -> (Maybe Int, Maybe Int, Maybe Int, Maybe Int, Maybe String) -> (Int, Maybe String) -> DbTypePrimitive
readSqlType typ (character_maximum_length, numeric_precision, numeric_scale, datetime_precision, _) (array_ndims, array_elem) = (case typ of
  "int4" -> DbInt32
  "int8" -> DbInt64
  "varchar" -> maybe DbString (dbOther . ("varchar"++) . wrap . show) character_maximum_length
  "numeric" -> dbOther $ "numeric" ++ maybe "" wrap attrs where
    attrs = liftM2 (\a b -> if b == 0 then show a else show a ++ ", " ++ show b) numeric_precision numeric_scale
  "date" -> DbDay
  "bool" -> DbBool
  "time" -> mkDate DbTime "time"
  "timestamp" -> mkDate DbDayTime "timestamp"
  "timestamptz" -> mkDate DbDayTimeZoned "timestamptz"
  "float4" -> DbReal
  "float8" -> DbReal
  "bytea" -> DbBlob
  _ | array_ndims > 0 -> dbOther $ arr ++ concat (replicate array_ndims "[]") where
    arr = fromMaybe (error "readSqlType: array with elem type Nothing") array_elem
  a -> dbOther a) where
    dbOther t = DbOther $ OtherTypeDef [Left t]
    wrap x = "(" ++ x ++ ")"
    mkDate t name = maybe t (dbOther . (name++) . wrap . show) datetime_precision'
    defDateTimePrec = 6
    datetime_precision' = datetime_precision >>= \p -> if p == defDateTimePrec then Nothing else Just p

showSqlType :: DbTypePrimitive -> String
showSqlType t = case t of
  DbString -> "VARCHAR"
  DbInt32 -> "INT4"
  DbInt64 -> "INT8"
  DbReal -> "DOUBLE PRECISION"
  DbBool -> "BOOLEAN"
  DbDay -> "DATE"
  DbTime -> "TIME"
  DbDayTime -> "TIMESTAMP"
  DbDayTimeZoned -> "TIMESTAMP WITH TIME ZONE"
  DbBlob -> "BYTEA"
  DbOther (OtherTypeDef ts) -> concatMap (either id showSqlType) ts

compareUniqs :: UniqueDefInfo -> UniqueDefInfo -> Bool
compareUniqs (UniqueDef _ (UniquePrimary _) cols1) (UniqueDef _ (UniquePrimary _) cols2) = haveSameElems (GM.colIsEquivalent escape) cols1 cols2
compareUniqs (UniqueDef name1 type1 cols1) (UniqueDef name2 type2 cols2) = fromMaybe True (liftM2 (==) name1 name2) && type1 == type2 && haveSameElems (GM.colIsEquivalent escape) cols1 cols2

compareRefs :: String -> (Maybe String, Reference) -> (Maybe String, Reference) -> Bool
compareRefs currentSchema (_, Reference (sch1, tbl1) pairs1 onDel1 onUpd1) (_, Reference (sch2, tbl2) pairs2 onDel2 onUpd2) =
     fromMaybe currentSchema sch1 == fromMaybe currentSchema sch2
  && unescape tbl1 == unescape tbl2
  && haveSameElems (==) pairs1 pairs2
  && fromMaybe NoAction onDel1 == fromMaybe NoAction onDel2
  && fromMaybe NoAction onUpd1 == fromMaybe NoAction onUpd2 where
    unescape name = if head name == '"' && last name == '"' then tail $ init name else name

compareTypes :: DbTypePrimitive -> DbTypePrimitive -> Bool
compareTypes type1 type2 = f type1 == f type2 where
  f = map toUpper . showSqlType

compareDefaults :: String -> String -> Bool
compareDefaults def1 def2 = Just def2 `elem` [Just def1, stripType def1, stripType def1 >>= stripParens] where
  stripType = fmap reverse . stripPrefix "::" . dropWhile (\c -> isAlphaNum c || isSpace c) . reverse
  stripParens = stripPrefix "(" >=> fmap reverse . stripPrefix ")" . reverse

defaultPriority, schemaPriority, referencePriority, functionPriority, triggerPriority :: Int
defaultPriority = 1
schemaPriority = 0
referencePriority = 2
functionPriority = 3
triggerPriority = 4

mainTableId :: String
mainTableId = "id"

--- MAIN

-- It is used to escape table names and columns, which can include only symbols allowed in Haskell datatypes and '$' delimiter. We need it mostly to support names that coincide with SQL keywords
escape :: String -> String
escape s = '\"' : s ++ "\""

getStatement :: Utf8 -> PG.Query
getStatement sql = PG.Query $ fromUtf8 sql

queryRaw' :: (MonadBaseControl IO m, MonadIO m, MonadLogger m) => Utf8 -> [PersistValue] -> (RowPopper (DbPersist Postgresql m) -> DbPersist Postgresql m a) -> DbPersist Postgresql m a
queryRaw' query vals f = do
  $logDebugS "SQL" $ fromString $ show (fromUtf8 query) ++ " " ++ show vals
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
            merr <- LibPQ.errorMessage rawconn
            fail $ "Postgresql.withStmt': bad result status " ++
                   show status ++ " (" ++ show msg ++ ")" ++
                   maybe "" ((". Error message: " ++) . unpack) merr

        -- Get number and type of columns
        cols <- LibPQ.nfields ret
        getters <- forM [0..cols-1] $ \col -> do
          oid <- LibPQ.ftype ret col
          return $ getGetter oid $ PG.Field ret col oid
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
          Just bs -> do
            ok <- PGFF.runConversion (getter mbs) conn
            bs `seq` case ok of
              Errors (exc:_) -> throw exc
              Errors [] -> error "Got an Errors, but no exceptions"
              Ok v  -> return v

-- | Avoid orphan instances.
newtype P = P PersistValue

instance PGTF.ToField P where
  toField (P (PersistString t))         = PGTF.toField t
  toField (P (PersistByteString bs))    = PGTF.toField (PG.Binary bs)
  toField (P (PersistInt64 i))          = PGTF.toField i
  toField (P (PersistDouble d))         = PGTF.toField d
  toField (P (PersistBool b))           = PGTF.toField b
  toField (P (PersistDay d))            = PGTF.toField d
  toField (P (PersistTimeOfDay t))      = PGTF.toField t
  toField (P (PersistUTCTime t))        = PGTF.toField t
  toField (P (PersistZonedTime (ZT t))) = PGTF.toField t
  toField (P PersistNull)               = PGTF.toField PG.Null
  toField (P (PersistCustom _ _))       = error "toField: unexpected PersistCustom"

type Getter a = PGFF.FieldParser a

convertPV :: PGFF.FromField a => (a -> b) -> Getter b
convertPV f = (fmap f .) . PGFF.fromField

getGetter :: PG.Oid -> Getter PersistValue
getGetter (PG.Oid oid) = case oid of
  16   -> convertPV PersistBool
  17   -> convertPV (PersistByteString . unBinary)
  18   -> convertPV PersistString
  19   -> convertPV PersistString
  20   -> convertPV PersistInt64
  21   -> convertPV PersistInt64
  23   -> convertPV PersistInt64
  25   -> convertPV PersistString
  142  -> convertPV PersistString
  700  -> convertPV PersistDouble
  701  -> convertPV PersistDouble
  702  -> convertPV PersistUTCTime
  703  -> convertPV PersistUTCTime
  1042 -> convertPV PersistString
  1043 -> convertPV PersistString
  1082 -> convertPV PersistDay
  1083 -> convertPV PersistTimeOfDay
  1114 -> convertPV (PersistUTCTime . localTimeToUTC utc)
  1184 -> convertPV (PersistZonedTime . ZT)
  1560 -> convertPV PersistInt64
  1562 -> convertPV PersistInt64
  1700 -> convertPV (PersistDouble . fromRational)
  2278 -> \_ _ -> return PersistNull
  _    -> \f dat -> fmap PersistByteString $ case dat of
    Nothing -> PGFF.returnError PGFF.UnexpectedNull f ""
    Just str -> return $ copy $ str

unBinary :: PG.Binary a -> a
unBinary (PG.Binary x) = x

proxy :: proxy Postgresql
proxy = error "proxy Postgresql"

withSchema :: QualifiedName -> String
withSchema (sch, name) = maybe "" (\x -> escape x ++ ".") sch ++ escape name

-- | Put explicit type for expression. It is useful for values which are defaulted to a wrong type.
-- For example, a literal Int from a 64bit machine can be defaulted to a 32bit int by Postgresql.
-- Also a value entered as an external string (geometry, arrays and other complex types have this representation) may need an explicit type.
explicitType :: (Expression Postgresql r a, PersistField a) => a -> Expr Postgresql r a
explicitType a = castType a t where
  t = case dbType proxy a of
    DbTypePrimitive t' _ _ _ -> showSqlType t'
    _ -> error "explicitType: type is not primitive"

-- | Casts expression to a type. @castType value \"INT\"@ results in @value::INT@.
castType :: Expression Postgresql r a => a -> String -> Expr Postgresql r a
castType a t = mkExpr $ Snippet $ \conf _ -> ["(" <> renderExpr conf (toExpr a) <> ")::" <> fromString t] where

-- | Distinct only on certain fields or expressions. For example, @select $ CondEmpty `distinctOn` (lower EmailField, IpField)@.
distinctOn :: (db ~ Postgresql, HasSelectOptions a db r, HasDistinct a ~ HFalse, Projection' p db r p') => a -> p -> SelectOptions db r (HasLimit a) (HasOffset a) (HasOrder a) HTrue
distinctOn opts p = opts' {dbSpecificOptions = ("DISTINCT_ON", clause): dbSpecificOptions opts'} where
  opts' = getSelectOptions opts
  clause = Snippet $ \conf _ -> [commasJoin $ concatMap (renderExprExtended conf 0) $ projectionExprs p []]

preColumns :: HasSelectOptions opts Postgresql r => opts -> RenderS Postgresql r
preColumns opts = clause where
  clause = apply "DISTINCT_ON" (\t -> "DISTINCT ON (" <> t <> ")")
  apply k f = case lookup k opts' of
    Nothing -> mempty
    Just (Snippet snippet) -> f $ head $ snippet renderConfig 0
  opts' = dbSpecificOptions $ getSelectOptions opts


instance PersistField Scientific where
  persistName _ = "Scientific"
  toPersistValues = primToPersistValue
  fromPersistValues = primFromPersistValue
  dbType _ _ = DbTypePrimitive
    (DbOther (OtherTypeDef [Left "numeric"]))
    True
    Nothing
    Nothing

instance PrimitivePersistField Scientific where
  toPrimitivePersistValue  _ n = PersistCustom (Utf8 $ fromString $ show n <> "::numeric") []
  fromPrimitivePersistValue _ (PersistCustom pv _) = fromMaybe
    (error $ "fromPrimitivePersistValue: Could not parse Scientific: " ++ show pv)
    $ either (const Nothing) (readMaybe . T.unpack) $ T.decodeUtf8' $ fromUtf8 pv
  fromPrimitivePersistValue _ (PersistInt64 v) = fromIntegral v
  fromPrimitivePersistValue _ (PersistDouble v) = fromFloatDigits v
  fromPrimitivePersistValue _ pv = error $ "fromPrimitivePersistValue: Unexpected PersistValue when trying to parse Scientific: " ++ show pv

instance NeverNull Scientific
