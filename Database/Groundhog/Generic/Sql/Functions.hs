{-# LANGUAGE FlexibleContexts, TypeFamilies, OverloadedStrings #-}

-- | This module has common SQL functions and operators which are supported in the most SQL databases
module Database.Groundhog.Generic.Sql.Functions
    ( like
    , in_
    , notIn_
    , lower
    , upper
    , append
    , toArith
    ) where

import Database.Groundhog.Core
import Database.Groundhog.Expression
import Database.Groundhog.Generic.Sql

in_ :: (SqlDb db, QueryRaw db ~ Snippet db, Expression db r a, Expression db r b, PrimitivePersistField b, Unifiable a b) =>
    a -> [b] -> Cond db r
in_ a bs = CondRaw $ Snippet $ \esc p -> [parens 45 p $ renderExpr esc (toExpr a) <> " IN (" <> commasJoin (map (renderExpr esc . toExpr) bs) <> ")"]

notIn_ :: (SqlDb db, QueryRaw db ~ Snippet db, Expression db r a, Expression db r b, PrimitivePersistField b, Unifiable a b) =>
       a -> [b] -> Cond db r
notIn_ a bs = CondRaw $ Snippet $ \esc p -> [parens 45 p $ renderExpr esc (toExpr a) <> " NOT IN (" <> commasJoin (map (renderExpr esc . toExpr) bs) <> ")"]

like :: (SqlDb db, QueryRaw db ~ Snippet db, ExpressionOf db r a String) => a -> String -> Cond db r
like a b = CondRaw $ operator 40 " LIKE " a b

lower :: (SqlDb db, QueryRaw db ~ Snippet db, ExpressionOf db r a String) => a -> Expr db r String
lower a = Expr $ function "lower" [toExpr a]

upper :: (SqlDb db, QueryRaw db ~ Snippet db, ExpressionOf db r a String) => a -> Expr db r String
upper a = Expr $ function "upper" [toExpr a]

append :: (SqlDb db, QueryRaw db ~ Snippet db, ExpressionOf db r a String, ExpressionOf db r b String) => a -> b -> Expr db r String
append a b = Expr $ operator 50 "||" a b

-- | Convert field to an arithmetic value. It is kept for compatibility with older Groundhog versions and can be replaced with liftExpr.
toArith :: (SqlDb db, QueryRaw db ~ Snippet db, ExpressionOf db r f a', FieldLike f db r a') => f -> Expr db r a'
toArith = liftExpr
