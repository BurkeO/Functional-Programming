{- burkeow Owen Burke -}
module Ex01 where
import Data.List ((\\))
import Data.Maybe

-- Datatypes -------------------------------------------------------------------

-- do not change anything in this section !

type Id = String

data Expr
  = Val Double
  | Add Expr Expr
  | Mul Expr Expr
  | Sub Expr Expr
  | Dvd Expr Expr
  | Var Id
  | Def Id Expr Expr
  deriving (Eq, Show)

type Dict k d  =  [(k,d)]

define :: Dict k d -> k -> d -> Dict k d
define d s v = (s,v):d

find :: Eq k => Dict k d -> k -> Maybe d
find []             _                 =  Nothing
find ( (s,v) : ds ) name | name == s  =  Just v
                         | otherwise  =  find ds name

type EDict = Dict String Double






-- Part 1 : Evaluating Expressions -- (63 marks) -------------------------------

-- Implement the following function so all 'eval' tests pass.

-- eval should return Nothing if:
  -- (1) a divide by zero operation was going to be performed;
  -- (2) the expression contains a variable not in the dictionary.

eval :: EDict -> Expr -> Maybe Double

eval _ (Val x) = Just x
eval a (Var x) = find a x

eval a (Dvd x y) | (eval a y) == Just 0.0 = Nothing 
                 | (eval a x) == Nothing = Nothing
                 | (eval a y) == Nothing = Nothing
                 | otherwise = Just(fromJust(eval a x) / fromJust(eval a y)) 

eval a (Sub x y) | (eval a x) == Nothing = Nothing
                 | (eval a y) == Nothing = Nothing
                 | otherwise = Just(fromJust(eval a x) - fromJust(eval a y))
                 
eval a (Mul x y) | (eval a x) == Nothing = Nothing
                 | (eval a y) == Nothing = Nothing
                 | otherwise = Just(fromJust(eval a x) * fromJust(eval a y))


eval a (Add x y) | (eval a x) == Nothing = Nothing
                 | (eval a y) == Nothing = Nothing
                 | otherwise = Just(fromJust(eval a x) + fromJust(eval a y))
                 
eval a (Def id x y) | (eval a x) == Nothing = Nothing
                    | (eval (define a id (fromJust(eval a x))) y) == Nothing = Nothing
                    | otherwise = Just(fromJust(eval (define a id (fromJust(eval a x))) y))



-- Part 2 : Simplifying Expressions -- (57 marks) ------------------------------

-- Given the following code :

simp :: EDict -> Expr -> Expr
simp d (Var v)        =  simpVar d v
simp d (Add e1 e2)    =  simpAdd d   (simp d e1) (simp d e2)
simp d (Sub e1 e2)    =  simpSub d   (simp d e1) (simp d e2)
simp d (Mul e1 e2)    =  simpMul d   (simp d e1) (simp d e2)
simp d (Dvd e1 e2)    =  simpDvd d   (simp d e1) (simp d e2)
simp d (Def v e1 e2)  =  simpDef d v (simp d e1) (simp d e2)
simp _ e = e  -- simplest case, Val, needs no special treatment

-- Implement the following functions so all 'simp' tests pass.

  -- (1) see test scripts for most required properties
  -- (2) (Def v e1 e2) should simplify to just e2 in the following two cases:
    -- (2a) if there is mention of v in e2
    -- (2b) if any mention of v in e2 is inside another (Def v .. ..)

simpVar :: EDict -> Id -> Expr

simpVar [] v = (Var v) 
simpVar d v  |(eval d (Var v)) == Nothing = (Var v)
             |otherwise = (Val (fromJust(eval d (Var v))))




simpAdd :: EDict -> Expr -> Expr -> Expr

simpAdd d e1 e2 = let e1P = simp d e1
                      e2P = simp d e2
                  in case (e1P,e2P) of
                      (Val 0.0,e)  ->  e
                      (e,Val 0.0)  ->  e
                      _            ->  if ((eval d e1 == Nothing) && (eval d e2 /= Nothing))
                                          then Add e1 (Val (fromJust(eval d e2)))
                                       else if ((eval d e1 /= Nothing) && (eval d e2 == Nothing))
                                          then Add (Val (fromJust(eval d e1))) e2
                                       else if ((eval d e1 /= Nothing) && (eval d e2 /= Nothing))
                                          then Val ((fromJust(eval d e1)) + (fromJust(eval d e2)))
                                       else Add e1 e2





simpSub :: EDict -> Expr -> Expr -> Expr
simpSub d e1 e2 = let e1P = simp d e1
                      e2P = simp d e2
                  in case (e1P,e2P) of
                      (e,Val 0.0)  ->  e
                      _            ->  if ((eval d e1 == Nothing) && (eval d e2 /= Nothing))
                                          then Sub e1 (Val (fromJust(eval d e2)))
                                       else if ((eval d e1 /= Nothing) && (eval d e2 == Nothing))
                                          then Sub (Val (fromJust(eval d e1))) e2
                                       else if ((eval d e1 /= Nothing) && (eval d e2 /= Nothing))
                                          then Val ((fromJust(eval d e1)) - (fromJust(eval d e2)))
                                       else Sub e1 e2






simpMul :: EDict -> Expr -> Expr -> Expr
simpMul d e1 e2 = let e1P = simp d e1
                      e2P = simp d e2
                  in case (e1P,e2P) of
                      (Val 0.0,e)  ->  Val(0.0)
                      (e,Val 0.0)  ->  Val(0.0)
                      (Val 1.0,e)  ->  e
                      (e,Val 1.0)  ->  e
                      _            ->  if ((eval d e1 == Nothing) && (eval d e2 /= Nothing))
                                          then Mul e1 (Val (fromJust(eval d e2)))
                                       else if ((eval d e1 /= Nothing) && (eval d e2 == Nothing))
                                          then Mul (Val (fromJust(eval d e1))) e2
                                       else if ((eval d e1 /= Nothing) && (eval d e2 /= Nothing))
                                          then Val ((fromJust(eval d e1)) * (fromJust(eval d e2)))
                                       else Mul e1 e2







simpDvd :: EDict -> Expr -> Expr -> Expr
simpDvd d e1 e2 = let e1P = simp d e1
                      e2P = simp d e2
                  in case (e1P,e2P) of
                      (Val 0.0,e)  ->  Val(0.0)
                      (e, Val 1.0) ->  e
                      (e,Val 0.0)  ->  Dvd e1P e2P
                      _            ->  if ((eval d e1 == Nothing) && (eval d e2 /= Nothing))
                                          then Dvd e1 (Val (fromJust(eval d e2)))
                                       else if ((eval d e1 /= Nothing) && (eval d e2 == Nothing))
                                          then Dvd (Val (fromJust(eval d e1))) e2
                                       else if ((eval d e1 /= Nothing) && (eval d e2 /= Nothing))
                                          then Val ((fromJust(eval d e1)) / (fromJust(eval d e2)))
                                       else Dvd e1 e2



simpDef :: EDict -> Id -> Expr -> Expr -> Expr
simpDef d v e1 e2
  = case (eval d e1) of
    Just e1' -> if (eval (define d v e1') e2) == Nothing then simp (define d v e1') e2
               else Val (fromJust (eval (define d v e1') e2))
















