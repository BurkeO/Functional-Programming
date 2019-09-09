{- burkeow Owen Burke -}
module Ex02 where
  import Data.Maybe
  
  -- Datatypes -------------------------------------------------------------------
  
  -- do not change anything in this section !
  
  
  -- a binary tree datatype
  data Tree k d
    = Br (Tree k d) (Tree k d) k d
    | Leaf k d
    | Nil
    deriving (Eq, Show)
  
  type IntFun = Tree Int Int -- binary tree with integer keys and data
  
  data Expr
    = Val Double
    | Var String
    | Add Expr Expr
    | Mul Expr Expr    
    | Sub Expr Expr
    | Abs Expr
    | Sign Expr
     deriving (Eq, Show)
  
  
  
  -- Part 1 : Tree Insert -------------------------------
  
  -- Implement:
  ins :: Ord k => k -> d -> Tree k d -> Tree k d
  
  ins key value Nil = Leaf key value
  
  ins key value (Leaf k d)
    | key < k   =  Br (Leaf key value) Nil k d
    | key > k   =  Br Nil (Leaf key value) k d
    | key == k  =  Leaf k value
  
  ins key value (Br left right k d)
    | key < k   =  Br (ins key value left) right k d
    | key > k   =  Br left (ins key value right) k d
    | key == k  =  Br left right k value
  
  
  
  -- Part 2 : Tree Lookup -------------------------------
  
  
  -- Implement:
  lkp :: (Monad m, Ord k) => Tree k d -> k -> m d
  
  lkp Nil k = fail "failure"
  
  lkp (Leaf key value) k
    | key == k = return value
    | otherwise = fail "failure"
   
  lkp (Br left right key value) k
    | key > k   =  lkp left k
    | key < k   =  lkp right k
    | key == k  =  return value
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  -- Part 3 : Instance of Num for Expr
  
  {-
    Fix the following instance for Num of Expr so all tests pass
    Note that the tests expect simplification to be done
    only when *all* Expr arguments are of the form Val v
    Hint 1 :  implementing fromInteger *first* is recommended!
    Hint 2 :  remember that Double is already an instance of Num
  -}
  
  --------------------------------------------------------------------
  
  eval :: Expr -> Maybe Double
  
  eval (Val x) = Just x
  
  eval (Add x y) = Just (fromJust(eval x) + fromJust(eval y))
  
  eval (Sub x y) = Just (fromJust(eval x) - fromJust(eval y))
  
  eval (Mul x y) = Just (fromJust(eval x) * fromJust(eval y))
  
  
  
  -------------------------------------------------------------------
  
  simp :: Expr -> Expr
  simp (Var v)        =  Var v
  simp (Add e1 e2)    =  simpAdd (simp e1) (simp e2)
  simp (Sub e1 e2)    =  simpSub (simp e1) (simp e2)
  simp (Mul e1 e2)    =  simpMul (simp e1) (simp e2)
  simp e = e  --for most simple one (Val _)
  
  --------------------------------------------------------------------
  
  simpAdd :: Expr -> Expr -> Expr
  
  simpAdd (Var x) (Var y) = Add (Var x) (Var y)
  simpAdd e1 (Var y) = Add (Val(fromJust(eval e1))) (Var y)
  simpAdd (Var x) e2 = Add (Var x) (Val(fromJust(eval e2)))
  simpAdd e1 e2 = Val (fromJust(eval (Add e1 e2)))
  
  simpSub :: Expr -> Expr -> Expr
  
  simpSub (Var x) (Var y) = Sub (Var x) (Var y)
  simpSub e1 (Var y) = Sub (Val(fromJust(eval e1))) (Var y)
  simpSub (Var x) e2 = Sub (Var x) (Val(fromJust(eval e2)))
  simpSub e1 e2 = Val (fromJust(eval (Sub e1 e2)))
  
  simpMul :: Expr -> Expr -> Expr
  
  simpMul (Var x) (Var y) = Mul (Var x) (Var y)
  simpMul e1 (Var y) = Mul (Val(fromJust(eval e1))) (Var y)
  simpMul (Var x) e2 = Mul (Var x) (Val(fromJust(eval e2)))
  simpMul e1 e2 = Val (fromJust(eval (Mul e1 e2)))
  
  -------------------------------------------------------------------
  
  addExpr e1 e2 = simp (Add e1 e2)
  
  subExpr e1 e2 = simp (Sub e1 e2)
  
  mulExpr e1 e2 = simp (Mul e1 e2)
  
  negExpr e = let e1 = simp e
              in case (e1) of
                  (Val x) ->  Val(-x)
                  (Var v) ->  (Sub (Val 0) (Var v))
  
  
  absExpr e = let e1 = simp e
              in case (e1) of
                  (Val x) ->  Val(abs(x))
                  (Var v) ->  Abs (Var v)
  
  
  signumExpr e = let e1 = simp e
             in case (e1) of
                (Val x) ->  if x == 0 then Val 0
                            else if x < 0 then Val (-1)
                            else Val 1
                (Var v) ->  Sign (Var v)
  
  
  integerToExpr i = Val (fromIntegral i)
  
  -------------------------------------------------------------------------
  
  instance Num Expr where
    e1 + e2 = addExpr e1 e2
    e1 - e2 = subExpr e1 e2
    e1 * e2 = mulExpr e1 e2
    negate e = negExpr e
    abs e = absExpr e
    signum e = signumExpr e
    fromInteger i = integerToExpr i