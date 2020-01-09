module Calculus where

import Data.Maybe

data UnOp = Neg | Sin | Cos | Log
          deriving (Eq, Ord, Show)

data BinOp = Add | Mul | Div
           deriving (Eq, Ord, Show)

data Exp = Val Double | Id String | UnApp UnOp Exp | BinApp BinOp Exp Exp
         deriving (Eq, Ord, Show)

type Env = [(String, Double)]

---------------------------------------------------------------------------
-- Type classes and class instances

class Vars a where
  x, y, z :: a

instance Vars Exp where
  x = Id "x"
  y = Id "y"
  z = Id "z"

instance Vars Double where
  x = 4.3
  y = 9.2
  z = -1.7

-- Extension task in overloading Haskell's existing functions
--    to reduce redundancy
-- I also included two cases for multiplication by zero which are not given
--    in the specification.
instance Num Exp where
  fromInteger     = (Val . fromInteger)
  negate (Val 0)  = Val 0
  negate ex       = UnApp Neg ex
  (+) ex (Val 0)  = ex
  (+) (Val 0) ex  = ex
  (+) ex1 ex2     = BinApp Add ex1 ex2
  (*) (Val 1) ex  = ex
  (*) ex (Val 1)  = ex
  (*) ex (Val 0)  = Val 0
  (*) (Val 0) ex  = Val 0
  (*) ex1 ex2     = BinApp Mul ex1 ex2
-- Leave the following two undefined...
  signum      = undefined
  abs         = undefined

-- Extension task in overloading Haskell's existing functions and using rules
--    to reduce redundancy
instance Fractional Exp where
  fromRational  = Val . fromRational
  (/) 0 ex1     = Val 0
  (/) ex1 1     = ex1
  (/) ex1 ex2  = BinApp Div ex1 ex2
-- Leave the following one undefined...
  recip        = undefined

instance Floating Exp where
  sin     = UnApp Sin
  cos     = UnApp Cos
  log     = UnApp Log
-- Leave the following fifteen undefined...
  tan     = undefined
  asin    = undefined
  acos    = undefined
  atan    = undefined
  pi      = undefined
  exp     = undefined
  sqrt    = undefined
  (**)    = undefined
  logBase = undefined
  sinh    = undefined
  cosh    = undefined
  tanh    = undefined
  asinh   = undefined
  acosh   = undefined
  atanh   = undefined

---------------------------------------------------------------------------

-- This function uses the in-built lookup function and extracts the value from
--    the Maybe that is returned. It uses the pre-condition to avoid an error.
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: There is a binding for the key in the list.
lookUp value pairs
  = fromJust (lookup value pairs)

showExp :: Exp -> String
showExp 
  = undefined

unaryOps = [(Neg, ((-1.0) * )), (Sin, sin), (Cos, cos), (Log, log)]
binaryOps = [(Add, (+)), (Mul, (*)), (Div, (/))]

-- This function pattern matches the different possibilites for the Exp type
-- Uses a lookUp on the two lists I have created above, unaryOps and binaryOps, 
--    which map the operators in the expression to evaluatable Haskell functions
eval :: Exp -> Env -> Double
eval (Val x) env
  = x
eval (Id x) env
  = lookUp x env
eval (UnApp uop exp) env
  = (lookUp uop unaryOps) (eval exp env)
eval (BinApp bop exp1 exp2) env
  = (lookUp bop binaryOps) (eval exp1 env) (eval exp2 env)

-- This is the initial diff function which doesn't make use of optimisations
--    or overloading of Haskell's in-built functions
-- It pattern matches on the possible situations for differentiation and
--    recursively solves each part (such as in the product rule)
diff :: Exp -> String -> Exp
-- Pre: The input expression is to be differentiated in terms of "x"
diff (Val _) _
  = Val 0
diff (Id ex) var
  | ex == var  = Val 1
  | otherwise  = Val 0
diff (UnApp Sin x) var
  = BinApp Mul (UnApp Cos x) (diff x var)
diff (UnApp Cos x) var
  = UnApp Neg (BinApp Mul (UnApp Sin x) (diff x var))
diff (UnApp Neg x) var
  = UnApp Neg (diff x var)
diff (UnApp Log x) var
  = BinApp Div (diff x var) x
diff (BinApp Add ex1 ex2) var
  = BinApp Add (diff ex1 var) (diff ex2 var)
diff (BinApp Mul ex1 ex2) var
  = BinApp Add (BinApp Mul ex1 (diff ex2 var)) (BinApp Mul (diff ex1 var) ex2)
diff (BinApp Div ex1 ex2) var
  = BinApp Div (BinApp Add (BinApp Mul (diff ex1 var) ex2) 
      (UnApp Neg (BinApp Mul ex1 (diff ex2 var)))) (BinApp Mul ex2 ex2)

-- Extension function that makes use of overloading Haskell's existing functions
--    and reducing redundancy with rules in the Num and Fractional instances
-- The use of case reduces the need for excessive pattern matching in
--    function definitions (I researched this online)
diffEff :: Exp -> String -> Exp
-- Pre: The input expression is to be differentiated in terms of "x"
diffEff (Id ex) var
  | ex == var  = Val 1
  | otherwise  = Val 0
diffEff term var
  = case term of
      Val _               -> Val 0
      UnApp Sin x         -> (*) (cos x) (diffEff x var)
      UnApp Cos x         -> negate ((*) (sin x) (diffEff x var))
      UnApp Neg x         -> negate (diffEff x var)
      UnApp Log x         -> (/) (diffEff x var) x
      BinApp Add ex1 ex2  -> (+) (diffEff ex1 var) (diffEff ex2 var)
      BinApp Mul ex1 ex2  -> (+) ((*) ex1 (diffEff ex2 var)) 
                                ((*) (diffEff ex1 var) ex2)
      BinApp Div ex1 ex2  -> (/) ((+) ((*) (diffEff ex1 var) ex2) 
                                (negate ((*) ex1 (diffEff ex2 var)))) 
                                ((*) ex2 ex2)

-- This function makes use of three infinite lists that are combined with
--    zipWith3 which uses a lambda function to calculate each maclaurin term.
-- We take the number of terms from the infinite list as specified in the input
--    and sum these.
-- Uses the more efficient extension diffEff function to calculate differentials
maclaurin :: Exp -> Double -> Int -> Double
-- Pre: The input integer is greater than or equal to zero
-- Pre: The input expression is to be differentiated in terms of "x"
maclaurin expression point term
  = sum (take term (zipWith3 (\x y z -> (eval x [("x", 0)]) * 
      (eval y [("x", point)]) / z) diffs xPower factorials))
  where
    factorials    = scanl (*) 1 [1..]
    diffs         = iterate (flip diffEff "x") expression
    xPower        = iterate ((BinApp Mul) x) (Val 1)

---------------------------------------------------------------------------
-- Test cases...

e1, e2, e3, e4, e5, e6 :: Exp

-- 5*x
e1 = BinApp Mul (Val 5.0) (Id "x")

-- x*x+y-7
e2 = BinApp Add (BinApp Add (BinApp Mul (Id "x") (Id "x")) (Id "y"))
                (UnApp Neg (Val 7.0))

-- x-y^2/(4*x*y-y^2)::Exp
e3 = BinApp Add (Id "x")
            (UnApp Neg (BinApp Div (BinApp Mul (Id "y") (Id "y"))
            (BinApp Add (BinApp Mul (BinApp Mul (Val 4.0) (Id "x")) (Id "y"))
                        (UnApp Neg (BinApp Mul (Id "y") (Id "y"))))))

-- -cos x::Exp
e4 = UnApp Neg (UnApp Cos (Id "x"))

-- sin (1+log(2*x))::Exp
e5 = UnApp Sin (BinApp Add (Val 1.0)
                           (UnApp Log (BinApp Mul (Val 2.0) (Id "x"))))

-- log(3*x^2+2)::Exp
e6 = UnApp Log (BinApp Add (BinApp Mul (Val 3.0) (BinApp Mul (Id "x") (Id "x")))
                           (Val 2.0))
