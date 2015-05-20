

type Var = String

data Expr = Sum Expr Expr
          | Prod Expr Expr
          | I Integer
          | V Var

instance Show Expr where
  show (I i)
    | i < 0 = "(" ++ show i ++ ")"
    | _     = show i
  show (V x) = x
  show (Prod s@(Sum _ _) t@(Sum _ _)) = "(" ++ show s ++ ")*" ++
                                        "(" ++ show t ++ ")"
  show (Prod s@(Sum _ _) c) = "(" ++ show s ++ ")*" ++ show c
  show (Prod a s@(Sum _ _)) = show a ++ "*(" ++ show s ++ ")"
  show (Prod a b) = show a ++ "*" ++ show b
  show (Sum  a b) = show a ++ "+" ++ show b


derivative :: Expr -> Var -> Expr
derivative (Sum  u v) x = Sum (derivative u x) (derivative v x)
derivative (Prod u v) x = Sum udv vdu
  where udv = Prod u $ derivative v x
        vdu = Prod v $ derivative u x
derivative (I _) x = 0
derivative (V x') x = if x == x' then 1 else 0 -- partial derivative
