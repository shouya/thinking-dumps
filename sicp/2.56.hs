type Var = String

data Expr = Sum Expr Expr
          | Prod Expr Expr
          | I Integer
          | V Var
          deriving Eq

instance Show Expr where
  show (I i)
    | i < 0     = "(" ++ show i ++ ")"
    | otherwise = show i
  show (V x) = x
  show (Prod s@(Sum _ _) t@(Sum _ _)) = "(" ++ show s ++ ")*" ++
                                        "(" ++ show t ++ ")"
  show (Prod s@(Sum _ _) c) = "(" ++ show s ++ ")*" ++ show c
  show (Prod a s@(Sum _ _)) = show a ++ "*(" ++ show s ++ ")"
  show (Prod a b) = show a ++ "*" ++ show b
  show (Sum  a b) = show a ++ "+" ++ show b


derivative :: Expr -> Var -> Expr
derivative (Sum  u v) x = mkS (derivative u x) (derivative v x)
derivative (Prod u v) x = mkS udv vdu
  where udv = mkP u $ derivative v x
        vdu = mkP v $ derivative u x
derivative (I _) _ = I 0
derivative (V x') x = I $ if x == x' then 1 else 0 -- partial derivative


mkS :: Expr -> Expr -> Expr
mkS (I 0) a = a
mkS a (I 0) = a
mkS (I a) (I b) = I (a + b)
mkS a b
  | a == b    = mkP (I 2) a
  | otherwise = Sum a b


mkP :: Expr -> Expr -> Expr
mkP (I 1) a = a
mkP a (I 1) = a
mkP (I 0) _ = I 0
mkP _ (I 0) = I 0
mkP (I a) (I b) = I (a*b)
mkP a b = Prod a b





main :: IO ()
main = do
  let expr = Prod (V "x") (V "x")
    in print (derivative expr "x")
