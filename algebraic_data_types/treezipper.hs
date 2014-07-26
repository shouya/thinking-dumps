

data Tree a = Empty | Node a (Tree a) (Tree a)

data Empty' = Empty'                    -- 1
data Node' a = Node' (a, Tree' a, Tree' a)    -- a * T(a) * T(a)
type Tree' a = Either Empty' (Node' a)  -- 1 + a * T(a) * T(a)

{-
https://chris-taylor.github.io/images/tree.png
-}

data TZTrace a = TZTrace { tztcurr :: a
                         , tztleft :: Tree a
                         , tztright :: Tree a
                         }

data TreeZipper a = TZ { curr :: a
                       , lchild :: Tree a
                       , rchild :: Tree a
                       , btrace :: [TZTrace a]
                       }

left :: TreeZipper a -> TreeZipper a
left (TZ _ Empty _ _) = error "empty on left"
left (TZ cur (Node n ll lr) r bt) =
  TZ { curr = n
     , lchild = ll
     , rchild = lr
     , btrace = (TZTrace { tztcurr = cur
                         , tztleft = Empty
                         , tztright = r
                         }):bt
     }

right :: TreeZipper a -> TreeZipper a
right (TZ _ _ Empty _) = error "empty on right"
right (TZ cur l (Node n rl rr) bt) =
  TZ { curr = n
     , lchild = rl
     , rchild = rr
     , btrace = (TZTrace { tztcurr = cur
                         , tztleft = l
                         , tztright = Empty
                         }):bt
     }

up :: TreeZipper a -> TreeZipper a
up (TZ _ _ _ []) = error "already on the top"
up (TZ cur l r ((TZTrace tztcur Empty tztr):bt)) =
    TZ { curr = tztcur
       , lchild = Node cur l r
       , rchild = tztr
       , btrace = bt
       }

up (TZ cur l r ((TZTrace tztcur tztl Empty):bt)) =
    TZ { curr = tztcur
       , lchild = tztl
       , rchild = Node cur l r
       , btrace = bt
       }

up (TZ _ _ _ ((TZTrace _ _ _):_)) = error "invalid backtrace"
