module Interpreter

import Data.Fin
import Data.Vect

data Ty = TyInt | TyBool | TyFun Ty Ty


interpTy : Ty -> Type
interpTy TyInt = Integer
interpTy TyBool = Bool
interpTy (TyFun x y) = interpTy x -> interpTy y

using (G : Vect n Ty)
  -- See 'De Bruijn index'

  -- HasType i G t means variable i in context G has type t
  -- This type acts like a Nat, like an index to variables
  data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
    Stop : HasType FZ (t :: G) t
    Pop  : HasType k G t -> HasType (FS k) (u :: G) t

  data Expr : Vect n Ty -> Ty -> Type where
    Var : HasType i G t -> Expr G t
    Val : (x : Integer) -> Expr G TyInt
    Lam : Expr (a :: G) t -> Expr G (TyFun a t)
    App : Expr G (TyFun a t) -> Expr G a -> Expr G t
    Op  : (interpTy a -> interpTy b -> interpTy c) ->
          Expr G a -> Expr G b -> Expr G c
    If  : Expr G TyBool -> Lazy (Expr G a) -> Lazy (Expr G a) -> Expr G a

  data Env : Vect n Ty -> Type where
    Nil  : Env Nil
    (::) : interpTy a -> Env G -> Env (a :: G)

  lookup : HasType i G t -> Env G -> interpTy t
  lookup Stop    (x :: xs) = x
  lookup (Pop k) (x :: xs) = lookup k xs

  interp : Env G -> Expr G t -> interpTy t
  interp env (Var i) = lookup i env
  interp env (Val x) = x
  interp env (Lam f) = \x => interp (x :: env) f
  interp env (App f x) = (interp env f) (interp env x)
  interp env (Op f x y) = f (interp env x) (interp env y)
  interp env (If b x y) = if interp env b
                          then interp env x
                          else interp env y
