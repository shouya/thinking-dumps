import Data.Fin

data Vect : Nat -> Type -> Type where
  VNil : Vect 0 a
  VCons : a -> Vect n a -> Vect (S n) a

vecToList : Vect n a -> List a
vecToList VNil = []
vecToList (VCons x xs) = x :: (vecToList xs)

listToVec : (xs : List a) -> Vect (length xs) a
listToVec [] = VNil
listToVec (x :: xs) = VCons x (listToVec xs)


restN : (n : Fin) -> Type
restN FZ  = Nat
restN (FS FZ) = Nat -> Nat
restN _ = Nat -> Nat -> Nat


foo : (n : Fin) -> restN n
foo FZ = 0
foo (FS FZ) = \x => x + 1
foo _ = \x, y => x + y
