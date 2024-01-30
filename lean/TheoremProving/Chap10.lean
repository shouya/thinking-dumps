structure Point (α : Type) where
  x : α
  y : α
deriving Repr

#check Point.rec
-- ⊢ {α : Type} →
--   {motive : Point α → Sort u} →
--   ((x y : α) → motive { x := x, y := y }) →
--   (t : Point α) →
--   motive t
#check Point.mk
-- ⊢ {α : Type} → α → α → Point α

structure Point2 (α : Type) where
  mk :: (x : α) (y : α)


namespace TypeClassPlayground

structure Add (α : Type) where
  add : α → α → α

def double (s: Add α) (x : α) : α := s.add x x

class AddTC (α : Type) where
  add : α → α → α

#check AddTC.add
-- ⊢ {α : Type} → [self : AddTC α] → α → α → α

instance : AddTC Nat where
  add := Nat.add

instance : AddTC (Point Nat) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

def doubleTC [AddTC α] (x : α) : α := AddTC.add x x

#eval doubleTC 10
#eval doubleTC { x := 10, y := 20 : Point Nat }

instance [AddTC α] : AddTC (Array α) where
  add x y := Array.zipWith x y AddTC.add

#eval doubleTC #[1, 2, 3]

end TypeClassPlayground

-----------------

namespace OfNatPlayground

instance [OfNat α n] : OfNat (Point α) (n : Nat) where
  ofNat := { x := OfNat.ofNat n, y := OfNat.ofNat n }

#eval (10 : Point Nat)

def foo : Add Nat := inferInstance

#print foo

#check inferInstance
-- ⊢ {α : Sort u} → [i : α] → α

end OfNatPlayground
