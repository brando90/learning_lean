-- define a point using structures in lean4
import Std
import Mathlib.Data.Real.Basic

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point
#check Point.ext -- Point.ext (x y : Point) (x : x.x = y.x) (y : x.y = y.y) (z : x.z = y.z) : x = y
#check Point.mk

def point1 : Point := ⟨1, 2, 3⟩
def point2: Point := ⟨1, 2, 3⟩
def point3: Point := Point.mk 1 2 3

theorem point1_eq_point2 : point1 = point2 := by
  unfold point1 point2
  #check Point.ext -- ⊢ ∀ (x y : Point), x.x = y.x → x.y = y.y → x.z = y.z → x = y
  apply Point.ext
  . simp
  . simp
  . simp

example : point2 = point3 := by rfl

theorem any_point1_eq_point2 (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  #check Point.ext -- ⊢ ∀ (x y : Point), x.x = y.x → x.y = y.y → x.z = y.z → x = y
  ext
  repeat' assumption
