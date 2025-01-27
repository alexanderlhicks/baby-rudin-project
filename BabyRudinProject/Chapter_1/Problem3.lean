import Mathlib.Algebra.Field.Basic 
/-!
desc: If x,y,z are elements in a field F then show that the following are true
a)  If x ≠ 0 and xy = xz then x = y 
b)  If x ≠ 0 and xy = x then y = 1 
c)  If x ≠ 0 and xy = 1 then y = 1/x 
d)  If x ≠ 0 then 1/(1/x) = x

In Lean we have that 1/0 is defined to be 0
score: 0.5
author: srivatsasrinivasmath
-/

/-- If x,y,z are elements in a field F and x ≠ 0 then xy = xz ⇒ y = z -/
theorem problem3a {F : Type u_1} [Field F] (x y z : F) (hx : x ≠ 0) (heq : x*y = x*z) : y = z := by
  -- We use the fact that left multiplication by an invertible element in a field is injective
  apply (mul_right_inj' hx).mp 
  -- We now use the hypothesis 
  exact heq

/-- If x,y,z are elements in a field F and x ≠ 0 then xy = x ⇒ y = 1 -/ 
theorem problem3b {F : Type u_1} [Field F] (x y : F) (hx : x ≠0) (heq : x*y = x) : y = 1 := by  
  -- We use the fact that x = x*1
  have : x = x*1 := by exact Eq.symm (mul_one x)
  -- We rewrite the right hand side of the hypothesis x*y = x to get x*y = x*1
  conv at heq => 
    rhs  
    rw [this]
  -- Apply problem3a to x y 1 deduce that y = 1
  exact problem3a x y 1 hx heq 

/-- If x,y are elements in a field F and x ≠ 0 then xy = 1 ⇒ y = 1/x -/ 
theorem problem3c {F : Type u_1} [Field F] (x y : F) (hx : x ≠ 0) (heq : x*y = 1) : y = x⁻¹ := by 
  -- We use the fact that x*x⁻¹ = 1 when x ≠ 0
  have : 1 = x*x⁻¹ := by exact Eq.symm (mul_inv_cancel₀ hx)
  -- We rewrite the right hand side of heq to be x*x⁻¹
  conv at heq =>
    rhs
    rw [this]
  -- We apply problem3a to x y x⁻¹ to deduce that y = x⁻¹
  exact problem3a x y x⁻¹ hx heq

/-- If x ≠ 0 then 1/(1/x) = x -/
theorem problem3d {F: Type u_1} [Field F] (x : F) : x⁻¹⁻¹ = x := by 
  -- This is proved in mathlib so we reuse it
  exact inv_inv x
