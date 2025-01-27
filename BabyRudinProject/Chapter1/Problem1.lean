import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
/-!
desc: Show that if r ∈ ℚ and that r ≠ 0 then we have that for any x ∈ ℝ that is irrational we that both r*x and r+x are irrational
difficulty: 0.5
author: srivatsasrinivasmath
-/

theorem problem1 (r : ℚ) (x: ℝ) : (r ≠ 0) -> (Irrational x) -> (Irrational (r + x)) ∧ (Irrational (r * x)):= 
  by
    --Introduce the hypothesis $r ≠ 0$ and $x$ is irrational
    intros rneq0 x_irr 
    --Let us see what we get when we use, simp. Since Lean4 knows that the sum and product of two rationals is rational, after definition chasing it trivializes the problem
    simp [rneq0, x_irr]
  
