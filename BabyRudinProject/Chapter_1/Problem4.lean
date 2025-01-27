import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
/-!
desc: Let E be a nonempty ordered set; suppose that α is an upper bound and β is a lower bound of E. Prove that α ≤ β
score: 0.5
author: srivatsasrinivasmath
-/

/-- Let E be a nonempty ordered set; suppose that α is a lowerbound and β is an upper bound of E. Prove that α ≤ β. 
 In this situation we have to grant a Preorder on A, since we need transitivity. When people talk about "orderings" they usually are talking about pre-orderings 
-/
theorem problem4 {A : Type u_1} [Preorder A] (s : Set A) (ne : Set.Nonempty s) (α : A) (hα : α ∈ lowerBounds s) (β : A) (hβ : β ∈ upperBounds s) : α ≤ β := by 
  -- obtain an x that is in the set s and the proof, hx, that it is in the set 
  obtain ⟨x,hx⟩ := ne
  -- by definition α ≤ x 
  have α_le_x : α ≤ x := by exact hα hx 
  -- by definition x ≤ β
  have x_le_β : x ≤ β := by exact hβ hx
  -- apply the transitivity of the pre-order 
  exact (le_trans α_le_x x_le_β)


