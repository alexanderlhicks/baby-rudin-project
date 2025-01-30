import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Group.Pointwise.Set.Basic
/-!
desc: Show that for any set A : Set α such that OrderedAddCommGroup α, we have that if A has an infimum then -A has a supremum and inf (A) = - sup (-A)
author: srivatsasrinivasmath
score: 2 
-/

/--For any α that is an ordered additive commutative group, we have that for any set s of elements of α we have that the lower bounds of s are exactly the negative of the upper bounds of -s -/
theorem neg_lower_bound {α : Type u_1} [OrderedAddCommGroup α] {s : Set α} {x : α} : (x ∈ lowerBounds s) ↔ (x ∈ - upperBounds (-s)) := by
  -- unpack the definition for lowerBounds and upperBounds 
  delta lowerBounds upperBounds
  rw [
    -- Rewrite set membership as a proposition
    Set.mem_setOf, 
    -- x ∈ -s if and only if x is in the image of s under the map (fun x => - x) 
    ←Set.image_neg_eq_neg]
    -- Unpack the definition of the image set
  rw [Set.mem_image]
  -- Prove the two cases required for an iff statement p ↔ q
  constructor
  -- If x is a lower bound of s then -x is an upper bound of -s
  case mp => 
    -- introduce hypothesis
    intro h1
    -- In the final answer, we will use -x as the certificate of existence in the goal
    use -x
    -- The goal is of the form p ∧ q, so we seperate the goal into two cases
    constructor
    -- -x is an upper bound of -s
    case h.left =>
      -- Rewrite set membership as a proposition
      rw [Set.mem_setOf]
      -- Introduce the element a of α and the hypothesis that a is in -s
      intros a hs
      -- We have that -a ∈ s
      have : -a ∈ s := by rw[←Set.neg_mem_neg, neg_neg]; exact hs 
      -- So we plug in the fact that -a ∈ s into h1 to show that x ≤ -a
      have := h1 this 
      -- Negate both sides to flip the inequality 
      have := neg_le_neg this
      -- - - a = a
      rw[neg_neg] at this 
      exact this
    -- - - x = x
    case h.right => 
      -- -x is indeed equal to negative x 
      rw[neg_neg]
  -- If -x is an upper bound of -s then x is a lower bound of s
  case mpr => 
    -- h says that there is an upper bound of -s whose negative is x. Now we want to show that x is a lower bound of s
    intros h x_1 hx_1
    -- from h we deduce that existence of an upper bound of -s and name it x_2, such that -x_2 = x.  
    rcases h with ⟨ x_2,
                    -- The hypothesus that x_2 is an upper bound of -s
                    hs,
                    -- The hypothesis that -x_2 = x
                    hneg⟩
    -- Rewrite the goal in terms of x_2
    rw [←hneg]
    -- Rewrite set membership as a proposition
    rw [Set.mem_setOf] at hs 
    -- We know that since x_1 ∈ s, that -x_1 ∈ -s 
    have := Set.neg_mem_neg.mpr hx_1 
    -- Thus we can show that -x_1 ≤ x_2
    have := hs this
    -- So -x_2 ≤ - - x_1
    have := neg_le_neg this
    -- Use the fact that - - x_1 = x_1
    rw[neg_neg] at this 
    exact this 
  
/-- Show that for any set A : Set α such that OrderedAddCommGroup α, we have that if A has an infimum then -A has a supremum and inf (A) = - sup (-A) -/  
theorem problem5 {α: Type u_1} [OrderedAddCommGroup α] {s : Set α} {x : α} (hlub : IsGLB s x) : IsLUB (-s) (-x) := by
  -- Unpack the definitions of IsLUB, IsLeast
  delta IsLUB IsLeast
  -- Unpack the definitions of IsGLB and IsGreatest in hlub
  delta IsGLB IsGreatest at hlub
  -- h1 is the hypothesis that x is a lower bound of s and h2 is the hypothesis that it is an upper bound on the lower bounds
  rcases hlub with ⟨h1,h2⟩
  -- The goal has two cases, one where we show that -x is an upper bound of -s and the other is that -x is a lower bound of the upper bounds 
  constructor
  -- Show that -x is an upper bound of -s
  case left =>
    -- Rewrite so that the goal is x ∈ - upperBounds -s
    rw [←Set.neg_mem_neg, neg_neg]
    -- Now we use the above theorem neg_lower_bound combined with the fact that h1 is a lower bound of s to deduce that x ∈ - upperBounds (-s)
    exact (neg_lower_bound.mp h1)
  -- Show that -x is the least upper bound of -s
  case right =>
    -- We can rewrite lowerBounds (upperBounds (-s)) as - upperBounds (-upperBounds (-s))
    rw [neg_lower_bound]
    -- Create a universal quantifier version of neg_lower_bound
    have : ∀y : α, y ∈ lowerBounds s ↔ y ∈ - upperBounds (-s) := by exact (fun y => neg_lower_bound) 
    -- Show that lowerBounds s = - (upperBounds -s)
    have : lowerBounds s = - upperBounds (-s) := by exact (Set.ext this)
    -- Now we only have a bunch of rewrites left. We once again rewrite - upperBounds (-s) as lowerBounds s, and we are done!
    rw [←this, Set.neg_mem_neg]
    exact h2 

    
        
  
  
 


