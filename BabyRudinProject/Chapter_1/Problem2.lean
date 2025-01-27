import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Nat.Prime.Int 
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Qify 

/-!
desc: Show that there is no rational whose square is 12 
author: srivatsasrinivasmath
score: 2 
comments: theorem help1 is due to Rubden Van de Velde on Zulip (https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/.E2.9C.94.20What.20is.20the.20easiest.20way.20to.20deal.20with.20rationals.3F/near/495907421)
-/ 

/-- If there exists q in ℚ such that q*q = 12 then there exists m,n ∈ ℤ such that m^2 = 12*n^2 and gcd(m,n) = 1 -/
theorem help1 (q : ℚ) (hq : q*q = 12) : ∃ m n : ℤ, (m^2 = 12*n^2) ∧ (m.gcd n = 1) := by
  -- m and n are going to be the numerator and denominator of q 
  use q.num, q.den 
  -- construct the two propositions in the conjection that is the output
  constructor
  -- construct a proof of m^2 = 12*n^2. We use the tactic qify which converts the expression m^2 = 12*n^2 into an equality over ℚ
  . qify
  -- Algebra
    rw[ -- Rewrite 12 as q*q 
        <-hq, 
        -- Rewrite m^2 as m*m  
        sq, 
        -- Rewrite n^2 as n*n
        sq, 
        -- Rewrite q*q*(n*n) = q*n*q*n 
        mul_mul_mul_comm, 
        -- q*n = m, so we are done because we get m*m = m*m 
        Rat.mul_den_eq_num]
    -- Rewrite the definition of gcd with that of Nat.Coprime
  . rw [Int.gcd, Int.natAbs_ofNat, <-Nat.Coprime]
    exact q.reduced

/-- If 3 ∣ m then 3 ∣ m^2 -/
theorem three_div_sq {m : ℤ} (h : 3 ∣ m^2) : (3 ∣ m ) := 
  by
    rw [-- m^2 = m*m
        pow_two, 
        -- 3 is a prime so if 3 ∣ m*m then 3∣m ∨ 3∣m
        Int.prime_three.dvd_mul, 
        -- p ∨ p = p
        or_self] at h
    exact h 

/-- If gcd(m,n) = 1 then we cannot have that m^2 = 12*n^2 -/
theorem gcd_cant_be_one {m n : ℤ} (h : m.gcd n = 1) : (m^2 ≠ 12*n^2) := 
  by
    -- introduce the hypothesis that m^2 = 12*n^2 
    intro sqr_eq
    -- 12 divides m^2
    have : ((12 : ℤ) ∣ m^2) := by 
      -- the witness is n^2 since 12*n^2 = m^2
      exists n^2
    -- 3 divides 12 
    have three_div12 : (3 : ℤ) ∣ 12 := by 
      exact Int.dvd_of_emod_eq_zero rfl 
    -- So 3 divides m 
    have : (3 : ℤ) ∣ m := by
      have : (3 : ℤ) ∣ m^2 := by exact Int.dvd_trans three_div12 this
      exact three_div_sq this
    -- Obtain m' such that m = 3*m' and the hypothesis m = 3*m' 
    obtain ⟨m',h1⟩ := this
    -- Now we want to show that 3*(3*(m')^2) = 3*(4*n^2)
    have : (3*(3*(m')^2) = 3*(4*n^2)) := by 
    -- Rewrite m as as 3*m' in sqr_eq
      rw [h1] at sqr_eq
    -- Simplify sqr_eq 
      ring_nf at sqr_eq
    -- Simplify the goal 
      ring_nf
    -- They are now the same
      exact sqr_eq
    -- Cancel out the three on both sides of the above equation
    have : (3*(m')^2 = 4*n^2) := by  
      exact (mul_right_inj' (by norm_num)).mp this
    -- Now we can show that 3 ∣n^2
    have : (3 ∣ n^2) := by 
      -- Show that 3 ∣ $*n^2 by this (which refers to 3*(m')^2 = 4*n^2)
      have h2 : 3 ∣ 4*n^2 := by 
        exists (m')^2 
        exact (Eq.symm this)
      -- Now show that 3 ∣ n^2
      have h3: 3 ∣ n^2 := by 
        -- Since 3 is a prime 3 ∣ 4*n^2 only if 3 ∣ 4 or 3 ∣ n^2
        rw [Int.prime_three.dvd_mul] at h2
        cases h2 with
        -- Case 3 ∣ 4. Not possible
        |inl hl => contradiction 
        -- Case 3 ∣ n^2. This implies that 3 ∣ n^2
        |inr hr => exact hr
      exact h3
    -- From before we know that 3 ∣ m 
    have three_div_m : (3 : ℤ) ∣ m := by exists m'
    -- Since 3 ∣n^2, we know that 3 ∣ n
    have : (3 ∣ n) := by exact (three_div_sq this)
    -- Therefore 3 divides the gcd of m and n
    have : (3 : ℤ) ∣ m.gcd n := by 
      exact (Int.dvd_gcd three_div_m this)
    -- So three divides 1
    have : (3 : ℤ) ∣ 1 := by 
      rw [h] at this
      exact this
    -- This is obviously a contradiction and hence we deduce False : Prop
    norm_num at this
    
/-- There does not exist a rational whose square is 12 -/ 
theorem problem2 : ¬ (∃ q : ℚ, q*q = 12) := by
  -- Assume that there exists such a rational
  intro h
  -- Let the rational be q and let h1 be the hypothesis that q*q = 12
  obtain ⟨q,h1⟩ := h
  -- We now obtain that there exist m,n whose gcd is 1 yet m^2 = 12*n^2
  obtain e := help1 q h1
  -- Obtain the hypothesis h3 
  rcases e with ⟨_,_,_,h3⟩
  -- Plug h3 into gcd_cant_be_one to get a contradiction
  obtain f := gcd_cant_be_one h3
  contradiction




      









