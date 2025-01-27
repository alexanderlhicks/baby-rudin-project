# Baby Rudin Project

Welcome to the baby Rudin project. This is a collection of problems solved in Rudin along with their step-by-step natural language explanations. The goal of this project is to encourage new users of Lean to learn Lean better while contributing to a data set that can be used for machine learning in theorem proving.

If you would like to contribute please do the following: 
1. File an issue with the chapter and problem number from baby rudin
2. Create a pull request solving that problem in the folder BabyRudinProject/Chapter\<number\>/Problem\<number\>.lean
For example, Problem 4 from Chapter 5 would go into the folder BabyRudinProject/Chapter5/Problem4.lean. The solution has to be of the following format
- The start of the file should containt a comment enclosed by /-! -/ and should contain the following information: 
  - A natural language description of the problem, desc
  - The author name, author
  - A difficulty score of the problem, score
  - Any other comments, comments
  
  For example, for Chapter 1 Problem 1 the file BabyRudinProject/Chapter1/Problem1.lean can start with the following 
    ````lean4
    /-!
    desc: Show that if r ∈ ℚ and that r ≠ 0 then we have that for any x ∈ ℝ that is irrational we that both r*x and r+x are irrational
    difficulty: 0.5
    author: srivatsasrinivasmath
    comments: This is a test comment
    -/
    ````
- Every declaration in the file should be preceeded with a docstring comment <code> /-- description -/ </code> containing the natural language description of the declaration. Every tactic should be "appropriately" explained with comments. You can skip explaining a few tactics if they are "obvious". 

  For example, in Chapter 1 Problem 2 we see the following 
  ````lean4
  /-- If 3 ∣ m then 3 ∣ m^2 -/
  theorem three_div_sq {m : ℤ} (h : 3 ∣ m^2) : (3 ∣ m ) := 
    by
      rw [-- m^2 = m*m
          pow_two, 
          -- 3 is a prime so if 3 ∣ m*m then 3∣m ∨ 3∣m
          Int.prime_three.dvd_mul, 
          -- p ∨ p ⇒ p
          or_self] at h
      exact h 
  ````

That is all! We hope you can contribute! 

