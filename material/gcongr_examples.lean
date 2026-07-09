import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Int.ModEq


-- we notice in our fist example, that there are some congruences, and as the name hints, we could give gcongr a try
example (h1 : 0 ≡ a [ZMOD 7]) (h2 : 0 ≡ b [ZMOD 7]) : b ≡ a + 1 [ZMOD 7] → 0 ≡ 0 + 1 [ZMOD 7] := by sorry

















-- the normal gcongr trace doesn't shows you, which gcongr lemmas it tries to apply. So you can copy the file from https://github.com/HerrLaal/mathlib4/blob/master/Mathlib/Tactic/GCongr/Core.lean or maybe from the github of the seminar
set_option trace.Meta.gcongr true


-- try some different depths with gcongr 0, gcongr 1 and so on, or with different templates like gcongr ?_ + ?_ and check how the trace changes
example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr --x ^ 2 * ?_ + ?_
  · linarith
  · linarith



























open Finset


-- try to name some variables with the `with` notation for the second goal out of gcongr
example {a : ℤ} {n : ℕ} (ha : ∀ i < n, 2 ^ i ≤ a) :
    ∏ i ∈ range n, (a - 2 ^ i) ≤ ∏ _i ∈ range n, a := by
  gcongr --with p hp
  · intro i hi
    simp only [mem_range] at hi
    linarith [ha i hi]
  · simp























-- we define our own general realtion
@[irreducible]
def r : ℕ → ℕ → Prop := fun _ ↦ fun _ ↦ sorry


@[refl]
lemma r_refl {a : ℕ} [Std.Refl r] : r a a := Std.Refl.refl a

-- and see that gcongr can work with this relation
example {a : ℕ} [Std.Refl r] : r a a := by
  gcongr

-- but gcongr also works with implications and has also gcongr lemmas for implications
example {a b c d: ℕ} (h₁ : r c a) (h₂ : r b d) [IsTrans ℕ r] : r a b → r c d := by
  gcongr

















-- now we state our own gcongr lemma (yeah!). Which hypotheses of it are main goals and which are side goals?
@[gcongr]
lemma my_div {m n p : ℕ} (h₁ : 0 < n) (h₂ : n < m) (h₃ : m < p) : m / n < p / n := by sorry

-- in the trace you will find the answer.
example {m n p : ℕ} (h₁ : 0 < n) (h₂ : n < m) (h₃ : m < p) : m / n < p / n := by gcongr



















section myAdd
-- here you can test the options for a gcongr tag. Some hints:
-- if you don't write local or scoped, the lemma is added global
-- local: only in your section
-- scoped: only in your namespace
-- higher priorities are tried out first and some numbers are also given by the wods `high`, `default` and `low`
-- the default priority is 1000
@[local gcongr 1000]
lemma my_add_le_add {a b c d : ℕ} (h₁: a ≤ b) (h₂: c ≤ d): a + d ≤ b + c := by sorry


example {a b c d : ℕ} (h₁: a ≤ b) (h₂: c ≤ d): a + d ≤ b + c := by
  gcongr

end myAdd

example {a b c d : ℕ} (h₁: a ≤ b) (h₂: c ≤ d): a + d ≤ b + c := by
  gcongr





















-- sometimes the lemma can't be added to the grw lemmas, which also uses gcongr lemmas. Then you get the error message that tells you that you have to use @[gcongr only]
@[gcongr]
lemma lt_iff_lt {a b: ℕ} : a < b ↔ b < a := by
 sorry

-- in this case we have given now the exact statement as an iff lemma
example {a b: ℕ} : a < b ↔ b < a := by
 gcongr


-- but we don't get one implication out of the lemma, hence we have to state it seperately

--@[gcongr only]
--lemma lt_imp_lt {a b: ℕ} : a < b → b < a := by
-- sorry

example {a b: ℕ} : a < b → b < a := by
 gcongr

-- now we have also given one implication, but we still can't prove the same statement given in the form of a hypothesis and a goal
-- so let's try to also add this as a gcongr lemma

--@[gcongr only]
--lemma h_lt_lt  {a b: ℕ} (h: a < b) : b < a := by
--  sorry

example {a b: ℕ} (h: a < b) : b < a := by
 gcongr

-- unfortunately this is aslo added as the implication, otherwise it would not match the pattern of a gcongr lemma, since we don't apply a function
-- and we don't try to look at the lemma where we don't can apply a gcongr lemma as an implication
-- do you have an idea, why they decided it to behave like this?















-- some more test on the equivalences, since they can be confusing
-- define some funtion on the same way
@[irreducible]
def f : ℕ → ℕ := fun _ ↦ sorry

@[irreducible]
def g : ℕ → ℕ := fun _ ↦ sorry

-- and try to have the folling gcongr lemma, which is symmetric in f and g
-- notice here that if you leave out the `only` the error message will not help you, so sometimes you must be confident with your gcongr lemma and just try out the `only`
@[gcongr only]
lemma f_iff_g {a b} : f a < f b ↔ g a < g b := by sorry

-- we state now the symmetric statements in f and g and only the implication from the rhs to the lhs is added, since it will stop trying the other direction if this works
example {a b : ℕ} (h: f a < f b): g a < g b := by gcongr

example {a b : ℕ} (h: g a < g b): f a < f b := by gcongr


-- here we now get only the implication from the lhs to the rhs, since an the lhs we are not applying a function and can't take this as a goal
-- notice that we get this only in the form of a hypothesis and a goal and not as the implication
@[gcongr]
lemma lt_iff_f_eq {a b} : a < b ↔ f a = f b := by sorry

-- but we can fix this with using an `intro lhs`
example {a b : ℕ}: a < b → f a = f b := by gcongr

example {a b : ℕ} (h: a < b) : f a = f b := by gcongr

















open Mathlib.Tactic.GCongr

-- here you can get an idea of how the forward reasoning tactics are added
-- this only takes a hypothesis and the goal and checks whether they are definitionaly equal and if so, it assigns the hypothesis to the goal
-- this solves the goal sice for us the goal is a meta variable
@[gcongr_forward] def my_exact : ForwardExt where
  eval hyp goal := goal.assignIfDefEq hyp
















-- one example on rel, feel free to test a little bit
-- notice that the forward reasoning part is shorter
example {a b : ℕ} (ha : a ≥ 5) (hb: b ≥ 7) : a * (a + b) ≥ a * (5 + b) := by rel [ha]






















-- Below are the solutions of the examples in the sliedes, maybe first test on your own, whether you can decide if the statements are correct























example {a : ℕ} : a ≥ 0 := by
  gcongr


example {a : ℕ} (h: a ≥ 0) : a ≥ 0 := by
  gcongr


example {a : ℕ} : a ≥ 0 := by
  gcongr_discharger


example {a : ℕ} (h: a ≥ 0) : a ≥ 0 := by
  gcongr_discharger

























@[gcongr]
theorem of_eq_r {a b : ℕ} (h : a = b) [Std.Refl r] : r a b := by
  exact of_eq h -- this solves the goal

example {a b c : ℕ} (h : a  = b) [Std.Refl r]: r (a + c) (b + c) := by
  gcongr
  linarith

























@[gcongr]
theorem of_eq_r_2 {a b : ℕ} (h : a = b) [Std.Refl r] : r (id a) (id b) := by
  exact of_eq h -- this solves the goal

example {a b c : ℕ} (h : a  = b) [Std.Refl r]: r (id (a + c)) (id (b + c)) := by
  gcongr
  linarith

























@[gcongr only]
lemma my_imp {a b : ℕ} : r a b → r b a := by
  sorry

example {a b : ℕ} : r b a → r a b := by
  gcongr

























example (h : a → b) : (a ∧ ¬b) ∨ c → (b ∧ ¬a) ∨ c := by gcongr
example (h : a → b) : (a ∧ ¬b) ∨ c → (b ∧ ¬a) ∨ c := by gcongr ?_
example (h : a → b) : (a ∧ ¬b) ∨ c → (b ∧ ¬a) ∨ c := by gcongr ?_ ∧ ¬?_ ∨ c

























example {x y : ℤ} (hx : x ≥ 12) : y + x * x ≥ y + 12 * x := by rel [hx]
