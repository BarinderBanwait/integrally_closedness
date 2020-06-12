/-
Copyright (c) 2020 Barinder Singh Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder Singh Banwait, with lots of help from the good folk on the Leanprover Zulip chat :)
-/
import ring_theory.noetherian
import ring_theory.integral_closure
import ring_theory.adjoin
import ring_theory.algebra
import linear_algebra.basic

/-!
# Integrally closedness

Let R ⊆ A be an extension of integral domains.

## Main definitions

* `is_integrally_closed_in R A : Prop` is the assertion that `R` is integrally closed in `A`. It is
   a structure, implemented as the predicate that all elements of `A` that are integral over `R` 
   already belong to `R`.

* `is_integrally_closed R` is the definition that `R` is integrally closed in an absolute sense.
   This is implemented as the following implication: if for all `r` and `s` in `R` with `s ≠ 0`, 
   `r^n ∈ ⟨ r^{n-1}s, ⋯ , s^n ⟩ 


## Main statements

* `this` is that lemma, in the following form:
  if N is a finitely generated submodule of an ambient R-module M and I is an ideal of R
  such that N ⊆ IN, then there exists r ∈ 1 + I such that rN = 0.

## References

* [J. Neukirch, *Algebraic Number Theory*][neukirch-ant]

## Tags

Integrally closed

-/

universes u v

variables (R : Type u) {A : Type v}
variables [comm_ring R] [comm_ring A]
variables [algebra R A]
variables i : ℕ
variables (K : Type*)
open submodule
open function
open finset
open_locale big_operators

structure is_integrally_closed_in (R : Type u) (A : Type v) [comm_ring R] [comm_ring A] 
[algebra R A] : Prop := 
(inj : injective (algebra_map R A))
(closed : ∀ (a : A), is_integral R a → ∃  r : R, algebra_map R A r = a)

-- def my_set (R) [integral_domain R] (r : R) (s : R) (n : ℕ) := 
-- { x | ∃ (i:ℕ ) (h : 0≤ i) (h2 :i≤ n-1), x = r^(n-1-i) *s^(i+1) }

def my_set (R) [integral_domain R] (r : R) (s : R) (n : ℕ) := 
{ x | ∃ (c : ℕ × ℕ) (hy: c ∈ (finset.nat.antidiagonal n).erase ⟨0, n⟩), x = r ^ c.2 * s ^ c.1 }

def is_integrally_closed (R) [integral_domain R] : Prop :=
∀ (r : R) (s : R), (s ≠ 0) ∧ (∃ n : ℕ , 
r^n ∈ span R (my_set R r s n)) → s ∣ r

lemma equiv_johan_absolute (R) [integral_domain R] :
  is_integrally_closed R ↔ ∀ ⦃r s : R⦄, s ≠ 0 → (∃ (n : ℕ) (f : ℕ → R) (hf : f 0 = 1), 
  ∑ ij in finset.nat.antidiagonal n, f ij.1 * r ^ ij.2 * s ^ ij.1 = 0) → s ∣ r :=
begin
  split,
  intros h r s,
  intro k,
  unfold is_integrally_closed at h,
  specialize h r s,
  intro m,
  apply h,
  split,
  exact k,
  cases m with n m1,
  cases m1 with f m2,
  cases m2 with hf m3,
  use n,
  rw mem_span,
  intro p,
  intro p_H,
  rw my_set at p_H,
  sorry,
  sorry,
end

open submodule

lemma mwe (R) [integral_domain R] (n : ℕ) (f : ℕ → R) (hf : f 0 = 1) : ∀ ⦃r s : R⦄, s ≠ 0 → 
  ∑ ij in finset.nat.antidiagonal n, f ij.1 * r ^ ij.2 * s ^ ij.1 = 0 → 
  r^n ∈ span R (my_set R r s n) :=
begin
  intros r s,
  intro s_non_zero,
  intro H,
  let p' : ℕ × ℕ := ⟨0, n⟩,
  have LM : p' ∈ finset.nat.antidiagonal n,
  {
    rw finset.nat.mem_antidiagonal,
    linarith,
  },
  rw ← finset.insert_erase LM at H,
  simp at H,
  rw hf at H,
  simp at H,
  have KL : r^n = -∑ (x : ℕ × ℕ) in (nat.antidiagonal n).erase p', f x.fst * r ^ x.snd * s ^ x.fst,
  {
    exact eq_neg_of_add_eq_zero H,
  },
  rw KL,
  rw my_set,
  rw mem_span,
  intro p,
  intro p_H,
  rw ideal.neg_mem_iff p,
  apply sum_mem,
  intro c,
  intro c_H,
  have x_in_my_set : r ^ c.snd * s ^ c.fst ∈ {x : R | ∃ (c : ℕ × ℕ) (hy : c ∈ (nat.antidiagonal n).erase (0, n)), x = r ^ c.snd * s ^ c.fst},
  {
    simp,
    use c.fst,
    use c.snd,
    split,
    split,
    intro something,
    by_contradiction HAPPY,
    have obv : c = p',
    {
      exact prod.ext something HAPPY,
    },
    rw obv at c_H,
    rw mem_erase at c_H,
    cases c_H,
    contradiction,
    rw ← finset.nat.mem_antidiagonal,
    rw mem_erase at c_H,
    cases c_H with c_H_1 c_H_2,
    exact c_H_2,
    refl,
  },
  have x_in_p : r ^ c.snd * s ^ c.fst ∈ ↑p,
  {
    exact set.mem_of_mem_of_subset x_in_my_set p_H,
  },
  rw mul_assoc,
  exact p.smul (f c.fst) x_in_p,
end

open set

variable {α : Type u}
example {x : α} (A B : set α) (H : A ⊆ B)(hx : x ∈ A) : x ∈ B :=
begin
  exact H hx,
end



lemma fundamental_theorem_integrally_closedness (R : Type u) (A : Type v) [integral_domain R] 
[comm_ring A] [algebra R A] (H : fraction_map R A):
  is_integrally_closed R ↔ is_integrally_closed_in R A :=
begin
  split,
  rw equiv_johan_absolute,
  intro H,
  sorry,
  sorry,
end






-- class dedekind_domain (α : Type*) extends integral_domain α :=
-- (noetherian : is_noetherian_ring α)
-- (factors_prod : ∀{a : α}, a ≠ 0 → (factors a).prod ~ᵤ a)
-- (prime_factors : ∀{a : α}, a ≠ 0 → ∀x∈factors a, prime x)
