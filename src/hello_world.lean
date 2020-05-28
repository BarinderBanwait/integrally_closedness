import ring_theory.noetherian
import ring_theory.integral_closure
import ring_theory.adjoin
import ring_theory.algebra
import linear_algebra.basic

universes u v

variables (R : Type u) {A : Type v}
variables [comm_ring R] [comm_ring A]
variables [algebra R A]
variables i : ℕ
variables (K : Type*)
open ideal
open function
open_locale big_operators

structure is_integrally_closed_in (R : Type u) (A : Type v) [comm_ring R] [comm_ring A] 
[algebra R A] : Prop := 
(inj : injective (algebra_map R A))
(closed : ∀ (a : A), is_integral R a → ∃  r : R, algebra_map R A r = a)

def my_set (R) [integral_domain R] (r : R) (s : R) (n : ℕ) := 
{ x | ∃ (i:ℕ ) (h : 0≤ i) (h2 :i≤ n-1), x = r^(n-1-i) *s^(i+1) }

def is_integrally_closed (R) [integral_domain R] : Prop :=
∀ (r : R) (s : R), (s ≠ 0) ∧ (∃ n : ℕ , 
r^n ∈ span (my_set R r s n)) → s ∣ r

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
  rw ideal.span,
  sorry,
  sorry,
  
end

lemma fundamental_theorem_integrally_closedness (R : Type u) (A : Type v) [integral_domain R] 
[comm_ring A] [algebra R A] (H : fraction_map R A):
  is_integrally_closed R ↔ is_integrally_closed_in R A :=
begin
  sorry,
end






-- class dedekind_domain (α : Type*) extends integral_domain α :=
-- (noetherian : is_noetherian_ring α)
-- (factors_prod : ∀{a : α}, a ≠ 0 → (factors a).prod ~ᵤ a)
-- (prime_factors : ∀{a : α}, a ≠ 0 → ∀x∈factors a, prime x)
