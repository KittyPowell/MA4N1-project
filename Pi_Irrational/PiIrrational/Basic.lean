import Mathlib

set_option linter.style.commandStart false

open Polynomial

noncomputable def f (n : ℕ) (a : ℤ) (b : ℤ) : Polynomial ℚ :=
  (C (1 / (n.factorial : ℚ))) * (X^n * (C (a : ℚ) - C (b : ℚ) * X)^n)

noncomputable def nfact_f (n : ℕ) (a b : ℤ) : Polynomial ℚ := C (n.factorial : ℚ) * f n a b

lemma nfact_f_integral_coeffs (n: ℕ) (a b : ℤ) :
  ∃ pz : Polynomial ℤ, map (Int.castRingHom ℚ) pz = nfact_f n a b := by
  use X^n * (C a - C b * X)^n
  simp [eq_intCast]
  rw [nfact_f, f]

  have fact_cancel : C (n.factorial : ℚ) * C (1 / n.factorial : ℚ) = 1 := by
    rw [map_mul_eq_one C]
    field

  rw [← mul_assoc, fact_cancel]
  simp [one_mul]


open BigOperators
open Finset

noncomputable def F (n : ℕ) (a b : ℤ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n + 1), (C (-1 : ℚ))^k * (derivative^[k] (f n a b))

lemma eval_f_at_zero_is_0 (h : n ≠ 0): (f n a b).eval 0 = 0 := by
  simp [f, h]

lemma f_derivs_integral_at_zero : ∀ k ∈ Finset.range (n + 1), ∃ z : ℤ,
(derivative^[k] (f n a b)).eval 0 = (z : ℚ) := by
sorry
