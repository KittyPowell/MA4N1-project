import Mathlib

set_option linter.style.commandStart false
set_option linter.unusedTactic false

open Polynomial

noncomputable def f (n : ℕ) (a : ℚ) (b : ℚ) : Polynomial ℚ :=
  (C (1 / (n.factorial : ℚ))) * (X^n * (C a - C b * X)^n)

noncomputable def nfact_f (n : ℕ) (a b : ℚ) : Polynomial ℚ := C (n.factorial : ℚ) * f n a b

lemma nfact_f_integral (a b n : ℕ) :
  ∃ f : ℤ[X], nfact_f n a b = f.map (algebraMap ℤ ℚ) := by
    unfold nfact_f f
    use X^n * (C (a : ℤ) - C (b : ℤ) * X)^n
    ext
    simp [field]
    done

lemma nfact_f_integral_coeffs (k a b n : ℕ) : ∃ z : ℤ,
  (nfact_f n a b).coeff k = (z : ℚ) := by
    obtain ⟨f, hf⟩ := nfact_f_integral a b n
    rw [hf]
    simp
    done

open BigOperators
open Finset

noncomputable def F (n : ℕ) (a b : ℤ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n + 1), (C (-1 : ℚ))^k * (derivative^[k] (f n a b))

lemma eval_f_at_zero_is_0 (n : ℕ) (a b : ℚ) (h : n ≠ 0): (f n a b).eval 0 = 0 := by
  simp [f, h]
  done

lemma symmetry_of_f (x : ℚ) (n : ℕ) (a b : ℚ) (hb : b ≠ 0) :
(f n a b).eval x = (f n a b).eval ((a / b) - x) := by
  simp [f]
  constructor
  field_simp
  simp [← mul_assoc, ← mul_pow]
  field_simp
  done


lemma symmetry_of_f_derivs (x : ℚ) (n k: ℕ) (a b : ℚ) (hb : b ≠ 0) (hk : k ≤ n) :
(derivative^[k] (f n a b)).eval x =
(-1 : ℚ)^k * (derivative^[k] (f n a b)).eval ((a / b) - x) := by
  sorry

lemma symmetry_of_f_derivs_new (n k: ℕ) (a b : ℚ) (hb : b ≠ 0) :
(derivative^[k] (f n a b)) =
(C (-1 : ℚ))^k * (derivative^[k] (f n a b)).comp ( C (a / b) - X) := by
  induction k with
  | zero => sorry

  | succ n _ =>
    --expose_names
    --rw [← Function.comp_iterate_pred_of_pos, Function.comp_apply]
    --simp
    --rw [h]
    --The above makes some progress
    sorry
  done


lemma eval_f_at_aoverb_is_0 (n : ℕ) (a b : ℚ) (hb : b ≠ 0) (hn : n ≠ 0) :
(f n a b).eval (a / b) = 0 := by
  rw [symmetry_of_f]
  · simp
    exact eval_f_at_zero_is_0 n a b hn
  exact hb
  done

lemma f_integral_at_0 (n : ℕ) (a b : ℚ) (hn : n ≠ 0) : ∃ z : ℤ,
(f n a b).eval 0 = (z : ℚ) := by
  use 0
  exact eval_f_at_zero_is_0 n a b hn
  done

lemma f_integral_at_pi (n : ℕ) (a b : ℚ) (hb : b ≠ 0) (hn : n ≠ 0) : ∃ z : ℤ,
(f n a b).eval (a / b) = 0 := by
  use 0
  exact eval_f_at_aoverb_is_0 n a b hb hn
  done

lemma f_derivs_integral_at_zero (n k : ℕ) (a b : ℤ) (hk : k ≤ n) :
∃ z : ℤ, (derivative^[k] (f n a b)).eval 0 = (z : ℚ) := by
  sorry
  done

lemma f_derivs_integral_at_pi (n k : ℕ) (a b : ℤ) (hb : b ≠ 0) (hk : k ≤ n):
∃ z : ℤ, (derivative^[k] (f n a b)).eval (a / b : ℚ) = (z : ℚ) := by

  have hbQ : (b : ℚ) ≠ 0 := by
    exact_mod_cast hb

  simp [symmetry_of_f_derivs (a / b : ℚ) n k a b hbQ hk]
  obtain ⟨z, hz⟩ := f_derivs_integral_at_zero n k a b hk
  simp [hz]
  use (-1)^k * z
  simp
  done

lemma f_times_sin_greater_than_zero (x : ℝ) (n : ℕ) (a b : ℚ) (hb : b ≠ 0)
(hxl : 0 < x) (hxu : x < Real.pi) :
0 < ((Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x * Real.sin x) := by
  have h1 : 0 < Real.sin x := by
    exact Real.sin_pos_of_pos_of_lt_pi hxl hxu

  have h2 : 0 < (Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x := by
    sorry
  exact mul_pos h2 h1
  done

lemma f_times_sin_less_than_bound (x : ℝ) (n : ℕ) (a b : ℚ)
(hxl : 0 < x) (hxu : x < Real.pi) :
((Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x * Real.sin x)
< (Real.pi ^ n * (a : ℝ) ^ n) / (n.factorial : ℝ) := by

  have h : (Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x <
  (Real.pi^n * a^n) / n.factorial := by
    simp [f]
    field_simp
    have h1 : x^(n + 1) < Real.pi^(n + 1) := by
      induction n with
      | zero =>
        simp
        assumption
      | succ n _ =>
        expose_names
        rw [pow_add]
        have h11 : Real.pi^(n + 1 + 1) = Real.pi^(n + 1) * Real.pi := by
          simp [pow_add]
        simp [h11]
        sorry
        -- find a lemma that says for x,y,a,b suitable, x < y and a < b implies xa < yb
    -- This seems reasonable to prove
    sorry
  obtain := Real.sin_le_one x
  expose_names
  -- The same xa < yb lemma will prove this part as most of the work is done by h_1 and h
  sorry
