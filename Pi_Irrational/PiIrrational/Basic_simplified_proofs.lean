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


lemma symmetry_of_f_uniform (n : ℕ) (a b : ℚ) (hb : b ≠ 0)(hn: n>0) :
(f n a b) = (f n a b).comp (C (a / b) - X) := by
  rw [f]
  simp
  left
  have h :
    C a - C b * (C (a / b) - X) = C b * X := by
    ring_nf
    simp [← mul_assoc]
    simp[←mul_comm]
    rw[mul_comm]
    rw[mul_assoc]
    rw [← Polynomial.C_mul]
    simp [hb]
  simp[h]
  -- this is extremely trivial but lean will not prove it
  rw [← mul_pow,← mul_pow]
  sorry

lemma symmetry_of_f_poly (n : ℕ) (a b : ℚ) (hb : b ≠ 0) :
f n a b = (f n a b).comp (C (a / b) - X) := by
  apply Polynomial.funext
  intro x
  simpa [Polynomial.eval_comp, sub_eq_add_neg,
  add_comm, add_left_comm, add_assoc] using
  (symmetry_of_f x n a b hb)

lemma symmetry_of_f_derivs (n k : ℕ) (a b : ℚ) (hb : b ≠ 0) :
(derivative^[k] (f n a b)) = (C (-1 : ℚ))^k * (derivative^[k] (f n a b)).comp (C (a / b) - X) := by
  classical
  let q : Polynomial ℚ := C (a / b) - X
  have hqder : q.derivative = C (-1 : ℚ) := by
    simp [q]

  have derivative_negOne_pow : ∀ m : ℕ, derivative ((-1 : Polynomial ℚ) ^ m) = 0 := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m hm =>
        rw [pow_succ]
        rw [derivative_mul]
        simp [hm]

  induction k with
  | zero =>
      simpa [q] using (symmetry_of_f_poly n a b hb)

  | succ k ih =>
      have ih' := congrArg (fun p : Polynomial ℚ => p.derivative) ih

      have hconst' : derivative ((-1 : Polynomial ℚ) ^ k) = 0 := by
        exact derivative_negOne_pow k

      have ih_simplified :
          (derivative^[Nat.succ k] (f n a b))
            =
          (C (-1 : ℚ))^k *
            ((derivative^[Nat.succ k] (f n a b)).comp q) * (C (-1 : ℚ)) := by
        simpa [Function.iterate_succ_apply', q, hqder,
              derivative_mul, derivative_comp, hconst',
              mul_assoc, mul_left_comm, mul_comm] using ih'

      calc
        (derivative^[Nat.succ k] (f n a b))
            =
          (C (-1 : ℚ))^k *
            ((derivative^[Nat.succ k] (f n a b)).comp q) * (C (-1 : ℚ)) := ih_simplified
        _ =
          (C (-1 : ℚ))^(Nat.succ k) *
            ((derivative^[Nat.succ k] (f n a b)).comp q) := by
          simp [pow_succ, mul_comm]


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
  rw [symmetry_of_f_derivs n k a b hbQ]
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
    rw [f]
    simp
    sorry
  exact mul_pos h2 h1
  done
-- In the following we assume pi = a/b when we say x < a/b
lemma f_times_sin_less_than_bound (x : ℝ) (n : ℕ) (a b : ℚ)
(hxl : 0 < x) (hxu : x < Real.pi) (hn : n ≠ 0) (ha : a ≥ 0) (hb : b > 0) (h : Real.pi = a / b):
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
        refine pow_lt_pow_left₀ hxu ?_ ?_
        · exact Std.le_of_lt hxl
        exact Ne.symm (Nat.zero_ne_add_one (n + 1))
    refine mul_lt_mul_of_pos_of_nonneg' ?_ ?_ ?_ ?_
    · refine pow_lt_pow_left₀ hxu ?_ hn
      exact Std.le_of_lt hxl
    · refine (pow_le_pow_iff_left₀ ?_ ?_ hn).mpr ?_
      · simp
        have h_eq : (a : ℝ) = (b : ℝ) * Real.pi := by
          rw [h]
          field_simp
        rw [h_eq]
        have h_ineq : ↑b * x < ↑b * Real.pi := by
          rel [hxu]
        exact Std.le_of_lt h_ineq
      · exact Rat.cast_nonneg.mpr ha
      simp
      apply mul_nonneg
      · positivity
      positivity


    · refine pow_pos ?_ n
      simp
      have h_eq : ↑a = ↑b * Real.pi := by
        rw [h]
        field_simp
      have h_ineq : ↑b * x < ↑b * Real.pi := by
        rel [hxu]
      rw [← h_eq] at h_ineq
      exact h_ineq
    refine pow_nonneg ?_ n
    exact Real.pi_nonneg

  obtain := Real.sin_le_one x
  expose_names

  have h_poly_nonneg : 0 ≤ (Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x := by
    rw [f]
    simp
    apply mul_nonneg
    · simp
    apply mul_nonneg
    · refine pow_nonneg ?_ n
      exact Std.le_of_lt hxl
    apply pow_nonneg
    have h_eq : (a : ℝ) = (b : ℝ) * Real.pi := by
      rw [h_1]
      field_simp
    rw [h_eq]
    simp
    rw [h_1]
    field_simp
    rw [h_eq]
    field_simp
    exact Std.le_of_lt hxu

  have h_sin_pos : 0 < Real.sin x := Real.sin_pos_of_mem_Ioo ⟨hxl, hxu⟩
  have h_prod_le : eval x (Polynomial.map (algebraMap ℚ ℝ) (f n a b)) * Real.sin x
  ≤ eval x (Polynomial.map (algebraMap ℚ ℝ) (f n a b)) := by
    apply mul_le_of_le_one_right h_poly_nonneg h_2

  exact h_prod_le.trans_lt h

  done

-- Defining the definite integral of f(x) * sin(x) from 0 to pi
noncomputable def definite_integral_f_sin (n : ℕ) (a b : ℚ) : ℝ :=
  ∫ x in 0..Real.pi, (Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x * Real.sin x

-- Lemma to show integral above = F(pi) + F(0)
lemma f_sin_integral_equals_F_eval_pi_plus_F_eval_0 (n : ℕ) (a b : ℤ) :
  definite_integral_f_sin n (a : ℚ) (b : ℚ) =
  (Polynomial.map (algebraMap ℚ ℝ) (F n a b)).eval Real.pi +
  (Polynomial.map (algebraMap ℚ ℝ) (F n a b)).eval 0 := by
    sorry
