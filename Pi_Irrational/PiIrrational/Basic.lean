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
  ∑ k ∈ Finset.range (n+1), (C (-1 : ℚ))^k * (derivative^[2*k] (f n a b))

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

lemma symmetry_of_f_uniform (n : ℕ) (a b : ℚ) (hb : b ≠ 0) (hn: n>0) :
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

  rw [← mul_pow,← mul_pow]
  have h_base : X * (C a - C b * X) = (C (a / b) - X) * (C b * X) := by
    have h_sub : C a - C b * X = C b * (C (a / b) - X) := by
      linear_combination h
    rw [h_sub]
    ring
  rw [h_base]

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

lemma f_derivs_integral_at_zero (n k : ℕ) (a b : ℤ) (hn : n > 0) (hk : k ≤ n) :
  ∃ z : ℤ, (derivative^[k] (f n a b)).eval 0 = (z : ℚ) := by
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
  rw [f]

  rw [coeff_C_mul]


  simp only [zero_add]
  let P := (C (a : ℚ) - C (b : ℚ) * X) ^ n

  rcases lt_or_eq_of_le hk with h_lt | h_eq
  · use 0
    rw [coeff_mul]
    rw [sum_eq_zero]
    · simp
    · intro x hx
      simp only [mem_antidiagonal] at hx
      rw [coeff_X_pow]
      split_ifs with h_i
      · rw [h_i] at hx
        have h_contra : n ≤ k := by
          rw [← hx]
          exact Nat.le_add_right n x.2
        exact (not_le_of_gt h_lt h_contra).elim
      · simp

  · rw [h_eq]
    rw [Nat.descFactorial_self]

    rw [coeff_mul]

    have h_sum : ∑ x ∈ antidiagonal n, (X ^ n).coeff x.1 * P.coeff x.2
                 = (X^n).coeff n * P.coeff 0 := by
      apply sum_eq_single (n, 0)
      · rintro ⟨i, j⟩ h_mem h_ne
        simp only [mem_antidiagonal] at h_mem
        rw [coeff_X_pow]
        split_ifs with h_i
        · subst h_i
          have h_j_zero : j = 0 := by
            exact Nat.left_eq_add.mp (id (Eq.symm h_mem))
          subst h_j_zero
          contradiction
        · exact Rat.zero_mul (P.coeff (i, j).2)
      · simp
    rw [h_sum]
    rw [coeff_X_pow_self, one_mul, coeff_zero_eq_eval_zero]
    simp only [P, eval_pow, eval_sub, eval_mul, eval_C, eval_X, mul_zero, sub_zero]
    use a ^ n
    simp only [nsmul_eq_mul]

    have h_fact_ne_zero : (n.factorial : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

    field_simp [h_fact_ne_zero]
    norm_cast


  done


lemma f_derivs_integral_at_pi (n k : ℕ) (a b : ℤ) (hn : n > 0) (hb : b ≠ 0) (hk : k ≤ n):
∃ z : ℤ, (derivative^[k] (f n a b)).eval (a / b : ℚ) = (z : ℚ) := by

  have hbQ : (b : ℚ) ≠ 0 := by
    exact_mod_cast hb
  rw [symmetry_of_f_derivs n k a b hbQ]
  obtain ⟨z, hz⟩ := f_derivs_integral_at_zero n k a b hn hk
  simp [hz]
  use (-1)^k * z
  simp
  done

lemma f_times_sin_greater_than_zero (x : ℝ) (n : ℕ) (a b : ℚ) (hb : b > 0) (h : Real.pi = a / b)
(hxl : 0 < x) (hxu : x < Real.pi) :
0 < ((Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x * Real.sin x) := by
  have h1 : 0 < Real.sin x := by
    exact Real.sin_pos_of_pos_of_lt_pi hxl hxu

  have h2 : 0 < (Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x := by
    rw [f]
    simp
    apply mul_pos
    · simp
      exact Nat.factorial_pos n
    apply mul_pos
    · exact pow_pos hxl n
    apply pow_pos
    simp

    have h_eq : (a : ℝ) = (b : ℝ) * Real.pi := by
      rw [h]
      field_simp
    rw [h_eq]
    rel [hxu]
  exact mul_pos h2 h1
  done

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

noncomputable def definite_integral_f_sin (n : ℕ) (a b : ℚ) : ℝ :=
  ∫ x in 0..Real.pi, (Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x * Real.sin x

lemma F_telescope (x : ℝ) (n : ℕ) (hn : n ≠ 0) (ha : a ≥ 0) (hb : b > 0) : (F n a b) + derivative (derivative (F n a b)) = (f n a b) := by
    unfold F
    simp_rw [derivative_sum, derivative_mul]
    rw [sum_range_succ_comm] 
    rw [sum_range_succ']    
    simp only [pow_zero, one_mul]
    simp only [add_assoc, add_comm, add_left_comm]
    rw [← sum_add_distrib]  
    have h_cancel : ∑ k ∈ range n, (C (-1 : ℚ) ^ (k + 1) * derivative^[2 * k + 2] (f n a b) + C (-1 : ℚ) ^ k * derivative^[2 * k + 2] (f n a b)) = 0 := by
      apply sum_eq_zero
      intro k _
      rw [← add_mul, pow_succ]
      ring_nf
      simp

    have h_lin : (C (a : ℚ) - C (b : ℚ) * X).degree ≤ 1 := by
          rw [sub_eq_add_neg, neg_mul_eq_neg_mul]
          refine (degree_add_le _ _).trans ?_
          simp only [ degree_neg, degree_mul, degree_X]
          rw [max_le_iff]
          constructor
          · apply le_trans (degree_C_le : (C (a : ℚ)).degree ≤ 0)
            exact (by decide : (0 : WithBot ℕ) ≤ 1)
          · have h_deg : (C (b : ℚ)).degree ≤ 0 := degree_C_le
            convert add_le_add (degree_C_le : (C (b : ℚ)).degree ≤ 0) (le_refl (1 : WithBot ℕ))

    have h_deg_f : natDegree (f n a b) ≤ 2 * n := by
        rw [f]
        refine (natDegree_C_mul_le _ _).trans ?_
        refine natDegree_le_iff_degree_le.mpr ?_
        simp only [degree_mul, degree_pow]
        rw [degree_X]
        rw [two_mul, Nat.cast_add]
        apply add_le_add
        · simp only [nsmul_one, le_refl]
        · calc n • (C (a : ℚ) - C (b : ℚ) * X).degree
            ≤ n • (1 : WithBot ℕ) := nsmul_le_nsmul_right h_lin n
          _ = ↑n := by simp


    have h_high_deriv : derivative^[2 * n + 2] (f n a b) = 0 := by
      ext k
      rw [coeff_zero]
      apply coeff_eq_zero_of_natDegree_lt
      rw[f]
      sorry
      
    sorry

lemma F_trig_product_rule (n : ℕ) (a b : ℤ) :
    ∀ x : ℝ, deriv (fun x => (Polynomial.map (algebraMap ℚ ℝ) (derivative (F n a b))).eval x * Real.sin x - 
                             (Polynomial.map (algebraMap ℚ ℝ) (F n a b)).eval x * Real.cos x) x = 
             (Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x * Real.sin x := by
  intro x
  let f_R := (f n a b).map (algebraMap ℚ ℝ)
  let F_R := (F n a b).map (algebraMap ℚ ℝ)
  let F'_R := (derivative (F n a b)).map (algebraMap ℚ ℝ)
  let F''_R := (derivative (derivative (F n a b))).map (algebraMap ℚ ℝ)
  rw [show (fun x => F'_R.eval x * Real.sin x - F_R.eval x * Real.cos x) = 
           (fun x => F'_R.eval x * Real.sin x) - (fun x => F_R.eval x * Real.cos x) by rfl]
  rw [deriv_sub]
  rw [show (fun x => F'_R.eval x * Real.sin x) = (fun x => F'_R.eval x) * Real.sin by rfl]
  rw [deriv_mul]
  rw [show (fun x => F_R.eval x * Real.cos x) = (fun x => F_R.eval x) * Real.cos by rfl]
  rw [deriv_mul]
  rw [Real.deriv_sin, Real.deriv_cos]
  simp only [eval_map]
  ring_nf
  sorry


lemma f_sin_integral_equals_F_eval_pi_plus_F_eval_0 (n : ℕ) (a b : ℤ)(hb : b> 0 ) :
  definite_integral_f_sin n (a : ℚ) (b : ℚ) =
  (Polynomial.map (algebraMap ℚ ℝ) (F n a b)).eval Real.pi +
  (Polynomial.map (algebraMap ℚ ℝ) (F n a b)).eval 0 := by
  rw[F,f, definite_integral_f_sin]
  simp
  field_simp
  rw [← sum_add_distrib]
  simp_rw [← add_div, ← mul_add]
  sorry

lemma f_sin_integral_equals_F_eval_pi_plus_F_eval_0_1 (n : ℕ) (a b : ℤ)(hb : b> 0 ) :
  definite_integral_f_sin n (a : ℚ) (b : ℚ) =
  (Polynomial.map (algebraMap ℚ ℝ) (F n a b)).eval Real.pi +
  (Polynomial.map (algebraMap ℚ ℝ) (F n a b)).eval 0 := by
  have F_product_rule:

sorry

-- Theorem that pi is irrational
theorem pi_irrational {π : ℝ} (x : ℝ) (n : ℕ)
(a b : ℚ) (hb : b > 0) (hxl : 0 < x) (hxu : x < Real.pi):
Irrational π := by
  rw [irrational_iff_ne_rational]
  by_contra h_rational
  push_neg at h_rational
  sorry
