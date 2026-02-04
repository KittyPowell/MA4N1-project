import Mathlib

set_option linter.style.commandStart false
set_option linter.unusedTactic false

-- this project follows the layout of Niven's proof of irrationality of pi
-- the work has been labelled to describe how it corresponds to his proof
-- the final contradiction assumes pi = a/b so
-- one is sometimes used to refer to the other throughout

open Polynomial
--defining f(x) as given in Niven's proof
noncomputable def f (n : ℕ) (a : ℚ) (b : ℚ) : Polynomial ℚ :=
  (C (1 / (n.factorial : ℚ))) * (X^n * (C a - C b * X)^n)

--defining n!f(x) for later use
noncomputable def nfact_f (n : ℕ) (a b : ℚ) : Polynomial ℚ := C (n.factorial : ℚ) * f n a b

-- proving n!f(x) has integral coefficients
-- this is done in 2 ways to acccount for potential future use
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

--defining F(x) as given in Niven's proof
noncomputable def F (n : ℕ) (a b : ℤ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n+1), (C (-1 : ℚ))^k * (derivative^[2*k] (f n a b))

-- showing f(0)=0
lemma eval_f_at_zero_is_0 (n : ℕ) (a b : ℚ) (h : n ≠ 0): (f n a b).eval 0 = 0 := by
  simp [f, h]
  done

-- showing f(a/b - x)= f(x)
-- this is done in 3 ways to account for potential future uses
lemma symmetry_of_f (x : ℚ) (n : ℕ) (a b : ℚ) (hb : b ≠ 0) :
(f n a b).eval x = (f n a b).eval ((a / b) - x) := by
  simp [f]
  constructor
  field_simp
  simp [← mul_assoc, ← mul_pow]
  field_simp
  done

lemma symmetry_of_f_uniform (n : ℕ) (a b : ℚ) (hb : b ≠ 0):
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

-- proving a similar symmetry for the kth derivatives of f
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
      (derivative^[Nat.succ k] (f n a b)) = (C (-1 : ℚ))^k *
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

-- showing f(a/b)=0
lemma eval_f_at_aoverb_is_0 (n : ℕ) (a b : ℚ) (hb : b ≠ 0) (hn : n ≠ 0) :
(f n a b).eval (a / b) = 0 := by
  rw [symmetry_of_f]
  · simp
    exact eval_f_at_zero_is_0 n a b hn
  exact hb
  done

-- the next 4 lemmas show that f and its derivatives take integer values at 0 and pi
lemma f_integral_at_0 (n : ℕ) (a b : ℚ) (hn : n ≠ 0) : ∃ z : ℤ,
(f n a b).eval 0 = (z : ℚ) := by
  use 0
  exact eval_f_at_zero_is_0 n a b hn
  done


lemma f_integral_at_pi (n : ℕ) (a b : ℚ) (hb : b ≠ 0) (hn : n ≠ 0) :
    (f n a b).eval (a / b) = 0 := by
  exact eval_f_at_aoverb_is_0 n a b hb hn


lemma f_derivs_integral_at_zero (n k : ℕ) (a b : ℤ) :
  ∃ z : ℤ, (derivative^[k] (f n a b)).eval 0 = (z : ℚ) := by

  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]

  rw [zero_add]


  rw [f]
  rw [coeff_C_mul]


  let P : Polynomial ℤ := X^n * (C a - C b * X)^n

  have h_map : P.map (algebraMap ℤ ℚ) = X^n * (C (a:ℚ) - C (b:ℚ) * X)^n := by
    simp [P, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_sub]


  rw [← h_map, Polynomial.coeff_map]

  by_cases h_lt : k < n
  · have h_coeff_0 : P.coeff k = 0 := by
      rw [coeff_X_pow_mul']
      simp [h_lt]
    rw [h_coeff_0]
    simp
    use 0
    simp
  · push_neg at h_lt
    use (k.factorial / n.factorial : ℕ) * P.coeff k

    simp
    have h_fact_div : (n.factorial : ℚ) ∣ (k.factorial : ℚ) := by
      refine Nat.cast_dvd_cast ?_
      exact_mod_cast Nat.factorial_dvd_factorial h_lt


    simp [← mul_assoc]
    left
    refine (mul_inv_eq_iff_eq_mul₀ ?_).mpr ?_
    · refine Nat.cast_ne_zero.mpr ?_
      exact Nat.factorial_ne_zero n
    rw [Nat.descFactorial_self]
    norm_cast
    rw [Nat.div_mul_cancel (Nat.factorial_dvd_factorial h_lt)]


lemma f_derivs_integral_at_pi (n k : ℕ) (a b : ℤ) (hb : b ≠ 0) :
∃ z : ℤ, (derivative^[k] (f n a b)).eval (a / b : ℚ) = (z : ℚ) := by
  have hbQ : (b : ℚ) ≠ 0 := by
    exact_mod_cast hb
  rw [symmetry_of_f_derivs n k a b hbQ]
  obtain ⟨z, hz⟩ := f_derivs_integral_at_zero n k a b
  simp [hz]
  use (-1)^k * z
  simp
  done

-- the next 2 lemmas use the above to show F takes integer values at zero and pi

lemma F_zero_integer (n : ℕ) (a b : ℤ) :
  ∃ z : ℤ, (F n a b).eval 0 = z := by
  unfold F
  choose g hg using fun k => f_derivs_integral_at_zero n (2 * k) a b

  use ∑ k ∈ Finset.range (n + 1), (-1)^k * g k
  rw [Polynomial.eval_finset_sum]
  norm_cast

  simp
  apply Finset.sum_congr rfl
  intro k _
  simp
  rw [hg]
  done

lemma F_pi_integer (n : ℕ) (a b : ℤ) (hb : b ≠ 0) :
  ∃ z : ℤ, (F n a b).eval (a / b : ℚ) = z := by
  unfold F

  choose g hg using fun k => f_derivs_integral_at_pi n (2 * k) a b hb

  use ∑ k ∈ Finset.range (n + 1), (-1)^k * g k
  rw [Polynomial.eval_finset_sum]
  simp
  apply Finset.sum_congr rfl
  intro k _
  simp
  exact hg k

  done


-- showing F(0)+F(pi) is an integer
lemma F_zero_plus_F_pi_integer (n : ℕ) (a b : ℤ) (hb : b ≠ 0) :
  ∃ z : ℤ, (F n a b).eval 0 + (F n a b).eval (a / b : ℚ) = z := by
  obtain ⟨z1, hz1⟩ := F_zero_integer n a b
  obtain ⟨z2, hz2⟩ := F_pi_integer n a b hb
  use z1 + z2

  rw [hz1, hz2]
  simp

--showing the left-hand of the inequality at the end of Niven's proof
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

-- showing the right-hand side of the inequality at the end of Niven's proof
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

-- defining the integral of f(x)sin(x) given in Niven's proof
noncomputable def definite_integral_f_sin (n : ℕ) (a b : ℚ) : ℝ :=
  ∫ x in 0..Real.pi, (Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x * Real.sin x

-- a partially unfinished lemma to show F'' + F' = f, needed to simplify
--the product rule application to f, F and trig functions given in Niven's proof
lemma F_telescope (a b : ℕ) (n : ℕ) (hn : n > 0)
(ha : a ≥ 0) (hb : b > 0) : (F n a b) + derivative (derivative (F n a b)) = (f n a b) := by
    unfold F
    simp_rw [derivative_sum, derivative_mul]
    rw [sum_range_succ_comm]
    rw [sum_range_succ']
    simp only [pow_zero, one_mul]

    have h_cancel : ∑ k ∈ range n,
    (C (-1 : ℚ) ^ (k + 1) * derivative^[2 * k + 2]
    (f n a b) + C (-1 : ℚ) ^ k * derivative^[2 * k + 2] (f n a b)) = 0 := by
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

-- proving the product rule application to f, F and trig functions given in Niven's proof
lemma F_trig_product_rule (n : ℕ) (a b : ℕ) (hn : n > 0) (ha : a ≥ 0) (hb : b > 0) :
  ∀ x : ℝ, deriv (fun x => (Polynomial.map (algebraMap ℚ ℝ)
  (derivative (F n a b))).eval x * Real.sin x -
  (Polynomial.map (algebraMap ℚ ℝ) (F n a b)).eval x * Real.cos x) x =
  (Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x * Real.sin x := by

  intro x
  let f_R := (f n a b).map (algebraMap ℚ ℝ)
  let F_R := (F n a b).map (algebraMap ℚ ℝ)
  let F'_R := (derivative (F n a b)).map (algebraMap ℚ ℝ)
  let F''_R := (derivative (derivative (F n a b))).map (algebraMap ℚ ℝ)
  have h_sin_diff : DifferentiableAt ℝ Real.sin x := Real.differentiableAt_sin
  have h_cos_diff : DifferentiableAt ℝ Real.cos x := Real.differentiableAt_cos
  have h_poly_diff (P : ℝ[X]) : DifferentiableAt ℝ (fun y => P.eval y) x :=
    P.differentiableAt
  change deriv (fun x => F'_R.eval x * Real.sin x -
  F_R.eval x * Real.cos x) x = f_R.eval x * Real.sin x
  simp [h_sin_diff, h_cos_diff, h_poly_diff]
  have h1 : derivative F_R = F'_R := by
    simp [F_R, F'_R,]
  have h2 : derivative F'_R = F''_R := by
    simp [F'_R, F''_R,]
  rw [h1, h2]
  ring_nf
  have h_factor : eval x F''_R * Real.sin x + Real.sin x * eval x F_R =
  (eval x F''_R + eval x F_R) * Real.sin x := by ring
  rw[h_factor]
  rw [mul_comm (Real.sin x) (eval x f_R)]
  rw [← Polynomial.eval_add, ← Polynomial.map_add]
  have h_total :
  (derivative (derivative (F n a b)) + F n a b).map (algebraMap ℚ ℝ)= (F''_R + F_R) := by
    simp [F''_R, F_R, Polynomial.map_add]
  rw [add_comm (derivative (derivative (F n a b)))]
  rw [F_telescope a b n hn ha hb]

--proving the equation labelled (1) in the linked PDF of Niven's proof
-- about the integral of f(x)sin(x)
lemma f_sin_integral_equals_F_eval_pi_plus_F_eval_0 (n : ℕ)
(a b : ℕ) (hn : n > 0) (ha : a ≥ 0)(hb : b> 0 ) :
  definite_integral_f_sin n (a : ℚ) (b : ℚ) =
  (Polynomial.map (algebraMap ℚ ℝ) (F n a b)).eval Real.pi +
  (Polynomial.map (algebraMap ℚ ℝ) (F n a b)).eval 0 := by
  simp[definite_integral_f_sin]
  simp_rw [Polynomial.aeval_def]
  simp_rw [Polynomial.eval₂_eq_eval_map]
  simp_rw [← F_trig_product_rule n a b hn ha hb]
  rw [intervalIntegral.integral_deriv_eq_sub]
  · simp [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero]
  · intro x _
    fun_prop
  · let g := fun x => eval x (Polynomial.map (algebraMap ℚ ℝ) (f n a b)) * Real.sin x
    have hg : IntervalIntegrable g MeasureTheory.volume 0 Real.pi := by
      apply Continuous.intervalIntegrable
      exact (Polynomial.continuous _).mul Real.continuous_sin
    convert hg using 1
    ext x
    dsimp [g]
    exact (F_trig_product_rule n a b hn ha hb x)


-- Combining the work above into the theorem that pi is irrational
-- partially unfinished
theorem pi_irrational : Irrational Real.pi := by
  rw [irrational_iff_ne_rational]
  intro a_frac b_frac h_frac_pos h_pi_eq
  have : ∃ (a b : ℕ), b ≠ 0 ∧ Real.pi = a / b := by
    use a_frac.natAbs, b_frac.natAbs
    constructor
    · simp
      exact h_frac_pos
    · simp
      rw [← abs_div, ← h_pi_eq, abs_of_nonneg Real.pi_pos.le]

  rcases this with ⟨a, b, hb_ne, h_pi_ab⟩
  have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb_ne)
  have ha_pos : (0 : ℝ) < a := by
    rw [← div_pos_iff_of_pos_right hb_pos, ← h_pi_ab]
    exact Real.pi_pos

  let I := fun n =>
  ∫ x in 0..Real.pi, (Polynomial.map (algebraMap ℚ ℝ) (f n a b)).eval x * Real.sin x

  have I_is_int : ∀ n, ∃ z : ℤ, I n = z := by
    intro n
    simp [I]

    have F0 : ∃ z : ℤ, (F n a b).eval 0 = z := by
      exact F_zero_integer n ↑a ↑b
    have Fpi : ∃ z : ℤ, (F n a b).eval (a / b : ℚ) = z := by
      exact F_pi_integer n (↑a) (↑b) (by exact_mod_cast hb_ne)


    obtain ⟨z1, hz1⟩ := F0
    obtain ⟨z2, hz2⟩ := Fpi
    use z1 + z2
    sorry -- I am unsure why rw [← hz1] fails here.

  have I_pos : ∀ n, 0 < I n := by
    intro n
    simp [I]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ ?_

    · apply Continuous.intervalIntegrable
      apply Continuous.mul
      · rw [f]
        continuity
      · exact Real.continuous_sin

    · intro x hx
      apply mul_pos

      · rw [f]
        simp
        have x_pos : 0 < x := hx.1
        have bx_lt_a : ↑b * x < ↑a := by
          rw [h_pi_ab] at hx
          have h_lt : x < ↑a / ↑b := hx.2
          exact (lt_div_iff₀' hb_pos).mp h_lt
        apply mul_pos
        · apply inv_pos.mpr
          norm_cast
          exact Nat.factorial_pos n
        · apply mul_pos
          · exact pow_pos x_pos n
          · apply pow_pos
            simp
            exact bx_lt_a

      exact Real.sin_pos_of_mem_Ioo hx

    exact Real.pi_pos


  have I_lim : Filter.Tendsto I Filter.atTop (nhds 0) := by

    sorry

  rw [Metric.tendsto_atTop] at I_lim
  specialize I_lim 1 zero_lt_one
  rcases I_lim with ⟨n, hn⟩

  specialize hn n (le_refl n)
  rw [dist_zero_right, Real.norm_eq_abs] at hn

  rw [abs_of_pos (I_pos n)] at hn
  rcases I_is_int n with ⟨z, hz⟩

  simp [hz] at hn I_pos
  norm_cast at hn
  specialize I_pos n
  norm_cast at I_pos

  rw [hz] at I_pos
  norm_cast at I_pos
  linarith
