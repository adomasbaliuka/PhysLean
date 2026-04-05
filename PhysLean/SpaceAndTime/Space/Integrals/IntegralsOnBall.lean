/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Algebra.Group.Even

public import PhysLean.SpaceAndTime.Space.Module
public import PhysLean.SpaceAndTime.Space.Integrals.Basic


/-!

# Integrals in Space over a ball cenetered at the origin

## i. Overview

In this module we give general properties of integrals over `Space d`.
We focus here on the volume measure, which is the usual measure on `Space d`, i.e.
`dx dy dz`.

## ii. Key results

- `TODO`

-/


@[expose] public section

namespace Space

open InnerProductSpace MeasureTheory

/-- The integral of an odd function over a ball centered at the origin is zero. -/
lemma integral_ball_zero_of_odd {d : ℕ} {R : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space d → E) (hodd : f.Odd) :
    ∫ x in Metric.ball (0 : Space d) R, f x = 0 := by
  by_contra! h_nonzero
  obtain ⟨l, hl⟩ : ∃ l : E →L[ℝ] ℝ, l (∫ x in Metric.ball (0 : Space d) R, f x) ≠ 0 :=
    SeparatingDual.exists_ne_zero' _ h_nonzero
  have h_integral_l : ∫ x in Metric.ball (0 : Space d) R, l (f x) =
      l (∫ x in Metric.ball (0 : Space d) R, f x) := by
    apply_rules [ContinuousLinearMap.integral_comp_comm]
    · exact (Classical.not_not.1 fun h => h_nonzero <| MeasureTheory.integral_undef h)
    · by_contra h_not_complete
      simp_all [MeasureTheory.integral]
  have h_integral_neg : ∫ x in Metric.ball (0 : Space d) R, l (f (-x)) =
      ∫ x in Metric.ball (0 : Space d) R, l (f x) := by
    rw [← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator] <;>
      norm_num [Set.indicator]
    · rw [← MeasureTheory.integral_neg_eq_self]; congr; ext; aesop
    · exact measurableSet_ball
    · exact measurableSet_ball
  simp_all [Function.Odd]
  rw [MeasureTheory.integral_neg] at h_integral_neg; exact hl (by linarith)


/--
The integral of `x i * x j` over a closed ball centered at the origin is zero when `i ≠ j`.
-/
lemma integral_coord_mul_coord_closedBall_eq_zero {d : ℕ} {i j : Fin d}
    (hij : i ≠ j) (R : ℝ) :
    ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
      x i * x j = 0 := by
  -- By symmetry, the integral of $x_i x_j$ over the ball is equal to the integral of $(-x_i) x_j$ over the ball.
  have h_symm : ∫ x : EuclideanSpace ℝ (Fin d) in Metric.closedBall 0 R, x.ofLp i * x.ofLp j
      = ∫ x : EuclideanSpace ℝ (Fin d) in Metric.closedBall 0 R, (-x.ofLp i) * x.ofLp j := by
    -- Let's simplify the integral using the fact that multiplication by a constant out of the integral results in the same integral.
    have h_const : ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, x i * x j = ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, (-x i) * x j := by
      have : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => x - 2 • (x i) • (EuclideanSpace.single i 1)) (MeasureTheory.volume) (MeasureTheory.volume) := by
        have h_linear : ∃ A : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)),
            ∀ x : EuclideanSpace ℝ (Fin d), x - 2 • (x i) • EuclideanSpace.single i 1 = A x := by
          refine ⟨ ?_, ?_ ⟩
          refine { toFun := fun x => x - 2 • x.ofLp i • EuclideanSpace.single i 1, map_add' := ?_, map_smul' := ?_ }
            <;> intros <;> ext <;> norm_num <;> ring_nf!
          exacts [ by split_ifs <;> ring, by split_ifs <;> ring, fun x => rfl ]
        obtain ⟨ A, hA ⟩ := h_linear
        have h_det : A.det = -1 ∨ A.det = 1 := by
          have h_det : A * A = 1 := by
            ext x; simp [ ← hA ]
            split_ifs <;> ring
          exact Or.symm ( eq_or_eq_neg_of_sq_eq_sq _ _
            <| by have := congr_arg LinearMap.det h_det; norm_num at this; linarith )
        have h_det : MeasureTheory.MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => A x)
            MeasureTheory.volume MeasureTheory.volume := by
          refine ⟨?_, ?_⟩
          · exact A.continuous_of_finiteDimensional.measurable
          · ext s hs
            rw [ Measure.map_apply ]
            · cases h_det <;> simp [ *, MeasureTheory.Measure.addHaar_preimage_linearMap ]
            · exact A.continuous_of_finiteDimensional.measurable
            · exact hs
        aesop
      rw [← MeasureTheory.integral_indicator measurableSet_closedBall,
          ← MeasureTheory.integral_indicator measurableSet_closedBall]
      rw [← this.integral_comp ] ; congr ; ext ; simp [Set.indicator]
      ring_nf
      · simp only [EuclideanSpace.norm_eq, PiLp.sub_apply, PiLp.smul_apply,
          EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, smul_ite,
          nsmul_eq_mul, Nat.cast_ofNat, Real.norm_eq_abs, sq_abs, hij.symm, ↓reduceIte,
          add_zero]
        rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ]
        rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ]
        simp only [sub_sq, mul_ite, mul_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.subset_univ, Finset.sum_sdiff_eq_sub, Finset.sum_singleton, Finset.sum_ite_eq',
          Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, not_true_eq_false, and_false,
          add_sub_cancel]
        ring_nf
      · refine' Continuous.measurableEmbedding _ _
        · fun_prop
        · intro x y hxy; ext k; replace hxy := congr_arg ( fun z => z k ) hxy; by_cases hk : k = i <;> simp_all [ two_smul ]
    convert h_const using 1
  norm_num [ MeasureTheory.integral_neg ] at * ; linarith!

/-
The integral of `x i ^ 2` over a closed ball does not depend on `i`.
-/
lemma integral_coord_sq_closedBall_eq {d : ℕ} (i j : Fin d) (R : ℝ) :
    ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
      x i ^ 2 =
    ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
      x j ^ 2 := by
  have h_swap : ∃ g : (EuclideanSpace ℝ (Fin d)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin d)), ∀ x, (g x).ofLp i = x.ofLp j ∧ (g x).ofLp j = x.ofLp i := by
    -- Define the permutation that swaps i and j.
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin d), σ i = j ∧ σ j = i ∧ ∀ k : Fin d, k ≠ i ∧ k ≠ j → σ k = k := by
      exact ⟨ Equiv.swap i j, Equiv.swap_apply_left _ _, Equiv.swap_apply_right _ _, fun k hk => Equiv.swap_apply_of_ne_of_ne hk.1 hk.2 ⟩
    refine' ⟨ _, _ ⟩
    exact LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
    simp [ LinearIsometryEquiv.piLpCongrLeft ]
    grind
  obtain ⟨ g, hg ⟩ := h_swap
  rw [ ← MeasureTheory.integral_indicator ( measurableSet_closedBall ), ← MeasureTheory.integral_indicator ( measurableSet_closedBall ) ]
  have h_swap : MeasureTheory.MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => g x) MeasureTheory.volume MeasureTheory.volume := by
    exact LinearIsometryEquiv.measurePreserving g
  rw [ ← h_swap.integral_comp ]
  · simp [ Set.indicator, hg ]
  · exact g.toHomeomorph.measurableEmbedding

/-
The integral of `x i ^ 2` over a closed ball equals
  `(1/d) * ∫ ‖x‖² = (1/d) * vol * d/(d+2) * R²`
-/
lemma integral_coord_sq_closedBall {d : ℕ} [NeZero d] (i : Fin d) (R : ℝ) (hR : 0 ≤ R) :
    ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
      x i ^ 2 =
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)).toReal * R ^ 2 / (d + 2) := by
  -- Use the formula: ∫_B x_i^2 = (1/d) * ∫_B ‖x‖².
  have h_formula : ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
      x i ^ 2 = (1 / d : ℝ) * ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, ‖x‖^2 := by
    -- The integral of $x_i^2$ over the closed ball is equal to the integral of $\|x\|^2$
    -- over the closed ball divided by $d$ because of symmetry.
    have h_symm : ∑ i : Fin d, ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
        x i ^ 2 = ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, ‖x‖^2 := by
      rw [ ← MeasureTheory.integral_finset_sum ]
      · simp [ EuclideanSpace.norm_eq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ]
      · exact fun i _ => ContinuousOn.integrableOn_compact ( ProperSpace.isCompact_closedBall _ _ ) ( Continuous.continuousOn ( by exact Continuous.pow ( continuous_apply _ |> Continuous.comp <| by continuity ) _ ) )
    rw [ ← h_symm, one_div, inv_mul_eq_div, eq_comm ]
    rw [ Finset.sum_congr rfl fun j _ => integral_coord_sq_closedBall_eq j i R ]
    norm_num [ NeZero.ne ]
  -- For ∫_B ‖x‖², use MeasureTheory.integral_fun_norm_addHaar to convert to a 1D radial integral:
  have h_radial :
      ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
      ‖x‖^2 = (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal * ∫ y in Set.Ioc 0 R, y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) + 1) := by
    have := @MeasureTheory.integral_fun_norm_addHaar
    convert @this ( EuclideanSpace ℝ ( Fin d ) ) _ _ _ ℝ _ _ ?_ MeasureTheory.MeasureSpace.volume _ _ _ ( fun x => if x ≤ R then x ^ 2 else 0 ) using 1
    · rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ]
      exact measurableSet_closedBall
    · rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ]
      cases d <;> norm_num [ pow_succ, mul_assoc ]
      exact Or.inl ( by congr; ext; split_ifs <;> tauto )
    · exact ⟨ 0, EuclideanSpace.single i 1, ne_of_apply_ne ( fun x => x i ) ( by norm_num ) ⟩
  -- Since vol(B(0,R)).toReal = R^d * vol(B(0,1)).toReal, we get:
  have h_volume : (MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R)).toReal = R ^ d * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal := by
    rw [ MeasureTheory.Measure.addHaar_closedBall ] <;> norm_num [ hR ]
  simp_all [ ← intervalIntegral.integral_of_le hR ]
  field_simp
  rw [ div_eq_iff ( NeZero.ne _ ) ] ; ring


@[expose] public section UsingSpace

open NNReal


/-- The volume of a closed ball in `Space 3` equals the volume in `EuclideanSpace`. -/
lemma volume_closedBall_space_eq_euclidean (R : ℝ) :
    volume (Metric.closedBall (0 : Space 3) R) =
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := by
  have h : MeasurePreserving (Space.basis (d := 3).repr)
      (volume : Measure (Space 3))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    LinearIsometryEquiv.measurePreserving Space.basis.repr
  have hpre : Space.basis.repr ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R =
      Metric.closedBall (0 : Space 3) R := by
    rw [show (0 : Space 3) = Space.basis.repr.symm 0 from by simp]
    rw [LinearIsometryEquiv.preimage_closedBall]
  rw [← hpre]
  exact h.measure_preimage measurableSet_closedBall.nullMeasurableSet


-- The volume of a closed ball in `Space d` equals the volume in `EuclideanSpace`. -/
-- lemma volume_closedBall_space_eq_euclidean'
--    {d : ℕ} {x : Space d} {x' : EuclideanSpace ℝ (Fin d)} (R : ℝ) :
--     volume (Metric.closedBall x R) = volume (Metric.closedBall x' R) := by
-- --   have h : MeasurePreserving (Space.basis (d := d).repr)
-- --       (volume : Measure (Space d))
-- --       (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
-- --     LinearIsometryEquiv.measurePreserving Space.basis.repr
--   sorry

/-- The integral of `x i * x j` over a closed ball in `Space 3` is zero when `i ≠ j`. -/
lemma integral_coord_mul_space (i j : Fin 3) (hij : i ≠ j) (R : ℝ) :
    ∫ x in Metric.closedBall (0 : Space 3) R, x.val i * x.val j = 0 := by
  have key : ∀ x : Space 3,
      x.val i * x.val j = (Space.basis.repr x) i * (Space.basis.repr x) j := by
    intro x; simp only [← Space.basis_repr_apply]
  simp_rw [key]
  rw [show (0 : Space 3) = Space.basis.repr.symm 0 from by simp,
      ← LinearIsometryEquiv.preimage_closedBall (Space.basis (d := 3)).repr
        (0 : EuclideanSpace ℝ (Fin 3)) R]
  rw [MeasurePreserving.setIntegral_preimage_emb
    (LinearIsometryEquiv.measurePreserving Space.basis.repr)
    (Space.basis.repr.toHomeomorph.measurableEmbedding)
    (fun y : EuclideanSpace ℝ (Fin 3) => y i * y j)
    (Metric.closedBall 0 R)]
  exact integral_coord_mul_coord_closedBall_eq_zero hij _

/-- The integral of `x i ^ 2` over a closed ball in `Space 3`. -/
lemma integral_coord_sq_space (i : Fin 3) (R : ℝ) (hR : 0 ≤ R) :
    ∫ x in Metric.closedBall (0 : Space 3) R, x.val i ^ 2 =
    volume.real (Metric.closedBall (0 : Space 3) R) * R ^ 2 / 5 := by
  have key : ∀ x : Space 3, x.val i ^ 2 = ((Space.basis.repr x) i) ^ 2 := by
    intro x; simp only [← Space.basis_repr_apply]
  simp_rw [key]
  rw [show (0 : Space 3) = Space.basis.repr.symm 0 from by simp,
      ← LinearIsometryEquiv.preimage_closedBall (Space.basis (d := 3)).repr
        (0 : EuclideanSpace ℝ (Fin 3)) R]
  rw [MeasurePreserving.setIntegral_preimage_emb
    (LinearIsometryEquiv.measurePreserving Space.basis.repr)
    (Space.basis.repr.toHomeomorph.measurableEmbedding)
    (fun y : EuclideanSpace ℝ (Fin 3) => y i ^ 2)
    (Metric.closedBall 0 R)]
  rw [integral_coord_sq_closedBall i R hR]
  simp only [Measure.real]
  rw [show Space.basis.repr ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R =
      Metric.closedBall (0 : Space 3) R from by
    rw [show (0 : Space 3) = Space.basis.repr.symm 0 from by simp]
    exact LinearIsometryEquiv.preimage_closedBall _ _ _]
  rw [volume_closedBall_space_eq_euclidean]
  norm_num
