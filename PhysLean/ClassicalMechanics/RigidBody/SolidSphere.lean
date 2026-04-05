/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.ClassicalMechanics.RigidBody.Basic
public import PhysLean.SpaceAndTime.Space.Integrals.IntegralsOnBall

/-!

# The solid sphere as a rigid body

In this module we consider the solid sphere as a rigid body, and compute its mass,
center of mass and inertia tensor.

-/

@[expose] public section

open Manifold
open MeasureTheory
namespace RigidBody
open NNReal

/-- The solid sphere as a rigid body. -/
noncomputable def solidSphere (d : ℕ) (m R : ℝ≥0) : RigidBody d where
  ρ := ⟨⟨fun f => m / volume.real (Metric.closedBall (0 : Space d) R) *
      ∫ x in Metric.closedBall (0 : Space d) R, f x ∂volume,
    by
    intro f g
    simp only [ContMDiffMap.coe_add, Pi.add_apply]
    rw [integral_add]
    ring
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))
    · exact IntegrableOn.integrable
        (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop))⟩, by
      intro r f
      simp only [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [integral_const_mul]
      ring⟩

lemma solidSphere_mass {d : ℕ} (m R : ℝ≥0) (hr : R ≠ 0) : (solidSphere d.succ m R).mass = m := by
  simp only [mass, solidSphere, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffMap.coeFn_mk, integral_const,
    MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, smul_eq_mul, mul_one]
  have h1 : (@volume (Space d.succ) measureSpaceOfInnerProductSpace).real
      (Metric.closedBall 0 R) ≠ 0 := by
    refine (measureReal_ne_zero_iff ?_).mpr ?_
    · apply Space.volume_closedBall_ne_top
    · apply Space.volume_closedBall_ne_zero
      have hr' := R.2
      have hx : R.1 ≠ 0 := by simpa using hr
      apply lt_of_le_of_ne hr' (Ne.symm hx)
  field_simp

/-- The center of mass of a solid sphere located at the origin is `0`. -/
lemma solidSphere_centerOfMass {d : ℕ} (m R : ℝ≥0) : (solidSphere d.succ m R).centerOfMass = 0 := by
  ext i
  simp only [Nat.succ_eq_add_one, centerOfMass, solidSphere, one_div, LinearMap.coe_mk,
    AddHom.coe_mk, ContMDiffMap.coeFn_mk, smul_eq_mul, Space.zero_apply, mul_eq_zero, inv_eq_zero,
    div_eq_zero_iff, coe_eq_zero]
  right
  right
  suffices ∫ x in Metric.closedBall (0 : Space d.succ) R, x i ∂MeasureSpace.volume
    = -∫ x in Metric.closedBall (0 : Space d.succ) R, x i ∂MeasureSpace.volume by linarith
  rw [← integral_neg]
  simp only [← integral_indicator measurableSet_closedBall, Set.indicator, Metric.mem_closedBall,
    dist_zero_right]
  rw [← integral_neg_eq_self]
  norm_num

/-- The moment of inertia tensor of a solid sphere through its center of mass is
  `2/5 m R^2 * I`. -/
@[sorryful]
lemma solidSphere_inertiaTensor (m R : ℝ≥0) (hr : R ≠ 0) :
    (solidSphere 3 m R).inertiaTensor = (2/5 * m.1 * R.1^2) • (1 : Matrix _ _ _) := by
  ext i j
  simp only [inertiaTensor, solidSphere, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffMap.coeFn_mk,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · -- Diagonal case: i = j
    subst hij
    simp only [ite_true, one_mul, mul_one]
    -- Rewrite integrand: ∑_k x_k² - x_i² = ∑_{k ≠ i} x_k²
    have hintegrand : ∀ x : Space 3,
        (∑ k : Fin 3, x.val k ^ 2) - x.val i * x.val i =
        Finset.sum (Finset.erase Finset.univ i) (fun k => x.val k ^ 2) := by
      intro x
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      ring
    simp_rw [hintegrand]
    have hint (k : Fin 3) : IntegrableOn (fun x : Space 3 => x.val k ^ 2)
          (Metric.closedBall (0 : Space 3) ↑R) volume := by
      exact ContinuousOn.integrableOn_compact (isCompact_closedBall 0 ↑R) (by fun_prop)
    rw [integral_finset_sum _ (fun k _ => hint k)]
    -- Each integral equals vol * R² / 5
    have hR_pos : (0 : ℝ) ≤ R := R.2
    simp_rw [Space.integral_coord_sq_space _ ↑R hR_pos]
    have hcard : (Finset.erase Finset.univ i : Finset (Fin 3)).card = 2 := by
      simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
    rw [Finset.sum_const, hcard]
    have hvol_ne : volume.real (Metric.closedBall (0 : Space 3) ↑R) ≠ 0 := by
      refine (measureReal_ne_zero_iff ?_).mpr ?_
      · apply Space.volume_closedBall_ne_top
      · apply Space.volume_closedBall_ne_zero
        exact lt_of_le_of_ne R.2 (Ne.symm (by simpa using hr))
    simp only [nsmul_eq_mul]
    field_simp
    simp [mul_comm]
  · -- Off-diagonal case: i ≠ j
    simp only [hij, ite_false, zero_mul, zero_sub, mul_zero]
    rw [integral_neg, Space.integral_coord_mul_space i j hij]
    simp


end RigidBody
