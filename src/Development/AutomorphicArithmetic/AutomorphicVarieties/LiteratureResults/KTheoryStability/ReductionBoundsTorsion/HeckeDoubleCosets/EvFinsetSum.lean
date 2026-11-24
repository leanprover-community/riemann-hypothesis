module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.MapPartialProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

theorem ev_finset_sum {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (F : (Fin (m + 1) → Y) → ℝ) (y : Y) {ι : Type} (s : Finset ι) (z : ι → Chn G m) :
    ev ρ F y (∑ i ∈ s, z i) = ∑ i ∈ s, ev ρ F y (z i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ev_eq, map_sum]

theorem inv_dC {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (E : (Fin (m + 1) → Y) → ℝ) (hE : Inv ρ E) : Inv ρ (dC E) := by
  intro g y
  simp only [dC]
  exact Finset.sum_congr rfl fun i _ => by rw [hE g (fun j => y (i.succAbove j))]

theorem pEvDC : PEvDC := by
  intro G H Y _ _ _ ρ m E hE y z
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · simp [ev_zero]
  · intro a b ha hb
    rw [ev_add, map_add (f := _), ev_add, ha, hb]
  · intro g a
    have hbd : bd G m (Finsupp.single g a) = a • bd G m (Finsupp.single g 1) := by
      rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hbd, ev_smul, ev_single]
    congr 1
    simp only [bd, Finsupp.linearCombination_single, one_smul]
    rw [ev_add, ev_single, one_mul, ev_finset_sum]
    simp only [ev_smul, ev_single, one_mul]
    simp only [dC]
    rw [Fin.sum_univ_succ]
    congr 1
    · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      have : (fun j : Fin (m + 1) => ρ (Fin.partialProd g j.succ) • y) =
          fun j => ρ (g 0) • (ρ (Fin.partialProd (fun i : Fin m => g i.succ) j) • y) := by
        funext j
        rw [Fin.partialProd_succ', map_mul, mul_smul]
        rfl
      rw [this, hE (g 0)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.partialProd_contractNth]
      simp [Fin.val_succ]

theorem pCob : PCob := by
  intro G _ m F hF hz
  let φ : Chn G (m + 1) →ₗ[ℝ] ℝ :=
    Finsupp.linearCombination ℝ (fun g : Fin (m + 1) → G => F fun j => Fin.partialProd g j)
  have hφ : ∀ z, φ z = ev (MonoidHom.id G) F 1 z := fun z => by
    rw [ev_eq]; simp [φ]
  have hker : LinearMap.ker (bd G m) ≤ LinearMap.ker φ := fun z hz' => by
    rw [LinearMap.mem_ker] at hz' ⊢; rw [hφ]; exact hz z hz'
  let ψ₀ : LinearMap.range (bd G m) →ₗ[ℝ] ℝ :=
    (LinearMap.ker (bd G m)).liftQ φ hker ∘ₗ (bd G m).quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend ψ₀
  have hψbd : ∀ z, ψ (bd G m z) = φ z := fun z => by
    have h1 := LinearMap.congr_fun hψ ⟨bd G m z, LinearMap.mem_range_self _ z⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    simp [ψ₀, LinearMap.quotKerEquivRange_symm_apply_image]
  let E : (Fin (m + 1) → G) → ℝ := fun y =>
    ψ (Finsupp.single (fun j : Fin m => (y j.castSucc)⁻¹ * y j.succ) 1)
  have hEinv : Inv (MonoidHom.id G) E := by
    intro g y
    simp only [E, MonoidHom.id_apply, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hevE : ∀ w : Chn G m, ev (MonoidHom.id G) E 1 w = ψ w := by
    intro w
    refine Finsupp.induction_linear w ?_ ?_ ?_
    · simp [ev_zero]
    · intro a b ha hb; rw [ev_add, ha, hb, map_add (f := _)]
    · intro g a
      rw [ev_single]
      simp only [E, MonoidHom.id_apply, smul_eq_mul, mul_one, Fin.partialProd_right_inv]
      rw [← smul_eq_mul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine ⟨E, hEinv, ?_⟩
  funext y
  set g' : Fin (m + 1) → G := fun i => (y i.castSucc)⁻¹ * y i.succ
  have hy : y = fun j => y 0 * Fin.partialProd g' j := by
    have := Fin.partialProd_left_inv y
    funext j
    exact (congrFun this j).symm
  have h1 : dC E y = dC E (fun j => Fin.partialProd g' j) := by
    conv_lhs => rw [hy]
    exact inv_dC (MonoidHom.id G) E hEinv (y 0) _
  have h2 : F y = F (fun j => Fin.partialProd g' j) := by
    conv_lhs => rw [hy]
    exact hF (y 0) _
  rw [h1, h2]
  have h3 := pEvDC G G G (MonoidHom.id G) m E hEinv 1 (Finsupp.single g' 1)
  rw [ev_single, hevE, hψbd, hφ, ev_single] at h3
  simpa using h3

end PositivityTheory.KB.AffineStabilizerVanishing

end
