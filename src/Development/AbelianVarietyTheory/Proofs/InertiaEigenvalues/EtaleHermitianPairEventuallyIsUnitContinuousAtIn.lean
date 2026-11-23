module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem units_near_one_inverse_continuousAt (F K : Type) [NontriviallyNormedField F] [CommRing K] [Algebra F K]
    [Module.Finite F K] [TopologicalSpace K] [IsModuleTopology F K] [IsTopologicalRing K] :
    (∀ᶠ a in 𝓝 (1 : K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : K) := by
  classical
  let b := Module.finBasis F K
  let ι : K →ₐ[F] Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F := Algebra.leftMulMatrix b
  have hι : Continuous ι := IsModuleTopology.continuous_of_linearMap ι.toLinearMap
  have hdet : Continuous fun a : K => (ι a).det := (continuous_id.matrix_det).comp hι
  have h1 : (ι 1).det ≠ 0 := by simp
  have hev : ∀ᶠ a in 𝓝 (1 : K), (ι a).det ≠ 0 :=
    hdet.continuousAt.eventually_ne h1
  have hunit : ∀ a : K, (ι a).det ≠ 0 → IsUnit a := by
    intro a ha
    have hn : Algebra.norm F a ≠ 0 := by rw [Algebra.norm_eq_matrix_det b]; exact ha
    rw [Algebra.norm_apply] at hn
    have hu : IsUnit (Algebra.lmul F K a) := by
      rw [LinearMap.isUnit_iff_isUnit_det]; exact hn.isUnit
    obtain ⟨c, hc⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
    exact IsUnit.of_mul_eq_one c (by simpa using hc)
  have hev' : ∀ᶠ a in 𝓝 (1 : K), IsUnit a := hev.mono hunit
  refine ⟨hev', ?_⟩
  let g : K → K := fun a => b.equivFun.symm ((ι a)⁻¹ *ᵥ b.equivFun 1)
  have hinv : ∀ a : K, IsUnit a → (ι a)⁻¹ = ι (Ring.inverse a) := by
    intro a ha
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
  have heq : g =ᶠ[𝓝 (1 : K)] Ring.inverse := by
    filter_upwards [hev'] with a ha
    simp only [g, hinv a ha, Module.Basis.equivFun_apply, ι, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]
  refine ContinuousAt.congr ?_ heq
  have hsymm : Continuous b.equivFun.symm := LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hdet1 : ContinuousAt Ring.inverse (ι 1).det := by
    have : (ι 1).det = 1 := by simp
    rw [this]
    have : (Ring.inverse : F → F) = Inv.inv := funext Ring.inverse_eq_inv
    rw [this]
    exact continuousAt_inv₀ one_ne_zero
  have hmi : ContinuousAt (fun a : K => (ι a)⁻¹) 1 :=
    (continuousAt_matrix_inv (ι 1) hdet1).comp hι.continuousAt
  have hmv : Continuous fun M : Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F => M *ᵥ b.equivFun 1 :=
    continuous_id.matrix_mulVec continuous_const
  exact hsymm.continuousAt.comp (hmv.continuousAt.comp hmi)

theorem et_units_near_one_inverse_continuousAt :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) :=
  fun F _ _ _ _ _ A => units_near_one_inverse_continuousAt F A.K

end GlobalTheory
