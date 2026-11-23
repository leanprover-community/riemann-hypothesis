module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStickMap

theorem hasSubst_of_cc {R : Type*} [CommRing R] (a : MvPowerSeries (Fin 3) R)
    (ha : MvPowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a :=
  PowerSeries.HasSubst.of_constantCoeff_zero ha

theorem map_defect {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (f : Fin 3 → R⟦X⟧) (s : R⟦X⟧) :
    MvPowerSeries.map h (GlobalTheory.FrobStick.defect f s)
      = GlobalTheory.FrobStick.defect (fun j => PowerSeries.map h (f j)) (PowerSeries.map h s) := by
  have hs : ∀ (a : MvPowerSeries (Fin 3) R), MvPowerSeries.constantCoeff a = 0 → ∀ g : R⟦X⟧,
      MvPowerSeries.map h (subst a g) = subst (MvPowerSeries.map h a) (PowerSeries.map h g) :=
    fun a ha g => PowerSeries.map_subst (hasSubst_of_cc a ha) g
  unfold GlobalTheory.FrobStick.defect
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_ofNat]
  rw [RingHom.map_det]
  congr 1
  · congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hs _ (by simp) _]
    simp
  · rw [hs _ (by simp), hs _ (by simp), hs _ (by simp), hs _ (by simp)]
    simp [map_add (f := _), map_sub]

end GlobalTheory.FrobStickMap

namespace GlobalTheory.FrobStickMap

noncomputable def tq (F : ℂ → ℂ) : (↥Qbar)⟦X⟧ :=
  PowerSeries.mk (fun n => if h : coef1 F n ∈ Qbar then ⟨_, h⟩ else 0)

theorem map_tq_of_algEnt (F : ℂ → ℂ) (hF : AlgEnt F) :
    PowerSeries.map (algebraMap (↥Qbar) ℂ) (tq F) = GlobalTheory.FrobStick.tay F := by
  ext n
  simp only [tq, GlobalTheory.FrobStick.tay, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rw [dite_eq_left (hF.2 n)]
  rfl

theorem mvmap_injective {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S)
    (hi : Function.Injective h) :
    Function.Injective (MvPowerSeries.map (σ := Fin 3) h) := by
  intro a b hab
  ext n
  apply hi
  have := congrArg (MvPowerSeries.coeff n) hab
  simpa [MvPowerSeries.coeff_map] using this

theorem defect_ser1_eq_zero_of_defect_tay_eq_zero (p : ℕ) [Fact p.Prime] (lam : (↥Qbar) →+* ℂ_[p]) (f : Fin 3 → ℂ → ℂ)
    (s : ℂ → ℂ) (hf : ∀ j, AlgEnt (f j)) (hs : AlgEnt s)
    (h0 : GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (f j)) (GlobalTheory.FrobStick.tay s) = 0) :
    GlobalTheory.FrobStick.defect (fun j => GL3Theta.ser1 lam (f j)) (GL3Theta.ser1 lam s) = 0 := by
  have hq : GlobalTheory.FrobStick.defect (fun j => tq (f j)) (tq s) = 0 := by
    apply mvmap_injective (algebraMap (↥Qbar) ℂ) (FaithfulSMul.algebraMap_injective _ _)
    rw [map_defect, map_zero]
    simp only [map_tq_of_algEnt _ (hf _), map_tq_of_algEnt _ hs]
    exact h0
  have hser : ∀ F : ℂ → ℂ, AlgEnt F → GL3Theta.ser1 lam F = PowerSeries.map lam (tq F) := fun F hF =>
    GlobalTheory.EvenTheta.Param.theta_series_map_coefficients lam F (tq F) (map_tq_of_algEnt F hF).symm
  simp only [hser _ (hf _), hser _ hs]
  rw [← map_defect, hq, map_zero]

end GlobalTheory.FrobStickMap
