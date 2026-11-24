module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.AbsInert

theorem ordL_eq_neg_log {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {y : L}
    (hy : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ))) : ordL y = -WithZero.log (Valued.v y) := by
  unfold ordL
  rw [dite_eq_right hy, WithZero.toAdd_unzero_eq_log]

theorem absEv_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV F v : ℝ) ^ (-(2 * ordL (toCompl h x.1))) := by
  intro F E _ _ _ _ _ σ hσ v w h hw x

  set N : Fv F v := Algebra.norm (Fv F v) x.1 with hNdef
  set z : w.adicCompletion E := toCompl h x.1 with hzdef
  have hN0 : N ≠ 0 := ((x.isUnit.map (Algebra.norm (Fv F v))).ne_zero)
  have hz0 : z ≠ 0 := (x.isUnit.map (toCompl h)).ne_zero

  have key := GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x.1
  have key' := congrArg (toCompl h) key
  rw [map_mul] at key'
  have hl : toCompl h (algebraMap (Fv F v) (Fv F v ⊗[F] E) N) = GlobalTheory.LFun.complMap h N := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [hl] at key'

  let c : w.adicCompletion E →+* w.adicCompletion E :=
    (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp
      (((sigR (Fv F v) σ : Fv F v ⊗[F] E →+* Fv F v ⊗[F] E)).comp (GlobalTheory.LFun.InertChart.complEquiv hw h).symm.toRingHom)
  have he : ∀ t, GlobalTheory.LFun.InertChart.complEquiv hw h t = toCompl h t := fun _ => rfl
  have hs : (GlobalTheory.LFun.InertChart.complEquiv hw h).symm z = x.1 := by
    rw [RingEquiv.symm_apply_eq, he]
  have hcz : c z = toCompl h (sigR (Fv F v) σ x.1) := by
    show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) = _
    rw [hs, he]
  have hc : GlobalTheory.LFun.IsConjAt σ h c := by
    unfold GlobalTheory.LFun.IsConjAt
    intro t
    show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (toCompl h t))) = _
    rw [← he t, RingEquiv.symm_apply_apply, he]

  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv hσ hw hc
  have hvc : Valued.v (toCompl h (sigR (Fv F v) σ x.1)) = Valued.v z := by
    rw [← hcz]
    exact hU.2.1 z

  have he1 : w.asIdeal.ramificationIdx (𝓞 F) = 1 :=
    GlobalTheory.LFun.isUnram_iff.mp (GlobalTheory.LFun.isUnram_of_isInertAt hw) w h
  have hvN : Valued.v N = Valued.v z ^ 2 := by
    have hv := GlobalTheory.LFun.valued_complMap h hN0
    rw [he1, pow_one, key', map_mul, hvc] at hv
    rw [sq]
    exact hv.symm
  have hz' : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
  have hN' : Valued.v N ≠ 0 := (Valuation.ne_zero_iff _).mpr hN0

  rw [GlobalTheory.Doubling.absEv_apply, coe_nnnorm]
  show ‖N‖ = _
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hN',
    hvN, WithZero.log_pow, ordL_eq_neg_log (y := toCompl h x.1) hz']
  have hq : ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) = (qV F v : ℝ) := by simp [qV]
  rw [NNReal.coe_zpow, hq]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.AbsInert

end
