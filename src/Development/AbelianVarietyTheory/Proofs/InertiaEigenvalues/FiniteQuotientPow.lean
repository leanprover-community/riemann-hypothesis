module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LocalIntegers

theorem finite_quotient_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (n : ℕ) : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n}) := by
  have h : Ideal.span {((l : ℕ) : O) ^ n} =
      (Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}).map (algebraMap ℤ_[l] O) := by
    simp [Ideal.map_span]
  rw [h]
  haveI : Finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}) := by
    rw [← PadicInt.ker_toZModPow]
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact Finite.of_injective _ (RingHom.kerLift_injective (PadicInt.toZModPow (p := l) n))
  haveI : Module.Finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n})
      (O ⧸ (Ideal.span {((l : ℕ) : ℤ_[l]) ^ n}).map (algebraMap ℤ_[l] O)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  exact Module.finite_of_finite (ℤ_[l] ⧸ Ideal.span {((l : ℕ) : ℤ_[l]) ^ n})

theorem isOpen_integers (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    IsOpen (Set.range (algebraMap ↥(OL LL) ↥LL.1)) := by
  have h : Set.range (algebraMap ↥(OL LL) ↥LL.1) =
      (fun x : ↥LL.1 => (x : PadicAlgCl l)) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    rw [Set.mem_preimage, mem_closedBall_zero_iff, ← mem_integralClosure_padicInt_iff]
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage continuous_subtype_val

theorem good_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) ∧ ∀ n : ℕ, Finite (↥(OL LL) ⧸ Ideal.span {((l : ℕ) : ↥(OL LL)) ^ n}) := by
  intro l _ LL
  haveI := LL.2
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := finite_integralClosure_padicInt l ↥LL.1
  haveI : ContinuousSMul ℚ_[l] ↥LL.1 :=
    Topology.IsInducing.continuousSMul (f := id) (g := fun x : ↥LL.1 => (x : PadicAlgCl l))
      Topology.IsInducing.subtypeVal continuous_id rfl
  haveI : IsTopologicalRing ↥LL.1 := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  refine ⟨⟨⟨inferInstance, isDiscreteValuationRing_integralClosure_padicInt l ↥LL.1,
    isFractionRing_integralClosure_padicInt l ↥LL.1⟩, LL.2, isModuleTopologyOfFiniteDimensional,
    inferInstance, isOpen_integers l LL⟩, finite_quotient_pow l _⟩

end GlobalTheory.LocalIntegers
