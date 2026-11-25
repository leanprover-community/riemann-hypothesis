module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.DiscChar

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {ω χ : HChar E}
  {V : Submodule ℂ (Sm E a)}

structure IsDiscreteWith (ω : HChar E) (V : Submodule ℂ (Sm E a)) : Prop where
  aut : ∀ φ ∈ V, IsAutForm φ
  central : ∀ z : Neutral.B1.Ideles E, ∀ φ ∈ V,
    rt E a (GeneralLinearGroup.scalar (Fin a) z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ
  sqInt : ∀ φ ∈ V, IsSqInt fun g => ((‖φ.1 g‖ : ℝ) : ℂ)
  stable : _root_.GlobalTheory.CuspRep.IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, _root_.GlobalTheory.CuspRep.IsStable W → W = ⊥ ∨ W = V

abbrev expId (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (t : ℝ) : Neutral.B1.Ideles E :=
  infId E (expU fun _ : InfinitePlace E => (t : ℂ))

theorem isSqInt_of_bounded {f : GA E a → ℂ} (h : ∀ t g, f (splitCentre E a t * g) = f g) {C : ℝ}
    (hC : ∀ g, ‖f g‖ ≤ C) : IsSqInt f := by
  have hd := isFundamentalDomain_stdDom (latticeGL E a) (Measure.haar : Measure (GA E a))
  have hf := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a Measure.haar
  refine ⟨h, Measure.haar, _, inferInstance, hd, ?_⟩
  refine (lintegral_mono (g := fun _ => ENNReal.ofReal C ^ 2) fun g => ?_).trans_lt ?_
  · exact pow_le_pow_left' ((ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hC g))) 2
  · rw [setLIntegral_const, ← quotMeasure_univ hd]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top _ _)

section Local

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

end GlobalTheory.DiscChar

namespace GlobalTheory.Published

open GlobalTheory.DiscChar

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

end GlobalTheory.Published

end
