module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.InertSupp.Unram

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open ValuativeRel Matrix MeasureTheory in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.InertSupp.Unram.valuation_det_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k}
    (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k m) :
    valuation k (GeneralLinearGroup.det g : k) = 1 := by
  unfold _root_.GlobalTheory.SplitWeil.KO at hg
  obtain ⟨h, rfl⟩ := hg
  have hdet : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap (𝒪[k]) k) h) : k)
      = algebraMap (𝒪[k]) k (GeneralLinearGroup.det h : 𝒪[k]) := by
    simp [GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [hdet]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

end GlobalTheory.InertSupp.Unram
