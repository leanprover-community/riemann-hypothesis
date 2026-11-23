module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.condEx :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ ψ : AddChar E Circle, Continuous ψ → ψ ≠ 1 → ∃ d : ℤ, HasConductor ψ (ϖ ^ d) := by
  intro E _ _ _ _ ϖ hϖ ψ hψ hψ1
  obtain ⟨c, hc⟩ := DiscreteGroups.sglob.DzType.exists_hasConductor_of_continuous_ne_one ψ hψ hψ1
  have h1 : ord E ϖ = 1 := ord_eq_one (k := E) hϖ
  have hz : ∀ d : ℤ, ord E (ϖ ^ d) = d := by
    intro d
    cases d with
    | ofNat n => simp [DiscreteGroups.sglob.DzType.ord_pow_bis, h1]
    | negSucc n =>
      rw [zpow_negSucc, DiscreteGroups.sglob.DzType.ord_inv_eq_neg_ord, DiscreteGroups.sglob.DzType.ord_pow_bis, h1, Int.negSucc_eq]
      push_cast; ring
  have hv : valuation E ((ϖ ^ ord E c : Eˣ) : E) = valuation E (c : E) :=
    le_antisymm ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))
      ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))
  refine ⟨ord E c, fun x => ?_⟩
  rw [hv]
  exact hc x
