module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CombinedBoundAtTrivialValuationsOfCharts
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsEveryFinitePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralityTrivialValuationsOfNormalAffineChartsStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NoCommonZeroOfFiniteValuesStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TransferLawOfNormalCharts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem transfer_of_models : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → (∀ la, ModelAt Xo c la) → (∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.regular₂ Xo c U) ∧ ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ Formalism.L2.PjFree.RegularityR2Quotient Xo c C := by
  intro hS E _ _ _ H Dw l Xo c hEv hInt hM
  have hN := fun la => GlobalTheory.T.exists_normalCharts_everyFinitePlace hS E H Dw l Xo c hEv hInt la (hM la)
  refine ⟨GlobalTheory.Reg.Transfer.transferLaw_of_normalCharts E H Dw l Xo c hN, fun C hC => ⟨?_, ?_⟩⟩
  · exact (GlobalTheory.T.integrality_trivialValuations_of_normalAffineCharts E H Dw l Xo c hN C hC).1
  · exact combined_bound_at_trivial_valuations_of_charts E H Dw l Xo c hN
      (fun la a n m ws hws hv => GlobalTheory.T.noCommonZero_of_exists_finite_value hS E H Dw l Xo c hEv la (hM la) a n m ws hws hv) C hC

end GlobalTheory.Reg
