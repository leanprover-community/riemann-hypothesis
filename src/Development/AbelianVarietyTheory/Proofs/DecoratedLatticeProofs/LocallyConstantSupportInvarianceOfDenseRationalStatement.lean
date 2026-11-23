module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyConstantSupportInvarianceOfDenseRational
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.HermitianLattices.StatementJac
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.locallyConstant_support_invariance_of_dense_rational : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (E : Type) [Field E] (ι : E →+* k), DenseRange ι →
  ∀ (A B : Type) [Fintype A] [Fintype B] (f : Matrix A B k → (A → k) → ℂ), IsLocallyConstant (fun p : Matrix A B k × (A → k) => f p.1 p.2) →
  ∀ (c : kˣ), (∀ (x : Matrix A B E) (y : A → E), f (x.map ι) (fun a => ι (y a)) ≠ 0 → (fun a => ι (y a)) ∈ box A c⁻¹) →
    (∀ (x : Matrix A B E) (y z : A → E), (fun a => ι (z a)) ∈ box A c → f (x.map ι) (fun a => ι (y a + z a)) = f (x.map ι) (fun a => ι (y a))) →
    ∀ x y, (f x y ≠ 0 → y ∈ box A c⁻¹) ∧ ∀ z ∈ box A c, f x (y + z) = f x y := by
  first | exact @GlobalTheory.DenseBox.support_invariance_of_dense | exact GlobalTheory.DenseBox.support_invariance_of_dense | (intros; apply GlobalTheory.DenseBox.support_invariance_of_dense <;> assumption)
