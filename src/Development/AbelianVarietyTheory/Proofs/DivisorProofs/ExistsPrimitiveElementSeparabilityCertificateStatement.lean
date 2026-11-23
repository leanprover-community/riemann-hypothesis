module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveElementSeparabilityCertificate
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

@[expose] public section


theorem _root_.GlobalTheory.T.exists_primitive_element_separability_certificate : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F), IsTranscendenceBasis k ((↑) : s → F) → Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F → ∀ T : Finset F, ∃ θ : F, IsIntegral (Algebra.adjoin k (s : Set F)) θ ∧ ∃ H : Algebra.adjoin k (s : Set F), H ≠ 0 ∧ ∃ U V : Polynomial (Algebra.adjoin k (s : Set F)), U * minpoly (Algebra.adjoin k (s : Set F)) θ + V * Polynomial.derivative (minpoly (Algebra.adjoin k (s : Set F)) θ) = Polynomial.C H ∧ ∀ x ∈ T, (H : F) * x ∈ Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
  first | exact @GlobalTheory.SepPoint.exists_primitive_sep_certificate | exact GlobalTheory.SepPoint.exists_primitive_sep_certificate | (intros; apply GlobalTheory.SepPoint.exists_primitive_sep_certificate <;> assumption)
