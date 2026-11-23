module

public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.WeightNormalizerAndExponentsOfWeightSum
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop

theorem _root_.GlobalTheory.T.nnW_eq_pow_mul_and_c2_cHalf_le_of_weight_sum : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (wL wF w : WeightFamilies.Wt D j) (k : ℕ), (∀ τ i, w.aP τ i = wF.aP τ i + k * wL.aP τ i) → (∀ τ i, w.aM τ i = wF.aM τ i + k * wL.aM τ i) → nnW B hinj EX w = nnW B hinj EX wL ^ k * nnW B hinj EX wF ∧ c2 D w ≤ k * c2 D wL + c2 D wF ∧ Formalism.MainNotions.DIV.Cons.cHalf w ≤ k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF := by
  first | exact @GlobalTheory.PlaceScalar.weight_normalizer_and_exponents_of_weight_sum | exact GlobalTheory.PlaceScalar.weight_normalizer_and_exponents_of_weight_sum | (intros; apply GlobalTheory.PlaceScalar.weight_normalizer_and_exponents_of_weight_sum <;> assumption)
