module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralElementsGenericLinearSectionGaussPoint
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

theorem _root_.GlobalTheory.T.integral_elements_generic_linear_section_gauss_point : ∀ (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω] (f : Ω →+* U) (D N : ℕ), Algebra.trdeg K Ω = D → ∀ (v : Valuation U (WithZero (Multiplicative ℤ))) (t : Fin (D + 1) × Fin N → U) (x : Fin N → Ω), (∃ k, x k ≠ 0) → (∀ i : Fin D, ∑ k, t (i.succ, k) * f (x k) = 0) → (∀ p, v (t p) ≤ 1) → (∀ p : MvPolynomial (Fin (D + 1) × Fin N) K, (∀ α, v (f (algebraMap K Ω (p.coeff α))) ≤ 1) → (∃ α, v (f (algebraMap K Ω (p.coeff α))) = 1) → v (MvPolynomial.eval₂ (f.comp (algebraMap K Ω)) t p) = 1) → ∀ g ∈ Subfield.closure (Set.range f ∪ Set.range t), v g ≤ 1 → ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range t), ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range t), v d = 1 ∧ g * d = a := by
  exact @GlobalTheory.GaussSection.integral_elements
