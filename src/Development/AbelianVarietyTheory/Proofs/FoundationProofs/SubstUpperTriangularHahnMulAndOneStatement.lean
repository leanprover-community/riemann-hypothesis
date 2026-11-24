module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstUpperTriangularHahnMulAndOne
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

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

theorem _root_.GlobalTheory.T.substUpperTriangularHahn_mul_and_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d → ∀ φ ψ : HahnSeries ℚ Ω,
  sub ε a b d (φ * ψ) = sub ε a b d φ * sub ε a b d ψ ∧ sub ε a b d 1 = 1 := by
  first | exact @GlobalTheory.CyclotomicQExpansion.sub_mul_and_one | exact GlobalTheory.CyclotomicQExpansion.sub_mul_and_one | (intros; apply GlobalTheory.CyclotomicQExpansion.sub_mul_and_one <;> assumption)
