module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSpanEigenOfBaseChangeEigen
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


theorem _root_.GlobalTheory.T.mem_span_eigen_of_baseChange_eigen' : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
  (g : S → Module.End ℤ_[l] M) (χ : S → ℤ_[l]), (∀ s, ∀ b ∈ B, g s b ∈ B) →
  ∀ x ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype),
  (∀ s, LinearMap.baseChange (PadicAlgCl l) (g s) x = algebraMap ℤ_[l] (PadicAlgCl l) (χ s) • x) →
  x ∈ Submodule.span (PadicAlgCl l) {y | ∃ b ∈ B, (∀ s, g s b = χ s • b) ∧ y = (1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] b} := by
  first | exact @GlobalTheory.mem_span_eigen_of_baseChange_eigen | exact GlobalTheory.mem_span_eigen_of_baseChange_eigen | (intros; apply GlobalTheory.mem_span_eigen_of_baseChange_eigen <;> assumption)
