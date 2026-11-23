module

public import Mathlib.RingTheory.Ideal.Maps
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealDescendingOneDimQuotient
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistApply

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

theorem _root_.GlobalTheory.T.ideal_descending_one_dim_quotient : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Finite A] (χ : A →ₐ[k] k) (e : A) (J : Ideal A), IsIdempotentElem e → χ e = 1 → (∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) → J ≤ Ideal.span {e} → J ≠ ⊥ → ∃ (J₁ : Ideal A) (t : A) (l : A →ₗ[k] k), J₁ < J ∧ t ∈ J ∧ (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) ∧ (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) ∧ (∀ a ∈ J₁, l a = 0) ∧ l t = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one | exact GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one <;> assumption)
