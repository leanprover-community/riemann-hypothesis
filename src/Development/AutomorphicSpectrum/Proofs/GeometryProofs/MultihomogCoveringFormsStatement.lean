module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogCoveringForms
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

open MvPolynomial

theorem _root_.GlobalTheory.T.multihomog_covering_forms : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) := by
  first | exact @GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line | exact GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line | (intros; apply GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line <;> assumption)
