module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetry
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

theorem _root_.GlobalTheory.T.points_integral_conjugation_symmetry : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (B B' : HermLine ι), IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ' (star w) = star (Ψ w)) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → B.a = 0 → IsSmoothHerm B → B'.a = 0 → IsSmoothHerm B' → (∀ z ∈ mcPts P, B'.h (star z) = B.h z) → IsGoodProj P Ψ' ∧ ptsIntegralAt P Ψ' (pot L) (logNorm B' 1) = ptsIntegralAt P Ψ (pot L) (logNorm B 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegralAt_conj | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegralAt_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegralAt_conj <;> assumption)
