module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LaurentCechNerveLevelSpecTensorPower
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DegreeLatticePrimeScaling
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

theorem _root_.GlobalTheory.T.degree_lattice_prime_scaling : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), IsMultiProjPrime (pointIdeal ℤ y) → ∀ (S : Finset Nat.Primes) (b b' : K → ℤ) (s : Ω), s ≠ 0 → (∀ c, segreVec y c ≠ 0 → (∀ t ∈ degLat ℤ y b c, ∃ n : ℕ, ∃ t' ∈ degLat ℤ y b' c, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n * t = s * t') ∧ ∀ t' ∈ degLat ℤ y b' c, ∃ n : ℕ, ∃ t ∈ degLat ℤ y b c, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n * (s * t') = t) → IsHorizontal (pointIdeal ℤ y) → ∃ f g : MRing ι ℤ, (⟨fun _ => b, fun _ => b', fun _ => f, fun _ => g⟩ : LocPair ι ℤ Unit).IsVertOff (pointIdeal ℤ y) S ∧ aeval y f = s * aeval y g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off | exact GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off <;> assumption)
