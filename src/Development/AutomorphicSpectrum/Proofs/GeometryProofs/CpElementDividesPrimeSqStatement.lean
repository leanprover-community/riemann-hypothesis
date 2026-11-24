module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpElementDividesPrimeSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.cp_element_divides_prime_sq : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [IsIntegrallyClosed A] [CharZero Ω] (p : ℕ) [Fact p.Prime] (κ : A), IsCp p (algebraMap A Ω κ) → κ ∣ (p : A) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq | exact GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.KappaDvd.kappa_dvd_sq <;> assumption)
