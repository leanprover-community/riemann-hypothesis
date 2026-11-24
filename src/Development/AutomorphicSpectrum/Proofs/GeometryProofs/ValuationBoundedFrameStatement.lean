module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationBoundedFrame
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem _root_.GlobalTheory.T.valuation_bounded_frame : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d r : ℕ) (F : Family C p d (𝓞 E)) (χ : 𝓞 E →+* K), (∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits) → (∀ (i : C.I) (a : 𝓞 E), C.v i (χ a) ≤ 1) → ∀ (x₀ : Fin r → (Fin d → K) × (Fin d → K)) (x : ∀ i : C.I, Fin r → (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring)) (N : C.I → Matrix (Fin r) (Fin r) K), IsHBasis F.B x₀ → (∀ i, IsHBasis (F.Bi i) (x i)) → (∀ i j, transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i j)) - ∑ l, N i j l • x₀ l ∈ eigW F.B χ) → (∀ i, (N i).det ≠ 0) ∧ {i | C.v i (N i).det ≠ 1}.Finite ∧ ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (N i).det) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegProd.curve_deg | exact GlobalTheory.CompanionTheory.Ar.Flat.DegProd.curve_deg | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegProd.curve_deg <;> assumption)
