module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChange
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_affine_nonzeroLocus_flat_local_baseChange : (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (M₀ : LB G.left), M₀.IsLB → ∀ s₀ : M₀.Sec, IsAffineOpen (nonzeroLocus s₀) → (∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ (R' : Type) (_ : CommRing R') (ρ : R →+* R'), ρ.Flat ∧ ∃ x' : ↥(pullback G.hom (spMap ρ)), pullback.fst G.hom (spMap ρ) x' = y ∧ ∃ n, 1 ≤ n ∧ ∃ s : (lbPow (M₀.pull (pullback.fst G.hom (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  first | exact @GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square | exact GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square | (intros; apply GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square <;> assumption)
