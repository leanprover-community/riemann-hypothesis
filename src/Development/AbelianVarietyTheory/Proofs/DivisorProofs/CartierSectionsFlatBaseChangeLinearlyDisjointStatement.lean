module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierSectionsFlatBaseChangeLinearlyDisjoint
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), ρ.Flat → ∀ (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), QuasiCompact p → QuasiSeparated p → IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (D : CartierDiv X) (D₁ : CartierDiv Y), PPull i φ θ D D₁ → LinDisj (GlobalTheory.Desc.cst p) (GlobalTheory.Desc.cst q) θ ∧ ∀ k : ℕ, {v | ∀ z : V, (k • D₁).RegularAt (i z) v} = spanBy (GlobalTheory.Desc.cst q) (θ '' Sec D k) := by
  first | exact @GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange | exact GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange | (intros; apply GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange <;> assumption)
