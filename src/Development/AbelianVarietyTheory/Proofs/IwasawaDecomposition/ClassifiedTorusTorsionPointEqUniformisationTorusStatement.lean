module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassifiedTorusTorsionPointEqUniformisationTorus
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

theorem _root_.GlobalTheory.T.classified_torusTorsionPoint_eq_uniformisationTorus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), FormalEq P.U.toUnifPre x₀ g₀ → ∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) (τ : Multiplicative P.D.toPre.X →* A'ˣ) (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → ∀ (g : GtPt P.D.toPre (Over.mk (spMap (f.comp a)))), (∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ)))) → ∀ (h : Over.mk (spMap (f.comp a)) ⟶ N), GtPt.IsPull h.left g₀ g → h.left ≫ x₀.left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ := by
  first | exact @GlobalTheory.TorusTorsionPoint.eq_torus_of_classify | exact GlobalTheory.TorusTorsionPoint.eq_torus_of_classify | (intros; apply GlobalTheory.TorusTorsionPoint.eq_torus_of_classify <;> assumption)
