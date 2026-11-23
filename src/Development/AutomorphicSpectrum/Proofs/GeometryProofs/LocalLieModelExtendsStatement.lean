module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalLieModelExtends
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric


theorem _root_.GlobalTheory.T.local_lie_model_extends : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F) (_ : Module R F) (MR : LieModel G x F) (e : J → F), p.1 ∈ x.opensRange ∧ x.opensRange ≤ N ∧ ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 → ∀ (i : J) (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G), v.left = spMap (dualMap ψ) ≫ (MR.pt (e i)).left → M.Extends q (c i) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections | exact GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections <;> assumption)
