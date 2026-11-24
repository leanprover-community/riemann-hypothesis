module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayProjectiveFormsThroughPoints
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_away_projective_forms_through_points : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (σ Hh : Type) [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ (∀ e ≥ d, Module.Projective (Localization.Away f) (↥(MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e) ⧸ ((vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).restrictScalars (Localization.Away f)).comap (MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e).subtype)) ∧ ∀ (K : Type) [Field K] (x : (Localization.Away f) →+* K), (vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).map (MvPolynomial.map x) = vanIdeal d (fun h i => x ((algebraMap R (Localization.Away f)) (p h i))) := by
  first | exact @GlobalTheory.ZM.FormsFamily.exists_away_projective_vanIdeal | exact GlobalTheory.ZM.FormsFamily.exists_away_projective_vanIdeal | (intros; apply GlobalTheory.ZM.FormsFamily.exists_away_projective_vanIdeal <;> assumption)
