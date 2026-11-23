module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreValueEqUnitMulLeadingFourierTermStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreIsoTorusExtensionBaseChangeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.trait_lead_value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (κ : ResidueField R →+* ResidueField W) (e : (Over.pullback (spMap (residue W))).obj T.G ≅ (Over.pullback (spMap κ)).obj ((Over.pullback (spMap (residue R))).obj Y.H)), κ.comp (residue R) = (residue W).comp T.φ ∧ IsMonHom e.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ ((Over.pullback (spMap (residue W))).obj T.G).left) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left), p' = p ≫ pullback.fst T.G.hom (spMap (residue W)) → y = p ≫ e.hom.left ≫ pullback.fst ((Over.pullback (spMap (residue R))).obj Y.H).hom (spMap κ) ≫ pullback.fst Y.H.hom (spMap (residue R)) → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  intro R _ _ _ hB D C Y W _ _ _ T
  obtain ⟨κ, e, h1, h2, h3⟩ := GlobalTheory.T.exists_closedFibre_iso_torusExtension_baseChange R hB D C Y W T
  refine ⟨κ, e, h1, h2, fun Z p p' y hp hy k u z J J' hJ hJ' => ?_⟩
  obtain ⟨g, ξ', hg, hξ, hP⟩ := h3 Z p p' y hp hy
  exact GlobalTheory.T.closedFibre_value_eq_unit_mul_leadingFourierTerm R hB D C Y W T Z p' y g ξ' hg hξ hP k u z J J' hJ hJ'
