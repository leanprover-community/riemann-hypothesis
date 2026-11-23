module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyHomOfGraphsOverRingInvertingElement
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

theorem _root_.GlobalTheory.T.exists_familyHom_of_graphs_over_ring_inverting_element : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → φ ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ φ) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} → ∀ (K₀ : Type) [Field K₀] (x₀ : R →+* K₀) φ₀, G K₀ x₀ φ₀ → ∃ f : R, x₀ f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Y : Scheme.{0}) (π : Y ⟶ Z₁.left) (sY : Y ⟶ Sp R'), π ≫ Z₁.hom = sY ≫ spMap ρ → ∃ F : Y ⟶ Z₂.left, F ≫ Z₂.hom = sY ≫ spMap ρ ∧ ∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → ∀ io : pullback Z₁.hom (spMap x) ⟶ Y, io ≫ π = pullback.fst _ _ → φ = io ≫ F := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit | exact GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit | (intros; apply GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit <;> assumption)
