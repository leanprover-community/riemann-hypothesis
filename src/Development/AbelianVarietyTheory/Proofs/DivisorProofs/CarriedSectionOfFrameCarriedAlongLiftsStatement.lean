module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionOfFrameCarriedAlongLifts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.carried_section_of_frame_carried_along_lifts : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X) (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)), φ ≫ f = f → (∀ f' : (pullback f (spMap ρ₁)) ⟶ (pullback f (spMap ρ₁)), f' ≫ (pullback.fst f (spMap ρ₁)) = (pullback.fst f (spMap ρ₁)) ≫ φ → f' ≫ (pullback.snd f (spMap ρ₁)) = (pullback.snd f (spMap ρ₁)) → FrameCarriedAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ φ w f') → ∀ l, SecCarriedOver L O (s l) φ w := by
  first | exact @GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong | exact GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong | (intros; apply GlobalTheory.Mum.secCarriedOver_of_frameCarriedAlong <;> assumption)
