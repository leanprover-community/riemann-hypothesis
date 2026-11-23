module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormCorrectionOfVanishingAfterBaseChange
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_form_correction_of_vanishing_after_baseChange : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (H₀ : LB X₀) (w₀ : LB.Iso H₀ (H.pull π)) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → w₀.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (π) z ∈ (H).U k → z ∈ (H₀).U k' → gs (π) z _ ((s j).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → ∀ t : ℕ, FirstCohomologyVanishes (pw H₀ t) → (∀ σ : LB.Sec (pw H₀ t), ∃ P : MvPolynomial (Fin (n + 1)) K, P.IsHomogeneous t ∧ ∀ k : H₀.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f₀) ((H₀).U k)) (fun j => (s₀ j).f k) (P)) → ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (H' : LB X') (w : LB.Iso H' (H.pull β)) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (β) z ∈ (H).U k → z ∈ (H').U k' → gs (β) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → ∀ F : MvPolynomial (Fin (n + 1)) A, F.IsHomogeneous t → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (β ≫ f) ((H').U k)) (fun j => (s' j).f k) (F) = 0) → ∃ G : MvPolynomial (Fin (n + 1)) A, G.IsHomogeneous t ∧ (∀ d, g (AddMonoidAlgebra.coeff G d) = 0) ∧ (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F - G) = 0) := by
  first | exact @GlobalTheory.FormCorr.exists_form_correction | exact GlobalTheory.FormCorr.exists_form_correction | (intros; apply GlobalTheory.FormCorr.exists_form_correction <;> assumption)
