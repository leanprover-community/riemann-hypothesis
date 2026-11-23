module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReductionClosedSubschemeIffIdealEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem GlobalTheory.FormalAlg.alg_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), Alg f I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ j : ∀ e, (Y e).left ⟶ W, (∀ e, IsClosedImmersion (j e)) → (∀ e, j e ≫ f = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ j (e + 1) = j e) → ∃ (T : Scheme.{0}) (i : T ⟶ W) (c : ∀ e, (Y e).left ⟶ T), IsClosedImmersion i ∧ IsProper (i ≫ f) ∧ (∀ e, c e ≫ i = j e) ∧ ∀ e, IsPullback (c e) (Y e).hom (i ≫ f) (thick R I e) := by
  intro R _ I W f hA Y β hβ hY j hj hjf hβj
  have hP := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1
  have key : ∀ e (T : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
      ((∃ b : (Y e).left ⟶ T, b ≫ i = j e ∧ IsPullback b (Y e).hom (i ≫ f) (thick R I e)) ↔
        i.ker ⊔ baseIdeal f (I ^ (e + 1)) = (j e).ker) :=
    fun e T i hi => GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W T (Y e).left f i (j e) (Y e).hom hi (hj e) (hjf e)
  have hsys : IsSystem f I (fun e => (j e).ker) := by
    intro e
    exact ((key e _ (j (e + 1)) (hj (e + 1))).1 ⟨β e, hβj e, by rw [hjf (e + 1)]; exact hP e⟩).symm
  have hprop : ∀ e, IsProper ((j e).ker.subschemeι ≫ f) := by
    intro e
    have h0 : (j e).toImage ≫ ((j e).ker.subschemeι ≫ f) = (Y e).hom ≫ thick R I e := by
      rw [← hjf e, ← Category.assoc]
      exact congrArg (· ≫ f) (Scheme.Hom.toImage_imageι (j e))
    have h1 : (j e).ker.subschemeι ≫ f = inv (j e).toImage ≫ (Y e).hom ≫ thick R I e := by
      rw [← h0, IsIso.inv_hom_id_assoc]
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [h1]
    infer_instance
  obtain ⟨T, hTp, hTr⟩ := hA _ hsys hprop
  have hc : ∀ e, ∃ b : (Y e).left ⟶ T.subscheme, b ≫ T.subschemeι = j e ∧
      IsPullback b (Y e).hom (T.subschemeι ≫ f) (thick R I e) := fun e =>
    (key e _ T.subschemeι inferInstance).2 (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hTr e)
  choose c hc1 hc2 using hc
  exact ⟨T.subscheme, T.subschemeι, c, inferInstance, hTp, hc1, hc2⟩
