module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.LieCombBaseChange

variable {R R' : Type} [CommRing R] [CommRing R']

private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (k : B →+* C) : spMap k ≫ spMap g = spMap (k.comp g) := by
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_epsScale (f : R →+* R') (c : R) :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ spMap (epsScaleR c) =
      spMap (epsScaleR (f c)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
  rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [epsScaleR, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, mul_comm]

theorem dualMap_over (f : R →+* R') :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  simp only [epsR, Over.mk_hom]
  rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsScale_over (c : R) : spMap (epsScaleR c) ≫ (epsR R).hom = (epsR R).hom := by
  simp only [epsR, Over.mk_hom]
  rw [spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem prod_left_comp {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (d : T'.left ⟶ T.left)
    (hd : d ≫ T.hom = T'.hom ≫ f) {n : ℕ} (u : Fin n → (T ⟶ G)) (u' : Fin n → (T' ⟶ G'))
    (hu : ∀ i, (u' i).left ≫ φ = d ≫ (u i).left) :
    (List.ofFn u').prod.left ≫ φ = d ≫ (List.ofFn u).prod.left := by
  have hd' : d ≫ T.hom = (Over.mk (T'.hom ≫ f)).hom := by simpa using hd
  have hsq : φ ≫ G.hom = G'.hom ≫ f := h.1.w

  have hone : (1 : T' ⟶ G').left ≫ φ = (1 : Over.mk (T'.hom ≫ f) ⟶ G).left := by
    let x₀ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk ((1 : T' ⟶ G').left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, hsq]
      rw [← Category.assoc, Over.w])
    have hx : x₀ * x₀ = x₀ := by
      apply Over.OverMorphism.ext
      rw [h.2 T' 1 1 x₀ x₀ rfl rfl, _root_.mul_one]
      rfl
    have h1 : x₀ = 1 := by simpa using hx
    rw [← h1]
    rfl

  have key : ∀ (m : ℕ) (u : Fin m → (T ⟶ G)) (u' : Fin m → (T' ⟶ G')),
      (∀ i, (u' i).left ≫ φ = d ≫ (u i).left) →
        (List.ofFn u').prod.left ≫ φ = ((Over.homMk d hd' : Over.mk (T'.hom ≫ f) ⟶ T) ≫ (List.ofFn u).prod).left := by
    intro m
    induction m with
    | zero =>
      intro u u' _
      simp only [List.ofFn_zero, List.prod_nil, MonObj.comp_one, hone]
    | succ m ih =>
      intro u u' hu
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul]
      refine (h.2 T' _ _ _ _ ?_ ?_).symm
      · rw [Over.comp_left]
        exact (hu 0).symm
      · exact (ih _ _ fun i => hu i.succ).symm
  have := key n u u' hu
  rw [Over.comp_left] at this
  exact this

end GlobalTheory.LieCombBaseChange

namespace GlobalTheory

open LieCombBaseChange

theorem lieComb_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap f) φ → ∀ (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) (a : Fin n → R) (v' : Fin n → (epsR R' ⟶ G')) (w' : epsR R' ⟶ G'), (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (v j).left) → IsLieComb a v w → (w'.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ↔ IsLieComb (fun i => f (a i)) v' w') := by
  intro R R' _ _ f G _ G' _ φ h n v w a v' w' hv hc
  obtain ⟨u, hu, rfl⟩ := hc

  have hcomp : ∀ i, (spMap (epsScaleR (f (a i))) ≫ (v' i).left) ≫ φ =
      spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (u i).left := by
    intro i
    rw [Category.assoc, hv i, hu i, ← Category.assoc, ← Category.assoc,
      LieCombBaseChange.dualMap_epsScale]
  have hprod : ∀ u'' : Fin n → (epsR R' ⟶ G'),
      (∀ i, (u'' i).left = spMap (epsScaleR (f (a i))) ≫ (v' i).left) →
        (List.ofFn u'').prod.left ≫ φ =
          spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (List.ofFn u).prod.left := fun u'' hu'' =>
    LieCombBaseChange.prod_left_comp h _ (LieCombBaseChange.dualMap_over f) u u''
      (fun i => by rw [hu'' i]; exact hcomp i)
  constructor
  · intro hw
    let u' : Fin n → (epsR R' ⟶ G') := fun i =>
      Over.homMk (spMap (epsScaleR (f (a i))) ≫ (v' i).left) (by
        rw [Category.assoc, Over.w]
        exact LieCombBaseChange.epsScale_over _)
    refine ⟨u', fun i => rfl, ?_⟩

    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hw, hprod u' fun i => rfl]
    · rw [Over.w w', Over.w]
  · rintro ⟨u'', hu'', rfl⟩
    exact hprod u'' hu''

end GlobalTheory
