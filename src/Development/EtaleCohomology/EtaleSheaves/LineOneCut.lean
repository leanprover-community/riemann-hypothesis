module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineOneCut

abbrev fib {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Scheme.{0} :=
  pullback p (cpt A)

def fibMap {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fib (ι ≫ p) ⟶ fib p :=
  pullback.map (ι ≫ p) (cpt A) p (cpt A) ι (𝟙 _) (𝟙 _) (by simp) (by simp)

def Charts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p →
  ∃ (U V : Scheme.{0}) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ ∧ IsOpenImmersion ι₂ ∧ IsAffine U ∧ IsAffine V ∧
    Set.range ι₁ ∪ Set.range ι₂ = Set.univ

def FibCover : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A))
  (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  IsOpenImmersion (fibMap p ι₁) ∧ IsOpenImmersion (fibMap p ι₂) ∧ Set.range (fibMap p ι₁) ∪ Set.range (fibMap p ι₂) = Set.univ

def ChartAcyc : Prop := Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] {Z U : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z), IsOpenImmersion ι → IsAffine U → AICSch Z → IsUnit (q : A) →
  Acyc q (sch.obj (fib (ι ≫ p)))

def ChartSurj : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  ∀ w : Ht q (sch.obj (pullback (fibMap p ι₁) (fibMap p ι₂))) 0 i, ∃ a b,
    w = pull _ (sch.map (pullback.fst (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 a -
      pull _ (sch.map (pullback.snd (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 b

end LateralTheory.E.LineOneCut
