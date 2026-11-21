import Development.EtaleCohomology.EtaleSheaves.CupUnitChernKummerLaws

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8

def RatModel {k : Type} [Field k] {P : Scheme.{0}} (r : P ⟶ Spec (CommRingCat.of k)) (d : ℕ) : Prop :=
  ∃ (V : P.Opens) (e : V.toScheme ⟶ 𝔸(Fin d; Spec (CommRingCat.of k))), IsOpenImmersion e ∧ Nonempty V ∧
    e ≫ (𝔸(Fin d; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) = V.ι ≫ r

def LeafPointModel : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ d : ℕ,
  ∃ (P : Scheme.{0}) (_ : IsIntegral P) (r : P ⟶ Spec (CommRingCat.of k)) (_ : IsProper r)
    (_ : SmoothOfRelativeDimension d r), RatModel r d ∧
    ∀ (y : Spec (CommRingCat.of k) ⟶ P) (_ : y ≫ r = 𝟙 _) (W : P.Opens), (W : Set P) = (Set.range y)ᶜ →
      ∃ c : Ht q (sch.obj P) (2 * d) d, pull _ (sch.map W.ι) _ _ c = 0 ∧ addOrderOf c = q

def LeafPointTransfer : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
    {P : Scheme.{0}} [IsIntegral P] (r : P ⟶ Spec (CommRingCat.of k)) [IsProper r] [SmoothOfRelativeDimension d r],
  RatModel r d →
  ∃ (x : Spec (CommRingCat.of k) ⟶ X) (_ : x ≫ p = 𝟙 _) (U : X.Opens) (_ : (U : Set X) = (Set.range x)ᶜ)
    (y : Spec (CommRingCat.of k) ⟶ P) (_ : y ≫ r = 𝟙 _) (W : P.Opens) (_ : (W : Set P) = (Set.range y)ᶜ)
    (T : Ht q (sch.obj X) (2 * d) d →+ Ht q (sch.obj P) (2 * d) d),
    ∀ c' : Ht q (sch.obj P) (2 * d) d, pull _ (sch.map W.ι) _ _ c' = 0 →
      ∃ c : Ht q (sch.obj X) (2 * d) d, pull _ (sch.map U.ι) _ _ c = 0 ∧ T c = c'

end LateralTheory.E.E8

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def relF (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) : Hrel R f F n →+ H R E F n :=
  HK.pull R (mappingCone.inr ((chains R).map f)) F n

def LeafRelExact : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (c : H R E F n),
  pull R f F n c = 0 ↔ ∃ e : Hrel R f F n, relF R f F n e = c

def LeafRelTransfer : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
    {P : Scheme.{0}} [IsIntegral P] (r : P ⟶ Spec (CommRingCat.of k)) [IsProper r] [SmoothOfRelativeDimension d r],
  RatModel r d →
  ∃ (x : Spec (CommRingCat.of k) ⟶ X) (_ : x ≫ p = 𝟙 _) (U : X.Opens) (_ : (U : Set X) = (Set.range x)ᶜ)
    (y : Spec (CommRingCat.of k) ⟶ P) (_ : y ≫ r = 𝟙 _) (W : P.Opens) (_ : (W : Set P) = (Set.range y)ᶜ)
    (T : Ht q (sch.obj X) (2 * d) d →+ Ht q (sch.obj P) (2 * d) d)
    (Tr : Hrel (ZMod q) (sch.map U.ι) (tw q d) (2 * d) →+ Hrel (ZMod q) (sch.map W.ι) (tw q d) (2 * d)),
    Function.Surjective Tr ∧
      ∀ e, T (relF (ZMod q) (sch.map U.ι) (tw q d) (2 * d) e) = relF (ZMod q) (sch.map W.ι) (tw q d) (2 * d) (Tr e)

def LeafRelPoint : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) (d : ℕ) [SmoothOfRelativeDimension d r]
    (y : Spec (CommRingCat.of k) ⟶ Y), y ≫ r = 𝟙 _ → ∀ W : Y.Opens, (W : Set Y) = (Set.range y)ᶜ →
    ∃ g : Hrel (ZMod q) (sch.map W.ι) (tw q d) (2 * d), addOrderOf g = q ∧ ∀ e, ∃ m : ℤ, e = m • g

def LeafRelTransferOrd : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
    {P : Scheme.{0}} [IsIntegral P] (r : P ⟶ Spec (CommRingCat.of k)) [IsProper r] [SmoothOfRelativeDimension d r],
  RatModel r d →
  ∃ (x : Spec (CommRingCat.of k) ⟶ X) (_ : x ≫ p = 𝟙 _) (U : X.Opens) (_ : (U : Set X) = (Set.range x)ᶜ)
    (y : Spec (CommRingCat.of k) ⟶ P) (_ : y ≫ r = 𝟙 _) (W : P.Opens) (_ : (W : Set P) = (Set.range y)ᶜ)
    (T : Ht q (sch.obj X) (2 * d) d →+ Ht q (sch.obj P) (2 * d) d)
    (Tr : Hrel (ZMod q) (sch.map U.ι) (tw q d) (2 * d) →+ Hrel (ZMod q) (sch.map W.ι) (tw q d) (2 * d)),
    (∃ e, addOrderOf (Tr e) = q) ∧
      ∀ e, T (relF (ZMod q) (sch.map U.ι) (tw q d) (2 * d) e) = relF (ZMod q) (sch.map W.ι) (tw q d) (2 * d) (Tr e)

end LateralTheory.E.E8

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def LeafArtinAffine : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ), DimLE p d →
  ∀ V : X.Opens, IsAffineOpen V → ∀ (n i : ℤ), (d : ℤ) < n → Subsingleton (H (ZMod q) (sch.obj V) (tw q i) n)

def LeafMVVanish : Prop := Base → ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (A B : X.Opens) (F : Shv R) (c : ℤ),
  (∀ n : ℤ, c < n → Subsingleton (H R (sch.obj A) F n)) → (∀ n : ℤ, c < n → Subsingleton (H R (sch.obj B) F n)) →
  (∀ n : ℤ, c - 1 < n → Subsingleton (H R (sch.obj ((A ⊓ B : X.Opens) : Scheme.{0})) F n)) →
  ∀ n : ℤ, c < n → Subsingleton (H R (sch.obj ((A ⊔ B : X.Opens) : Scheme.{0})) F n)

def LeafEmptyVanish : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj (⊥ : X.Opens)) F n)

end LateralTheory.E.E8

end
end
