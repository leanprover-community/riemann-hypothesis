import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

section
noncomputable section

namespace GlobalTheory.DrinLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}}

structure FreeChart (Z : Over S) where

  R : Type
  [ringR : CommRing R]

  t : Sp R ⟶ S

  B : Type
  [ringB : CommRing B]
  [alg : Algebra R B]
  [free : Module.Free R B]
  [fin : Module.Finite R B]

  e : Sp B ≅ pullback Z.hom t

  e_snd : e.hom ≫ pullback.snd Z.hom t = spMap (algebraMap R B)

attribute [instance] FreeChart.ringR FreeChart.ringB FreeChart.alg FreeChart.free FreeChart.fin

def FreeChart.ev {Z : Over S} (c : FreeChart Z) (P : 𝟙_ (Over S) ⟶ Z) : c.B →+* c.R :=
  (Spec.preimage (pullback.lift (c.t ≫ P.left) (𝟙 _)
    (by rw [Category.assoc, Over.w P]; rfl) ≫ c.e.inv)).hom

def IsFinLocFree (Z : Over S) (N : ℕ) : Prop :=
  ∀ x : S, ∃ c : FreeChart Z, IsOpenImmersion c.t ∧ x ∈ Set.range c.t ∧ Module.finrank c.R c.B = N

def IsFullSet (Z : Over S) {J : Type} (P : J → (𝟙_ (Over S) ⟶ Z)) : Prop :=
  Finite J ∧ IsFinLocFree Z (Nat.card J) ∧
    ∀ (c : FreeChart Z) (f : c.B), Algebra.norm c.R f = ∏ᶠ i, c.ev (P i) f

variable {O : Type} [CommRing O]

structure DrinfeldLevel {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OAct O G) (ϖ : O) (h m : ℕ) where

  α : (Fin h → O ⧸ Ideal.span {ϖ ^ m}) → (𝟙_ (Over S) ⟶ G)
  map_add : ∀ x y, α (x + y) = α x * α y
  map_smul : ∀ (c : O) x, α (c • x) = α x ≫ a.act c
  full : IsFullSet G α

end GlobalTheory.DrinLev

namespace GlobalTheory.DrinLev
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

def FreeChart.self (R : Type) [CommRing R] : FreeChart (Over.mk (𝟙 (Sp R))) where
  R := R
  t := 𝟙 _
  B := R
  e := (asIso (pullback.snd (𝟙 (Sp R)) (𝟙 (Sp R)))).symm
  e_snd := by
    simp only [Iso.symm_hom, asIso_inv, IsIso.inv_hom_id, Over.mk_hom]
    simp [spMap, Algebra.algebraMap_self]

example (R : Type) [CommRing R] [Nontrivial R] :
    Module.finrank (FreeChart.self R).R (FreeChart.self R).B = 1 :=
  Module.finrank_self R

example (R : Type) [CommRing R] : IsFinLocFree (Over.mk (𝟙 (Sp R))) 1 := by
  intro x
  have : Nontrivial R := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (PrimeSpectrum.isEmpty_iff_subsingleton.mpr h).false x
  exact ⟨FreeChart.self R, inferInstanceAs (IsOpenImmersion (𝟙 _)), ⟨x, rfl⟩, Module.finrank_self R⟩

end GlobalTheory.DrinLev
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField

namespace GlobalTheory.DrinLev.HT

open GlobalTheory.UPel.HT GlobalTheory.IwLevel

variable {p : ℕ} [Fact p.Prime]

abbrev powO (D : Datum p) (w : Ideal (𝓞 D.F)) (m : ℕ) : Ideal D.O := (w ^ m).map (algebraMap (𝓞 D.F) D.O)

def IsRankOneIdem (D : Datum p) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) : Prop :=
  e * e - e ∈ powO D w m ∧ (∀ x : D.O, ∃ c : 𝓞 D.F, e * x * e - algebraMap (𝓞 D.F) D.O c * e ∈ powO D w m) ∧
    e ∉ powO D w 1

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S S' : Scheme.{0}}

def IsEpsTors {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) {T : Over S} (x : T ⟶ o.A) :
    Prop :=
  KilledBy (htAct o) (powO D w m) x ∧ x ≫ o.act.act e = x

structure SubRep (A : Over S) (P : ∀ {T : Over S}, (T ⟶ A) → Prop) where

  Z : Over S

  incl : Z ⟶ A
  mono : Mono incl
  pts : ∀ (T : Over S) (x : T ⟶ A), P x ↔ ∃ y, y ≫ incl = x

def SubRep.unit (A : Over S) [GrpObj A] : SubRep A (fun x => x = 1) where
  Z := 𝟙_ (Over S)
  incl := 1
  mono := ⟨fun g h _ => toUnit_unique g h⟩
  pts T x := ⟨fun h => ⟨toUnit T, by rw [MonObj.comp_one, h]⟩, fun ⟨y, hy⟩ => hy ▸ MonObj.comp_one y⟩

structure HTLevel {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) where

  α : (Fin D.n → 𝓞 D.F ⧸ w ^ m) → (𝟙_ (Over S) ⟶ o.A)
  map_add : ∀ x y, α (x + y) = α x * α y
  map_smul : ∀ (c : 𝓞 D.F) x, α (c • x) = α x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)
  full : ∃ (G : SubRep o.A (IsEpsTors o w m e)) (β : (Fin D.n → 𝓞 D.F ⧸ w ^ m) → (𝟙_ (Over S) ⟶ G.Z)),
    (∀ x, β x ≫ G.incl = α x) ∧ IsFullSet G.Z β

structure ObjLev (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) (s : S ⟶ Sp R) where

  obj : Obj b N s

  lev : HTLevel obj w m e

def ObjLevMap {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} (o' : ObjLev b N w m e s')
    (o : ObjLev b N w m e s) (f : S' ⟶ S) : Prop :=
  ∃ φ : ObjMap o'.obj o.obj f, ∀ x, (o'.lev.α x).left ≫ φ.φ = f ≫ (o.lev.α x).left

structure LevRep (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) where

  X : Scheme.{0}

  s : X ⟶ Sp R

  univ : ObjLev b N w m e s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : ObjLev b N w m e s'),
    ∃! f : S ⟶ X, f ≫ s = s' ∧ ObjLevMap o univ f

namespace LevRep

variable {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O}

def forget (M : LevRep b N w m e) (F₀ : RepFam b N) : M.X ⟶ F₀.X :=
  (F₀.rep M.X M.s M.univ.obj).exists.choose

def Proj (M : LevRep b N w m e) : Prop := IsProjOver M.s

def Regular (M : LevRep b N w m e) : Prop := ∀ x : M.X, IsRegularLocalRing (M.X.presheaf.stalk x)

def FinFlat (M : LevRep b N w m e) (F₀ : RepFam b N) : Prop :=
  IsFinite (M.forget F₀) ∧ Flat (M.forget F₀)

end LevRep

structure LevModel (M₀ : Model b N) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) extends LevRep b N w m e where
  proj : toLevRep.Proj
  regular : toLevRep.Regular
  finFlat : toLevRep.FinFlat M₀.toRepFam

section Basic₂

example (D : Datum p) (w : Ideal (𝓞 D.F)) (e : D.O) (he : e ∉ powO D w 1) : IsRankOneIdem D w 0 e := by
  have h : powO D w 0 = ⊤ := by
    rw [powO, pow_zero, Ideal.one_eq_top]
    exact (Ideal.eq_top_iff_one _).2 (by simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) (Submodule.mem_top (x := (1 : 𝓞 D.F))))
  refine ⟨?_, fun x => ⟨0, ?_⟩, he⟩ <;> simp [h]

example {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) :
    IsEpsTors o w m e (1 : 𝟙_ (Over S) ⟶ o.A) := by
  have := o.act.hom e
  refine ⟨fun a _ => ?_, ?_⟩
  · have := (htAct o).hom a
    exact MonObj.one_comp _
  · exact MonObj.one_comp _

end Basic₂

end GlobalTheory.DrinLev.HT
end
end
