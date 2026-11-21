import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineInterFiniteBasicOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdjoinRestrictedSectionsOfLocal

section
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem exists_finset_awayMap_subalgebra_bijective :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B),
      (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) →
      ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C →
        ∀ b ∈ g, ∀ hb : b ∈ C,
          Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
  intro R B _ _ _ g hg
  classical
  have key : ∀ b ∈ g, ∃ t : Finset B, ∀ C : Subalgebra R B, (↑t : Set B) ⊆ ↑C → b ∈ C →
      ∀ x : B, ∃ m : ℕ, b ^ m * x ∈ C := by
    intro b hb
    obtain ⟨t, ht⟩ := (hg b hb).out
    refine ⟨t.image fun z => (IsLocalization.sec (Submonoid.powers b) z).1, fun C hC hbC x => ?_⟩
    have main : ∀ z : Localization.Away b, ∃ (m : ℕ) (c : B), c ∈ C ∧
        z * algebraMap B _ b ^ m = algebraMap B _ c := by
      intro z
      have hz : z ∈ Algebra.adjoin R (t : Set (Localization.Away b)) := ht ▸ Algebra.mem_top
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        obtain ⟨m, hm⟩ := (IsLocalization.sec (Submonoid.powers b) z).2.2
        refine ⟨m, (IsLocalization.sec (Submonoid.powers b) z).1, hC ?_, ?_⟩
        · simp only [Finset.coe_image]
          exact ⟨z, hz, rfl⟩
        · rw [← map_pow]
          have := IsLocalization.sec_spec (Submonoid.powers b) z
          rw [← hm] at this
          exact this
      | algebraMap r =>
        exact ⟨0, algebraMap R B r, C.algebraMap_mem r, by
          rw [pow_zero, mul_one, IsScalarTower.algebraMap_apply R B]⟩
      | add x y _ _ hx hy =>
        obtain ⟨m, c, hc, e⟩ := hx
        obtain ⟨n, d, hd, e'⟩ := hy
        refine ⟨m + n, c * b ^ n + d * b ^ m,
          add_mem (mul_mem hc (pow_mem hbC _)) (mul_mem hd (pow_mem hbC _)), ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, ← e, ← e']
        ring
      | mul x y _ _ hx hy =>
        obtain ⟨m, c, hc, e⟩ := hx
        obtain ⟨n, d, hd, e'⟩ := hy
        refine ⟨m + n, c * d, mul_mem hc hd, ?_⟩
        rw [map_mul, ← e, ← e']
        ring
    obtain ⟨m, c, hc, e⟩ := main (algebraMap B _ x)
    rw [← map_pow, ← map_mul] at e
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers b) _).1 e
    refine ⟨k + m, ?_⟩
    have : b ^ (k + m) * x = b ^ k * c := by
      have hk' : b ^ k * (x * b ^ m) = b ^ k * c := hk
      rw [← hk']; ring
    rw [this]
    exact mul_mem (pow_mem hbC _) hc
  choose! t ht using key
  refine ⟨g ∪ g.biUnion t, by simp, fun C hC b hb hbC => ⟨?_, ?_⟩⟩
  · refine (Localization.awayMap_injective_iff).2 fun a ha => ⟨0, ?_⟩
    have : a = 0 := Subtype.ext ha
    simp [this]
  · refine (Localization.awayMap_surjective_iff).2 fun x => ?_
    obtain ⟨m, hm⟩ := ht b hb C (fun y hy => hC (by
      simp only [Finset.coe_union, Finset.coe_biUnion, Set.mem_union, Set.mem_iUnion]
      exact Or.inr ⟨b, hb, hy⟩)) hbC x
    exact ⟨⟨_, hm⟩, m, rfl⟩

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B), (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) → ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C → ∀ b ∈ g, ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
  atlas_forward_decl GlobalTheory.exists_finset_awayMap_subalgebra_bijective
end

section
section
open Algebra

theorem GlobalTheory.adjoin_mem_of_away_localization {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'] (T : Set A) (b : A)
    (hb : algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T)) :
    ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  have hg : algebraMap A A' (algebraMap R A g) = algebraMap R A' g :=
    (IsScalarTower.algebraMap_apply R A A' g).symm
  have key : ∀ y ∈ Algebra.adjoin R' (algebraMap A A' '' T), ∃ k : ℕ, ∃ z ∈ Algebra.adjoin R T,
      algebraMap A A' z = algebraMap R A' g ^ k * y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨0, a, Algebra.subset_adjoin ha, by simp⟩
    | algebraMap r =>
      obtain ⟨⟨r0, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) r
      refine ⟨n, algebraMap R A r0, Subalgebra.algebraMap_mem _ r0, ?_⟩
      simp only at hr
      rw [← IsScalarTower.algebraMap_apply R A A', IsScalarTower.algebraMap_apply R R' A', ← hr,
        map_mul, ← IsScalarTower.algebraMap_apply R R' A', map_pow, mul_comm]
    | add x y _ _ hx hy =>
      obtain ⟨k1, z1, hz1, e1⟩ := hx
      obtain ⟨k2, z2, hz2, e2⟩ := hy
      refine ⟨k1 + k2, algebraMap R A g ^ k2 * z1 + algebraMap R A g ^ k1 * z2, ?_, ?_⟩
      · refine add_mem (mul_mem ?_ hz1) (mul_mem ?_ hz2) <;>
          (rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _)
      · rw [map_add, map_mul, map_mul, map_pow, map_pow, hg, e1, e2]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨k1, z1, hz1, e1⟩ := hx
      obtain ⟨k2, z2, hz2, e2⟩ := hy
      refine ⟨k1 + k2, z1 * z2, mul_mem hz1 hz2, ?_⟩
      rw [map_mul, e1, e2]; ring
  obtain ⟨k, z, hz, e⟩ := key _ hb
  have h0 : algebraMap A A' (z - algebraMap R A g ^ k * b) = 0 := by
    rw [map_sub, map_mul, map_pow, hg, e, sub_self]
  obtain ⟨⟨_, c, rfl⟩, hc⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A g)) A' _).1 h0
  refine ⟨c + k, ?_⟩
  have : algebraMap R A g ^ (c + k) * b = algebraMap R A g ^ c * z := by
    simp only at hc
    rw [mul_sub, sub_eq_zero] at hc
    rw [hc, pow_add]; ring
  rw [this]
  refine mul_mem ?_ hz
  rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _

theorem GlobalTheory.adjoin_mem_of_away_localization' : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (T : Set A) (b : A), algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T) → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  intros R A R' A' _ _ _ _ _ _ _ _ _ _ _ g _ _ T b h
  exact GlobalTheory.adjoin_mem_of_away_localization g T b h
end

open Algebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_mem_adjoin_of_localizationAway : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (T : Set A) (b : A), algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T) → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  atlas_forward_decl GlobalTheory.adjoin_mem_of_away_localization'
end

section
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub.PowerMultiple

variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)

theorem res_pow_mul_mem_gen
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {D W V : X.Opens} (hD : IsAffineOpen D) (hDW : D ≤ W) (hDV : D ≤ V)
    (T : Set (F.obj (op V))) (f : Γ(X, W)) (a : F.obj (op W))
    (ha : ∀ (W' : X.Opens), IsAffineOpen W' → ∀ (h1 : W' ≤ X.basicOpen f) (h2 : W' ≤ V),
      (F.map (homOfLE h1).op).hom ((F.map (homOfLE (X.basicOpen_le f)).op).hom a) ∈
        gen F α h2 T) :
    ∃ m : ℕ, (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f ^ m * a) ∈ gen F α hDV T := by
  set fD : Γ(X, D) := (X.presheaf.map (homOfLE hDW).op).hom f with hfD
  have hbo : X.basicOpen fD = D ⊓ X.basicOpen f := Scheme.basicOpen_res X f (homOfLE hDW).op
  have hD'D : X.basicOpen fD ≤ D := X.basicOpen_le fD
  have hD'f : X.basicOpen fD ≤ X.basicOpen f := hbo.le.trans inf_le_right
  have hD'V : X.basicOpen fD ≤ V := hD'D.trans hDV
  have hD' : IsAffineOpen (X.basicOpen fD) := hD.basicOpen fD
  letI iRA : Algebra Γ(X, D) (F.obj (op D)) := (α.app (op D)).hom.toAlgebra
  letI iRR' : Algebra Γ(X, D) Γ(X, X.basicOpen fD) :=
    (X.presheaf.map (homOfLE hD'D).op).hom.toAlgebra
  letI iR'A' : Algebra Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) :=
    (α.app (op (X.basicOpen fD))).hom.toAlgebra
  letI iAA' : Algebra (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    (F.map (homOfLE hD'D).op).hom.toAlgebra
  letI iRA' : Algebra Γ(X, D) (F.obj (op (X.basicOpen fD))) :=
    ((F.map (homOfLE hD'D).op).hom.comp (α.app (op D)).hom).toAlgebra
  haveI : IsScalarTower Γ(X, D) (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(X, D) Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have := congr($(α.naturality (homOfLE hD'D).op).hom r)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  haveI : IsLocalization.Away fD Γ(X, X.basicOpen fD) := hD.isLocalization_basicOpen fD
  haveI : IsLocalization.Away (algebraMap Γ(X, D) (F.obj (op D)) fD)
      (F.obj (op (X.basicOpen fD))) := isLocalizationAway F α hα hD fD
  have hres : ∀ {U₁ U₂ U₃ : X.Opens} (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂) (y : F.obj (op U₁)),
      (F.map (homOfLE h₂).op).hom ((F.map (homOfLE h₁).op).hom y) =
        (F.map (homOfLE (h₂.trans h₁)).op).hom y := by
    intro U₁ U₂ U₃ h₁ h₂ y
    rw [← CommRingCat.comp_apply, ← F.map_comp]
    rfl
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_pow_mul_mem_adjoin_of_localizationAway (R := Γ(X, D)) (A := F.obj (op D))
    (R' := Γ(X, X.basicOpen fD)) (A' := F.obj (op (X.basicOpen fD))) fD
    ((F.map (homOfLE hDV).op).hom '' T) ((F.map (homOfLE hDW).op).hom a) (by
      have h0 := ha _ hD' hD'f hD'V
      rw [hres, gen_eq_adjoin] at h0
      change (F.map (homOfLE hD'D).op).hom ((F.map (homOfLE hDW).op).hom a) ∈ _
      rw [hres, Set.image_image]
      have hfun : (fun x => (algebraMap (F.obj (op D)) (F.obj (op (X.basicOpen fD))))
          ((F.map (homOfLE hDV).op).hom x)) = ⇑(F.map (homOfLE hD'V).op).hom :=
        funext fun x => hres _ _ x
      rw [hfun]
      exact h0)
  refine ⟨m, ?_⟩
  have hnat : (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f) = (α.app (op D)).hom fD := by
    have := congr($(α.naturality (homOfLE hDW).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  rw [map_mul, map_pow, hnat, gen_eq_adjoin]
  exact hm

end GlobalTheory.QcSub.PowerMultiple

theorem GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by
  intro X hX F α hα ι _ V hV T W hW f a ha
  classical
  haveI := Fintype.ofFinite ι
  rw [mem_sub] at ha
  choose s hs1 hs2 using fun j => GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen X hX W (V j) hW (hV j)
  have hle : ∀ j, ∀ h ∈ s j, X.basicOpen h ≤ V j := by
    intro j h hh
    obtain ⟨r, hr⟩ := hs1 j h hh
    rw [hr]
    exact X.basicOpen_le r
  choose m hm using fun j (h : s j) =>
    GlobalTheory.QcSub.PowerMultiple.res_pow_mul_mem_gen F α hα (hW.basicOpen h.1) (X.basicOpen_le h.1)
      (hle j h.1 h.2) (T j) f a (fun W' hW' h1 h2 => ha j W' hW' h1 h2)
  refine ⟨∑ j, ∑ h : s j, m j h, ?_⟩
  rw [mem_sub]
  intro j W' hW' hWW' hWV
  refine GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) W (T j) _ ?_ W' hW' hWW' hWV
  intro x hx
  have hx' := hs2 j hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx'
  obtain ⟨h, hh, hxh⟩ := hx'
  refine ⟨X.basicOpen h, hW.basicOpen h, hxh, X.basicOpen_le h, hle j h hh, ?_⟩
  have hmle : m j ⟨h, hh⟩ ≤ ∑ j, ∑ h : s j, m j h :=
    le_trans (Finset.single_le_sum (f := fun h' => m j h') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨h, hh⟩ : s j)))
      (Finset.single_le_sum (f := fun j' => ∑ h' : s j', m j' h') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j))
  rw [show ∑ j, ∑ h : s j, m j h = (∑ j, ∑ h : s j, m j h - m j ⟨h, hh⟩) + m j ⟨h, hh⟩ by omega,
    pow_add, mul_assoc, map_mul]
  refine mul_mem ?_ (hm j ⟨h, hh⟩)
  rw [map_pow]
  refine pow_mem ?_ _
  have := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom f)
  simp only [CommRingCat.comp_apply] at this
  rw [← this]
  exact algebraMap_mem_gen F α _ _ _
end

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_mem_subalgebra_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by
  atlas_forward_decl GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen
end

section
section
namespace GlobalTheory

theorem submodule_fg_of_locally_le_fg {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] (M : Submodule R A) (s : Set R) (hs : Ideal.span s = ⊤)
    (hE : ∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ,
      algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) : M.FG := by
  classical
  obtain ⟨s0, hs0s, hs0⟩ := (Ideal.span_eq_top_iff_finite s).1 hs
  choose! E hEm using hE
  let T : Set A := ⋃ g ∈ (s0 : Set R), (E g : Set A)
  have hT : T.Finite := Set.Finite.biUnion s0.finite_toSet fun g _ => (E g).finite_toSet
  refine Submodule.FG.of_le (Submodule.fg_span hT) ?_
  intro b hb
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s0 : Set R) hs0 b ?_
  intro g
  obtain ⟨m, hm⟩ := hEm g.1 (hs0s g.2) b hb
  refine ⟨m, ?_⟩
  have hle : Submodule.span R (E g.1 : Set A) ≤ Submodule.span R T :=
    Submodule.span_mono (Set.subset_biUnion_of_mem (u := fun g => (E g : Set A)) g.2)
  have : (g.1 ^ m) • b = algebraMap R A g.1 ^ m * b := by
    rw [Algebra.smul_def, map_pow]
  rw [this]
  exact hle hm

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem : ∀ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing R] (M : Submodule R A) (s : Set R), Ideal.span s = ⊤ → (∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) → M.FG := by
  atlas_forward_decl GlobalTheory.submodule_fg_of_locally_le_fg
end

section
section
namespace GlobalTheory

open Submodule

theorem fg_localizationAway_span_finset
    {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R)
    [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A']
    (N : Submodule R' A') (hN : N.FG) :
    ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N →
      ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  classical
  obtain ⟨S, rfl⟩ := hN
  have hA : ∀ (c : R) (z : A),
      algebraMap A A' (c • z) = algebraMap R A' c * algebraMap A A' z := by
    intro c z
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  have hsurj : ∀ n : A', ∃ e : A, ∃ k : ℕ,
      n * algebraMap R A' g ^ k = algebraMap A A' e := by
    intro n
    obtain ⟨k, e, h⟩ := IsLocalization.Away.surj (algebraMap R A g) n
    exact ⟨e, k, by rw [IsScalarTower.algebraMap_apply R A A']; exact h⟩
  choose e k he using hsurj
  refine ⟨S.image e, ?_⟩
  have key : ∀ y ∈ Submodule.span R' (S : Set A'), ∃ m : ℕ,
      ∃ z ∈ Submodule.span R ((S.image e : Finset A) : Set A),
        algebraMap A A' z = algebraMap R A' g ^ m * y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      refine ⟨k x, e x, Submodule.subset_span ?_, ?_⟩
      · simp only [Finset.coe_image]
        exact Set.mem_image_of_mem e hx
      · rw [← he, mul_comm]
    | zero => exact ⟨0, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m1, z1, hz1, h1⟩ := hx
      obtain ⟨m2, z2, hz2, h2⟩ := hy
      refine ⟨m1 + m2, g ^ m2 • z1 + g ^ m1 • z2,
        add_mem (smul_mem _ _ hz1) (smul_mem _ _ hz2), ?_⟩
      rw [map_add, hA, hA, h1, h2, map_pow, map_pow]
      ring
    | smul r' x _ hx =>
      obtain ⟨m, z, hz, h⟩ := hx
      obtain ⟨l, r, hr⟩ := IsLocalization.Away.surj g r'
      refine ⟨m + l, r • z, smul_mem _ _ hz, ?_⟩
      have hr' : algebraMap R A' r = algebraMap R' A' r' * algebraMap R A' g ^ l := by
        rw [IsScalarTower.algebraMap_apply R R' A', ← hr, map_mul, map_pow,
          ← IsScalarTower.algebraMap_apply]
      rw [hA, h, Algebra.smul_def, hr']
      ring
  intro b hb
  obtain ⟨m, z, hz, h⟩ := key _ hb
  have h0 : algebraMap A A' (z - algebraMap R A g ^ m * b) = 0 := by
    rw [map_sub, h, map_mul, map_pow, ← IsScalarTower.algebraMap_apply, sub_self]
  obtain ⟨⟨x, hx⟩, hc⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A g)) A' _).1 h0
  obtain ⟨c, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hx
  refine ⟨c + m, ?_⟩
  have hc' : algebraMap R A g ^ c * (z - algebraMap R A g ^ m * b) = 0 := hc
  have : algebraMap R A g ^ (c + m) * b = g ^ c • z := by
    rw [Algebra.smul_def, map_pow]
    linear_combination -hc'
  rw [this]
  exact smul_mem _ _ hz

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (N : Submodule R' A'), N.FG → ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  atlas_forward_decl GlobalTheory.fg_localizationAway_span_finset
end

section
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem subMap_finite (X : Scheme.{0}) (_hX : IsNoetherian X) (F : X.Opensᵒᵖ ⥤ CommRingCat)
    (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    (hint : ∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral)
    {ι : Type} (V : ι → X.Opens) (_hV : ∀ j, IsAffineOpen (V j)) (hcov : ∀ x : X, ∃ j, x ∈ V j)
    (T : ∀ j, Set (F.obj (op (V j)))) (hT : ∀ j, (T j).Finite) (W : X.Opens)
    (hW : IsAffineOpen W) : (subMap F α V T W).Finite := by
  haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI alg : Algebra Γ(X, W) (F.obj (op W)) := (α.app (op W)).hom.toAlgebra
  let S : Subalgebra Γ(X, W) (F.obj (op W)) :=
    { sub F α V T W with algebraMap_mem' := algebraMap_mem_sub F α V T W }
  let s : Set Γ(X, W) := {g | ∃ j, X.basicOpen g ≤ V j}
  have hs : Ideal.span s = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨g, hg, hxg⟩ := hW.exists_basicOpen_le (V := V j) ⟨x, hj⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, j, hg⟩, hxg⟩
  have hloc : ∀ g ∈ s, ∃ E : Finset (F.obj (op W)), ∀ b ∈ S.toSubmodule, ∃ m : ℕ,
      algebraMap Γ(X, W) (F.obj (op W)) g ^ m * b ∈ Submodule.span Γ(X, W) (E : Set _) := by
    rintro g ⟨j, hj⟩
    have hD : IsAffineOpen (X.basicOpen g) := hW.basicOpen g
    letI a1 : Algebra Γ(X, W) Γ(X, X.basicOpen g) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    letI a2 : Algebra Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      (α.app (op (X.basicOpen g))).hom.toAlgebra
    letI a3 : Algebra (F.obj (op W)) (F.obj (op (X.basicOpen g))) :=
      (F.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    letI a4 : Algebra Γ(X, W) (F.obj (op (X.basicOpen g))) :=
      ((α.app (op (X.basicOpen g))).hom.comp
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom).toAlgebra
    haveI : IsScalarTower Γ(X, W) (F.obj (op W)) (F.obj (op (X.basicOpen g))) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ by
        have := congr($(α.naturality (homOfLE (X.basicOpen_le g)).op).hom r)
        simp only [CommRingCat.comp_apply] at this
        exact this
    haveI : IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ rfl
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) := hW.isLocalization_basicOpen g
    haveI : IsLocalization.Away (algebraMap Γ(X, W) (F.obj (op W)) g)
        (F.obj (op (X.basicOpen g))) := isLocalizationAway F α hα hW g
    let N : Submodule Γ(X, X.basicOpen g) (F.obj (op (X.basicOpen g))) :=
      (Algebra.adjoin Γ(X, X.basicOpen g) ((F.map (homOfLE hj).op).hom '' T j)).toSubmodule
    have hN : N.FG := fg_adjoin_of_finite ((hT j).image _) (fun x _ ↦ hint _ hD x)
    obtain ⟨E, hE⟩ := GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway (R := Γ(X, W)) (A := F.obj (op W)) (R' := Γ(X, X.basicOpen g))
      (A' := F.obj (op (X.basicOpen g))) g N hN
    refine ⟨E, fun b hb ↦ hE b ?_⟩
    have := (mem_sub F α V T).mp hb j (X.basicOpen g) hD (X.basicOpen_le g) hj
    rw [gen_eq_adjoin] at this
    exact this
  have hfg : S.toSubmodule.FG := GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem S.toSubmodule s hs hloc
  letI := (subMap F α V T W).toAlgebra
  have hfin : Module.Finite Γ(X, W) S.toSubmodule := Module.Finite.iff_fg.mpr hfg
  let e : S.toSubmodule ≃ₗ[Γ(X, W)] sub F α V T W :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact Module.Finite.equiv e

end GlobalTheory.QcSub
end

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral) → ∀ {ι : Type} (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → (∀ x : X, ∃ j, x ∈ V j) → ∀ (T : ∀ j, Set (F.obj (op (V j)))), (∀ j, (T j).Finite) → ∀ W : X.Opens, IsAffineOpen W → (subMap F α V T W).Finite := by
  atlas_forward_decl GlobalTheory.QcSub.subMap_finite
end

section
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.SubChoose

theorem exists_num {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {U : X.Opens} (hU : IsAffineOpen U) (h : Γ(X, U)) (z : F.obj (op (X.basicOpen h))) :
    ∃ (a : F.obj (op U)) (n : ℕ), z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a := by
  letI := (F.map (homOfLE (X.basicOpen_le h)).op).hom.toAlgebra
  haveI := isLocalizationAway F α hα hU h
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj ((α.app (op U)).hom h) z
  refine ⟨a, n, ?_⟩
  have nat := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom h)
  simp only [CommRingCat.comp_apply] at nat
  rw [nat]
  exact e

theorem mem_gen_of_eq {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    {U : X.Opens} (h : Γ(X, U)) (T : Set (F.obj (op U))) {a : F.obj (op U)} (ha : a ∈ T)
    (z : F.obj (op (X.basicOpen h))) (n : ℕ)
    (e : z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a) :
    z ∈ gen F α (X.basicOpen_le h) T := by
  have hu0 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) :=
    X.toRingedSpace.isUnit_res_basicOpen h
  obtain ⟨u, hu⟩ := hu0
  have key : (α.app (op (X.basicOpen h))).hom (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) *
      (α.app (op (X.basicOpen h))).hom ↑u⁻¹ = 1 := by
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  have hz : z = (F.map (homOfLE (X.basicOpen_le h)).op).hom a *
      ((α.app (op (X.basicOpen h))).hom ↑u⁻¹) ^ n := by
    rw [← e, mul_assoc, ← mul_pow, key, one_pow, mul_one]
  rw [hz]
  exact mul_mem (res_mem_gen F α _ T ha) (pow_mem (algebraMap_mem_gen F α _ T _) n)

end GlobalTheory.SubChoose

theorem GlobalTheory.sub_choose_finite : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  intro X hX F α hα ι _ V hV S hS
  choose s hs1 hs2 using fun i j => GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen X hX (V j) (V i) (hV j) (hV i)
  have hDi : ∀ i j, ∀ h ∈ s i j, X.basicOpen h ≤ V i := by
    intro i j h hh
    obtain ⟨r, hr⟩ := hs1 i j h hh
    rw [hr]
    exact X.basicOpen_le r
  haveI : ∀ i, Finite (S i) := fun i => (hS i).to_subtype
  choose a n ha using fun (j : ι) (p : Σ i, (S i) × (s i j)) =>
    GlobalTheory.SubChoose.exists_num F α hα (hV j) p.2.2.1
      ((F.map (homOfLE (hDi p.1 j p.2.2.1 p.2.2.2)).op).hom p.2.1.1)
  refine ⟨fun j => Set.range (a j), fun j => Set.finite_range _, ?_⟩
  intro i x hx
  rw [SetLike.mem_coe, mem_sub]
  intro j W' hW' hWi hWj
  apply GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) (V i) (Set.range (a j)) x _ W' hW' hWi hWj
  intro y hy
  have hy' : y ∈ ((V j ⊓ V i : X.Opens) : Set X) := ⟨hy.2, hy.1⟩
  have := hs2 i j hy'
  simp only [Set.mem_iUnion] at this
  obtain ⟨h, hh, hyh⟩ := this
  refine ⟨X.basicOpen h, (hV j).basicOpen h, hyh, hDi i j h hh, X.basicOpen_le h, ?_⟩
  exact GlobalTheory.SubChoose.mem_gen_of_eq F α h _ (Set.mem_range_self (⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩ : Σ i, (S i) × (s i j))) _ _
    (ha j ⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩)
end

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_sets_subalgebra_finite_affine_cover : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  atlas_forward_decl GlobalTheory.sub_choose_finite
end

section
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem isLocalizationAway_subring {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A')
    (S : Subring A) (S' : Subring A') (hρ : ∀ a ∈ S, ρ a ∈ S') (s : A) (hs : s ∈ S)
    (hloc : letI := ρ.toAlgebra; IsLocalization.Away s A')
    (hu : ∃ v ∈ S', ρ s * v = 1) (hd : ∀ a : A, ρ a ∈ S' → ∃ m : ℕ, s ^ m * a ∈ S) :
    letI := (ρ.restrict S S' hρ).toAlgebra
    IsLocalization.Away (⟨s, hs⟩ : S) S' := by
  letI := ρ.toAlgebra
  letI := (ρ.restrict S S' hρ).toAlgebra
  refine .mk _ ?_ (fun z ↦ ?_) fun a b hab ↦ ?_
  · obtain ⟨v, hv, hsv⟩ := hu
    exact .of_mul_eq_one (⟨v, hv⟩ : S') (Subtype.ext hsv)
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := A') s (z : A')
    have ha' : ρ a = (z : A') * ρ s ^ n := ha.symm
    have hmem : ρ a ∈ S' := ha' ▸ S'.mul_mem z.2 (S'.pow_mem (hρ s hs) n)
    obtain ⟨m, hm⟩ := hd a hmem
    refine ⟨n + m, ⟨s ^ m * a, hm⟩, Subtype.ext ?_⟩
    change (z : A') * ρ s ^ (n + m) = ρ (s ^ m * a)
    rw [map_mul, map_pow, ha', pow_add]
    ring
  · have h : ρ a = ρ b := congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') s (a := (a : A)) (b := (b : A)) h
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

end GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem coequifibered_subNat (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))
    (hd : ∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) →
      ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) :
    (subNat F α V T).Coequifibered := by
  rw [Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  have hloc := isLocalizationAway F α hα U.2 f
  have hnat : (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) =
      (α.app (op (X.basicOpen f))).hom ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) := by
    have := congr($(α.naturality (homOfLE (X.basicOpen_le f)).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  have hu : ∃ v ∈ sub F α V T (X.basicOpen f),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) * v = 1 := by
    obtain ⟨w, hw⟩ : ∃ w : Γ(X, X.basicOpen f),
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f * w = 1 :=
      (X.toRingedSpace.isUnit_res_basicOpen f).exists_right_inv
    refine ⟨(α.app (op (X.basicOpen f))).hom w, algebraMap_mem_sub F α V T _ w, ?_⟩
    rw [hnat, ← map_mul, hw, map_one]
  exact isLocalizationAway_subring (F.map (homOfLE (X.basicOpen_le f)).op).hom
    (sub F α V T U.1) (sub F α V T (X.basicOpen f)) (fun a ha ↦ res_mem_sub F α V T _ ha)
    _ (algebraMap_mem_sub F α V T U.1 f) hloc hu (hd U.1 U.2 f)

end GlobalTheory.QcSub
end

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j)))), (∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) → (subNat F α V T).Coequifibered := by
  atlas_forward_decl GlobalTheory.QcSub.coequifibered_subNat
end

section
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem exists_finite_coequifibered_subalgebra : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (Opposite.op U)).hom.IsIntegral) → ∀ (n : ℕ) (U : Fin n → X.AffineZariskiSite) (S : ∀ k, Finset (F.obj (Opposite.op (U k).1))), ∃ (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α' : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (ι : F' ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F), α'.Coequifibered ∧ α' ≫ ι = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α ∧ (∀ V, Function.Injective (ι.app V).hom) ∧ (∀ V, (α'.app V).hom.Finite) ∧ ∀ k, ∀ x ∈ S k, ∃ y, (ι.app (Opposite.op (U k))).hom y = x := by
  intro X hX F α hα hint n U S
  obtain ⟨t, ht⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun A : X.AffineZariskiSite => (A.1 : Set X)) (fun A => A.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  let V : Fin n ⊕ t → X.Opens := Sum.elim (fun k => (U k).1) (fun A => A.1.1)
  have hV : ∀ j, IsAffineOpen (V j) := by
    rintro (k | A)
    exacts [(U k).2, A.1.2]
  have hcov : ∀ x : X, ∃ j, x ∈ V j := by
    intro x
    obtain ⟨A, hA, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨.inr ⟨A, hA⟩, hx⟩
  let S' : ∀ j, Set (F.obj (op (V j))) := fun j =>
    Sum.rec (motive := fun j => Set (F.obj (op (V j)))) (fun k => ((S k : Set (F.obj (op (U k).1))))) (fun _ => ∅) j
  have hS' : ∀ j, (S' j).Finite := by
    rintro (k | A)
    exacts [(S k).finite_toSet, Set.finite_empty]
  obtain ⟨T, hTfin, hST⟩ := GlobalTheory.T.exists_finite_sets_subalgebra_finite_affine_cover X hX F α hα V hV S' hS'
  refine ⟨subFunctor F α V T, subNat F α V T, subIncl F α V T,
    GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent X F α hα V T (GlobalTheory.T.pow_mul_mem_subalgebra_of_res_basicOpen X hX F α hα V hV T), subNat_comp_subIncl F α V T,
    subIncl_injective F α V T,
    fun W => GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent X hX F α hα hint V hV hcov T hTfin W.unop.1 W.unop.2,
    fun k x hx => ⟨⟨x, hST (.inl k) (Finset.mem_coe.mpr hx)⟩, rfl⟩⟩

end GlobalTheory.QcSub
end

open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_coequifibered_subalgebra_alt : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (Opposite.op U)).hom.IsIntegral) → ∀ (n : ℕ) (U : Fin n → X.AffineZariskiSite) (S : ∀ k, Finset (F.obj (Opposite.op (U k).1))), ∃ (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α' : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (ι : F' ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F), α'.Coequifibered ∧ α' ≫ ι = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α ∧ (∀ V, Function.Injective (ι.app V).hom) ∧ (∀ V, (α'.app V).hom.Finite) ∧ ∀ k, ∀ x ∈ S k, ∃ y, (ι.app (Opposite.op (U k))).hom y = x := by
  atlas_forward_decl GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra
end

section
section
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

set_option autoImplicit false
noncomputable section

namespace GlobalTheory

theorem isIso_specMap_restrict_basicOpen_of_bijective {R S : CommRingCat.{0}} (f : R ⟶ S) (r : R)
    (h : Function.Bijective (Localization.awayMap f.hom r)) :
    IsIso (Spec.map f ∣_ (PrimeSpectrum.basicOpen r : (Spec R).Opens)) := by
  set φ := Spec.map f with hφ
  set g : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv r with hg
  have hbo : (PrimeSpectrum.basicOpen r : (Spec R).Opens) = (Spec R).basicOpen g :=
    (basicOpen_eq_of_affine (R := R) r).symm
  rw [hbo]
  have hU := isAffineOpen_top (Spec R)
  have hpre : IsAffineOpen (φ ⁻¹ᵁ (⊤ : (Spec R).Opens)) := by
    simpa using isAffineOpen_top (Spec S)
  have nat : ∀ x : R, (φ.app ⊤).hom ((Scheme.ΓSpecIso R).inv x) =
      (Scheme.ΓSpecIso S).inv (f x) := fun x =>
    (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality f)).symm
  have hi := (IsLocalization.Away.map_injective_iff (S := Localization.Away r)
    (Q := Localization.Away (f.hom r)) f.hom r).mp h.1
  have hs := (IsLocalization.Away.map_surjective_iff (S := Localization.Away r)
    (Q := Localization.Away (f.hom r)) f.hom r).mp h.2
  rw [isIso_morphismRestrict_iff_isIso_app _ (hU.basicOpen g),
    hU.app_basicOpen_eq_away_map φ hpre g]
  refine IsIso.comp_isIso' ?_ inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  have := hU.isLocalization_basicOpen g
  have := hpre.isLocalization_basicOpen ((φ.app ⊤).hom g)
  constructor
  · refine (IsLocalization.Away.map_injective_iff _ _ _).2 fun a ha => ?_
    obtain ⟨x, rfl⟩ : ∃ x, (Scheme.ΓSpecIso R).inv x = a :=
      ⟨(Scheme.ΓSpecIso R).hom a, Iso.hom_inv_id_apply _ _⟩
    rw [nat] at ha
    have hx : f x = 0 := by
      have := congrArg (Scheme.ΓSpecIso S).hom ha
      rw [Iso.inv_hom_id_apply] at this
      exact this.trans (map_zero _)
    obtain ⟨n, hn⟩ := hi x hx
    exact ⟨n, by rw [hg, ← map_pow, ← map_mul, hn, map_zero]⟩
  · refine (IsLocalization.Away.map_surjective_iff _ _ _ _).2 fun b => ?_
    obtain ⟨y, rfl⟩ : ∃ y, (Scheme.ΓSpecIso S).inv y = b :=
      ⟨(Scheme.ΓSpecIso S).hom b, Iso.hom_inv_id_apply _ _⟩
    obtain ⟨c, m, e⟩ := hs y
    exact ⟨(Scheme.ΓSpecIso R).inv c, m, by
      rw [nat, hg, nat]
      exact (congrArg (Scheme.ΓSpecIso S).inv.hom e).trans
        ((map_mul _ _ _).trans (congrArg (· * _) (map_pow _ _ _)))⟩

set_option backward.isDefEq.respectTransparency false in

theorem relSpec_map_isIso_over_basicOpen : ∀ (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F), α' ≫ ι = α → ∀ (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued), g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase → (∀ V, (relativeGluingData hα).cover.f V ≫ g = Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V) → ∀ (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V)), Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b) → ∀ (W : (relativeGluingData hα').glued.Opens), (W : Set (relativeGluingData hα').glued) = (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V)))) → IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) = (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) : Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by
  intro X F F' α α' hα hα' ι hαι g hg hg' V b hb W hW
  haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI := (relativeGluingData hα).cover.map_prop V
  haveI := (relativeGluingData hα').cover.map_prop V
  set φ := Spec.map (ι.app (Opposite.op V)) with hφ
  have hnat : (relativeGluingData hα).natTrans.app V =
      φ ≫ (relativeGluingData hα').natTrans.app V := by
    subst hαι
    simp [relativeGluingData, hφ, Spec.map_comp]
  have H : IsPullback φ ((relativeGluingData hα).cover.f V) ((relativeGluingData hα').cover.f V) g := by
    refine IsPullback.of_right ?_ (hg' V).symm ((relativeGluingData hα').isPullback_natTrans_ι_toBase V)
    rw [← hnat, hg]
    exact (relativeGluingData hα).isPullback_natTrans_ι_toBase V
  have hW' : W = (relativeGluingData hα').cover.f V ''ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) := by
    ext1; exact hW
  subst hW'
  have h1 := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H
    (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens)
  have hpre : φ ⁻¹ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) =
      PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) := by
    ext x; rfl
  refine ⟨?_, ?_⟩
  · set D' : (Spec (F'.obj (Opposite.op V))).Opens := PrimeSpectrum.basicOpen b with hD'
    have H₂ := (isPullback_morphismRestrict φ D').paste_vert H
    haveI : IsIso (φ ∣_ D') := isIso_specMap_restrict_basicOpen_of_bijective _ b hb
    haveI : IsIso (pullback.snd g (D'.ι ≫ (relativeGluingData hα').cover.f V)) := by
      rw [← H₂.flip.isoPullback_inv_snd]
      infer_instance
    have hr : (D'.ι ≫ (relativeGluingData hα').cover.f V).opensRange =
        (relativeGluingData hα').cover.f V ''ᵁ D' := by
      ext1
      rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.Opens.range_ι]
      rfl
    have := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictOpensRange g (D'.ι ≫ (relativeGluingData hα').cover.f V))).mpr
      (show IsIso _ from inferInstance)
    rw [hr] at this
    exact this
  · rw [← h1, hpre]
    rfl

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relSpec_map_isIso_over_basicOpen_alt : ∀ (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F), α' ≫ ι = α → ∀ (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued), g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase → (∀ V, (relativeGluingData hα).cover.f V ≫ g = Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V) → ∀ (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V)), Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b) → ∀ (W : (relativeGluingData hα').glued.Opens), (W : Set (relativeGluingData hα').glued) = (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V)))) → IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) = (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) : Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by
  atlas_forward_decl GlobalTheory.relSpec_map_isIso_over_basicOpen
end

section
section
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

theorem normalization_basicOpen_cover (U X : Scheme.{0}) (f : U ⟶ X) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra;
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈ f.normalizationOpenCover.f V ''
        (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by
  classical
  set B := f.normalizationDiagram.obj (Opposite.op V.1) with hB
  set ι := f.normalizationOpenCover.f V with hι
  set j := f.toNormalization with hj
  have key : ∀ b : B, (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j →
      letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
      Algebra.FiniteType Γ(X, V.1) (Localization.Away b) := by
    intro b hb
    letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
    let g : Spec (.of (Localization.Away b)) ⟶ Spec B :=
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))
    have hg : Set.range (g ≫ ι) ⊆ Set.range j := by
      rintro _ ⟨z, rfl⟩
      apply hb
      have : g z ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := ⟨z, rfl⟩
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b] at this
      exact this
    let h := IsOpenImmersion.lift j (g ≫ ι) hg
    have hh : h ≫ j = g ≫ ι := IsOpenImmersion.lift_fac _ _ _
    haveI : LocallyOfFiniteType (h ≫ j) := by rw [hh]; infer_instance
    haveI : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h j
    have e : h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away b))) ≫
        V.2.fromSpec := by
      rw [← f.toNormalization_fromNormalization, reassoc_of% hh, hι, f.ι_fromNormalization,
        ← Spec.map_comp_assoc]
      congr 2
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V.1) (Localization.Away b))) ≫ V.2.fromSpec) := by
      rw [← e]; infer_instance
    haveI := locallyOfFiniteType_of_comp (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V.1) (Localization.Away b)))) V.2.fromSpec
    have := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
    exact RingHom.finiteType_algebraMap.mp this
  have hcov : ∀ x : U, f x ∈ V.1 → ∃ b : B,
      (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j ∧
        j x ∈ ι '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
    intro x hx
    have hx' : j x ∈ Set.range ι := by
      have h1 : j x ∈ f.fromNormalization ⁻¹ᵁ V.1 := by
        show f.fromNormalization (j x) ∈ V.1
        rw [← Scheme.Hom.comp_apply, hj, f.toNormalization_fromNormalization]
        exact hx
      rw [f.fromNormalization_preimage V] at h1
      exact h1
    obtain ⟨y, hy⟩ := hx'
    have hO : IsOpen (ι ⁻¹' Set.range j) := j.isOpenEmbedding.isOpen_range.preimage ι.continuous
    obtain ⟨_, ⟨b, rfl⟩, hyb, hbO⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (show y ∈ ι ⁻¹' Set.range j from ⟨x, hy.symm⟩) hO
    exact ⟨b, hbO, y, hyb, hy⟩
  have hK : IsCompact (f ⁻¹' (V.1 : Set X)) := f.isCompact_preimage V.2.isCompact
  let T := {b : B // (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j}
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun b : T => j ⁻¹' (ι '' (PrimeSpectrum.basicOpen b.1 : Set (PrimeSpectrum B))))
    (fun b => (ι.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen b.1).2).preimage
      j.continuous)
    (by
      intro x hx
      obtain ⟨b, hb, hxb⟩ := hcov x hx
      exact Set.mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩)
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro b hb
    obtain ⟨b', -, rfl⟩ := Finset.mem_image.1 hb
    exact key b'.1 b'.2
  · intro x hx
    obtain ⟨b, hbt, hxb⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact ⟨b.1, Finset.mem_image_of_mem _ hbt, hxb⟩

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalization_basicOpen_cover' : ∀ (U X : Scheme.{0}) (f : U ⟶ X), ∀ [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (V : X.AffineZariskiSite), ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)), (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra; Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧ ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈ f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by
  atlas_forward_decl GlobalTheory.normalization_basicOpen_cover
end

section
section
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

namespace GlobalTheory

theorem awayMap_bijective_of_range_eq_subalgebra :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by
  intro R A B _ _ _ _ C φ hφ hC a b hab hloc
  subst hab
  have hmem : ∀ y, φ y ∈ C := fun y => (hC _).2 ⟨y, rfl⟩
  let f : A →+* C := φ.codRestrict C.toSubsemiring hmem
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => hφ (congrArg Subtype.val h), fun c => ?_⟩
    obtain ⟨y, hy⟩ := (hC c.1).1 c.2
    exact ⟨y, Subtype.ext hy⟩
  let e : A ≃+* C := RingEquiv.ofBijective f hf
  have H : Submonoid.map e.toMonoidHom (Submonoid.powers a) = Submonoid.powers (f a) :=
    Submonoid.map_powers e.toMonoidHom a
  have h1 : Function.Bijective (Localization.awayMap f a) := by
    have hb := (IsLocalization.ringEquivOfRingEquiv (Localization.Away a)
      (Localization.Away (f a)) e H).bijective
    have key : ∀ z, Localization.awayMap f a z =
        IsLocalization.ringEquivOfRingEquiv (Localization.Away a) (Localization.Away (f a)) e H z := by
      intro z
      rw [IsLocalization.ringEquivOfRingEquiv_apply]
      rfl
    rw [show (Localization.awayMap f a : Localization.Away a → Localization.Away (f a)) = _ from funext key]
    exact hb
  have h2 : Localization.awayMap φ a =
      (Localization.awayMap C.val.toRingHom (f a)).comp (Localization.awayMap f a) := by
    simp only [Localization.awayMap, IsLocalization.Away.map]
    rw [IsLocalization.map_comp_map]
    rfl
  rw [h2]
  exact (hloc (hmem a)).comp h1

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by
  atlas_forward_decl GlobalTheory.awayMap_bijective_of_range_eq_subalgebra
end

section
section
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
namespace GlobalTheory.ZMTFin

theorem exists_glued_map (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F')
    (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F) (hι : α' ≫ ι = α) :
    ∃ g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued,
      g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase ∧
      ∀ V, (relativeGluingData hα).cover.f V ≫ g =
        Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V := by
  haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  let η : (relativeGluingData hα).functor ⟶ (relativeGluingData hα').functor :=
    { app V := Spec.map (ι.app (Opposite.op V))
      naturality U V i := by
        dsimp [relativeGluingData]
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        exact (ι.naturality i.op).symm }
  refine ⟨colimMap η, ?_, ?_⟩
  · apply colimit.hom_ext; intro V
    rw [ι_colimMap_assoc, Scheme.Cover.RelativeGluingData.ι_toBase, Scheme.Cover.RelativeGluingData.ι_toBase]
    subst hι
    show Spec.map (ι.app _) ≫ (Spec.map (α'.app (Opposite.op V)) ≫ (restrictIsoSpec X).inv.app V) ≫ (V.1).ι =
      (Spec.map ((α' ≫ ι).app (Opposite.op V)) ≫ (restrictIsoSpec X).inv.app V) ≫ (V.1).ι
    rw [NatTrans.comp_app, Spec.map_comp]; exact (Category.assoc _ _ _).symm
  · intro V
    exact ι_colimMap η V

theorem isIso_morphismRestrict_iSup {Z T : Scheme.{0}} (g : Z ⟶ T) {ι : Type} (W : ι → T.Opens)
    (hW : ∀ i, IsIso (g ∣_ W i)) : IsIso (g ∣_ ⨆ i, W i) := by
  let 𝒰 := Scheme.Opens.iSupOpenCover W
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr fun x ↦ ?_
  refine (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
    ((morphismRestrictRestrict ..).symm ≪≫ morphismRestrictOpensRange ..)).mp ?_
  have : Scheme.Opens.ι _ ''ᵁ (𝒰.f x).opensRange = W x := by
    simp only [Scheme.Opens.iSupOpenCover, 𝒰, ← Scheme.Hom.opensRange_comp, Scheme.homOfLE_ι, Scheme.Opens.opensRange_ι]
  convert! hW x

theorem isOpenImmersion_comp_of_isIso_restrict {U Z T : Scheme.{0}} (h : U ⟶ Z) (g : Z ⟶ T)
    (W : T.Opens) [IsOpenImmersion h] (hg : IsIso (g ∣_ W)) (hr : Set.range h ⊆ (g ⁻¹ᵁ W : Set Z)) :
    IsOpenImmersion (h ≫ g) := by
  let h' : U ⟶ (g ⁻¹ᵁ W).toScheme := IsOpenImmersion.lift (g ⁻¹ᵁ W).ι h (by simpa using hr)
  have e : h = h' ≫ (g ⁻¹ᵁ W).ι := (IsOpenImmersion.lift_fac _ _ _).symm
  have : IsOpenImmersion (h' ≫ (g ⁻¹ᵁ W).ι) := by rw [← e]; infer_instance
  have : IsOpenImmersion h' := IsOpenImmersion.of_comp h' (g ⁻¹ᵁ W).ι
  rw [e, Category.assoc, ← morphismRestrict_ι]
  infer_instance

theorem toBase_of_Spec (X : Scheme.{0}) (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (h : α'.Coequifibered)
    (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ V, P (Spec.map (α'.app V))) : P (relativeGluingData h).toBase := by
  haveI : ((relativeGluingData h).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
  intro U
  let V0 : X.AffineZariskiSite := ⟨U.1, U.2⟩
  haveI : IsOpenImmersion ((relativeGluingData h).cover.f V0) := (relativeGluingData h).cover.map_prop V0
  have hpre : (relativeGluingData h).toBase ⁻¹ᵁ U.1 =
      ((relativeGluingData h).cover.f V0).opensRange := by
    simpa using! (relativeGluingData h).toBase_preimage_eq_opensRange_ι V0
  let e := IsOpenImmersion.isoOfRangeEq ((relativeGluingData h).toBase ⁻¹ᵁ U.1).ι
    ((relativeGluingData h).cover.f V0) (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← hpre])
  have hU : IsAffineOpen U.1 := U.2
  haveI : Mono hU.fromSpec := inferInstance
  have key : e.inv ≫ ((relativeGluingData h).toBase ∣_ U.1) ≫ hU.isoSpec.hom =
      Spec.map (α'.app (Opposite.op V0)) := by
    apply (cancel_mono hU.fromSpec).mp
    have := (relativeGluingData h).ι_toBase V0
    simp [IsAffineOpen.isoSpec_hom, e]
    refine (congrArg (· ≫ (relativeGluingData h).toBase) (IsOpenImmersion.isoOfRangeEq_inv_fac ((relativeGluingData h).toBase ⁻¹ᵁ U.1).ι ((relativeGluingData h).cover.f V0) (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← hpre]))).trans ?_
    refine this.trans ?_
    show (Spec.map (α'.app (Opposite.op V0)) ≫ hU.isoSpec.inv) ≫ U.1.ι = _
    exact (Category.assoc _ _ _).trans (congrArg (Spec.map (α'.app (Opposite.op V0)) ≫ ·) (IsAffineOpen.isoSpec_inv_ι hU))
  rw [← MorphismProperty.cancel_left_of_respectsIso P e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso P _ hU.isoSpec.hom, Category.assoc, key]
  exact hP _

set_option backward.isDefEq.respectTransparency false in

theorem isFinite_toBase (X : Scheme.{0}) (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (h : α'.Coequifibered)
    (hfin : ∀ V, (α'.app V).hom.Finite) : IsFinite (relativeGluingData h).toBase := by
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨toBase_of_Spec X F' α' h (@IsIntegralHom : MorphismProperty Scheme.{0}) fun V ↦ IsIntegralHom.SpecMap_iff.mpr (hfin V).to_isIntegral,
    toBase_of_Spec X F' α' h (@LocallyOfFiniteType : MorphismProperty Scheme.{0}) fun V ↦
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr (hfin V).finiteType⟩

theorem isIso_restrict_basicOpen (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F')
    (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F) (hι : α' ≫ ι = α)
    (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued)
    (hg₁ : g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase)
    (hg₂ : ∀ V, (relativeGluingData hα).cover.f V ≫ g =
      Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V)
    (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V))
    (hb : Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b))
    (W : (relativeGluingData hα').glued.Opens)
    (hW : (W : Set (relativeGluingData hα').glued) =
      (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V))))) :
    IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) =
      (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) :
        Set (PrimeSpectrum (F.obj (Opposite.op V)))) :=
  GlobalTheory.T.relSpec_map_isIso_over_basicOpen_alt X F F' α α' hα hα' ι hι g hg₁ hg₂ V b hb W hW

theorem exists_basicOpen_cover (U X : Scheme.{0}) (f : U ⟶ X) (h₁ : IsSeparated f)
    (h₂ : LocallyOfFiniteType f) (h₃ : QuasiCompact f) (h₄ : LocallyQuasiFinite f)
    (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈
        f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) :=
  GlobalTheory.T.normalization_basicOpen_cover' U X f V

theorem bijective_awayMap_of_range (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B] (C : Subalgebra R B) (φ : A →+* B) (hφ : Function.Injective φ)
    (hC : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B) (hab : φ a = b)
    (h : ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) :
    Function.Bijective (Localization.awayMap φ a) :=
  GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra R A B C φ hφ hC a b hab h

set_option backward.isDefEq.respectTransparency false in

theorem exists_finite_openImmersion : ∀ (U X : Scheme.{0}) (f : U ⟶ X), IsNoetherian X →
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → LocallyQuasiFinite f →
    ∃ (T : Scheme.{0}) (q : T ⟶ X) (j : U ⟶ T), IsFinite q ∧ IsOpenImmersion j ∧ j ≫ q = f := by
  intro U X f hX h₁ h₂ h₃ h₄
  obtain ⟨t, ht⟩ : ∃ t : Finset X.affineOpens, ∀ x : X, ∃ W ∈ t, x ∈ (W : X.Opens) := by
    obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
      (fun W : X.affineOpens ↦ ((W : X.Opens) : Set X)) (fun W ↦ (W : X.Opens).2) (fun x _ ↦ by
        obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
        exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩)
    exact ⟨t, fun x ↦ by simpa using ht (Set.mem_univ x)⟩
  let n := t.card
  let V : Fin n → X.AffineZariskiSite := fun k ↦ ⟨(t.equivFin.symm k).1.1, (t.equivFin.symm k).1.2⟩
  have hV : ∀ x : X, ∃ k, x ∈ (V k).1 := fun x ↦ by
    obtain ⟨W, hWt, hxW⟩ := ht x
    exact ⟨t.equivFin ⟨W, hWt⟩, by simpa [V] using hxW⟩
  choose G hGfin hGcov using fun k ↦ exists_basicOpen_cover U X f h₁ h₂ h₃ h₄ (V k)
  have hs : ∀ k, ∃ s : Finset (f.normalizationDiagram.obj (Opposite.op (V k).1)),
      (G k : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ s ∧
      letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
      ∀ C : Subalgebra Γ(X, (V k).1) (f.normalizationDiagram.obj (Opposite.op (V k).1)),
        (s : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ (C : Set _) → ∀ b ∈ G k, ∀ hb : b ∈ C,
          Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
    intro k
    letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
    exact GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge _ _ (G k) (hGfin k)
  choose s hGs hsC using hs
  have hint : ∀ W : X.Opens, IsAffineOpen W →
      (f.normalizationDiagramMap.app (Opposite.op W)).hom.IsIntegral := by
    intro W _
    letI := (f.app W).hom.toAlgebra
    change (algebraMap Γ(X, W) (integralClosure Γ(X, W) Γ(U, f ⁻¹ᵁ W))).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  obtain ⟨F', α', ι, hα', hι, hιinj, hfin, hιS⟩ := GlobalTheory.T.exists_finite_coequifibered_subalgebra_alt X hX f.normalizationDiagram
    f.normalizationDiagramMap f.coequifibered_normalizationDiagramMap hint n V s
  obtain ⟨g, hg₁, hg₂⟩ := exists_glued_map X _ F' _ α' f.coequifibered_normalizationDiagramMap hα' ι hι
  refine ⟨_, (relativeGluingData hα').toBase, f.toNormalization ≫ g,
    isFinite_toBase X F' α' hα' hfin, ?_, ?_⟩
  rotate_left
  · rw [Category.assoc, hg₁]; exact f.toNormalization_fromNormalization
  choose b' hb' using fun (k : Fin n) (b : G k) ↦ hιS k b.1 (hGs k b.2)
  haveI : ∀ k, IsOpenImmersion ((relativeGluingData hα').cover.f (V k)) :=
    fun k ↦ (relativeGluingData hα').cover.map_prop _
  let Wp : (Σ k, G k) → (relativeGluingData hα').glued.Opens := fun p ↦
    (relativeGluingData hα').cover.f (V p.1) ''ᵁ PrimeSpectrum.basicOpen (b' p.1 p.2)
  have hbij : ∀ p : Σ k, G k, Function.Bijective
      (Localization.awayMap (ι.app (Opposite.op (V p.1))).hom (b' p.1 p.2)) := by
    rintro ⟨k, b⟩
    letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
    let C : Subalgebra Γ(X, (V k).1) (f.normalizationDiagram.obj (Opposite.op (V k).1)) :=
      { (ι.app (Opposite.op (V k))).hom.range with
        algebraMap_mem' := fun r ↦ ⟨(α'.app (Opposite.op (V k))).hom r, by
          rw [← CommRingCat.comp_apply, ← NatTrans.comp_app, hι]; rfl⟩ }
    have hsub : ((s k : Finset _) : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ (C : Set _) :=
      fun x hx ↦ by obtain ⟨y, hy⟩ := hιS k x hx; exact ⟨y, hy⟩
    have hC : ∀ x, x ∈ C ↔ ∃ y, (ι.app (Opposite.op (V k))).hom y = x := fun x ↦ Iff.rfl
    have hB := hsC k C hsub b.1 b.2
    have hφ : Function.Injective (ι.app (Opposite.op (V k))).hom := hιinj _
    exact bijective_awayMap_of_range Γ(X, (V k).1) (F'.obj (Opposite.op (V k)))
      (f.normalizationDiagram.obj (Opposite.op (V k).1)) C (ι.app _).hom hφ hC (b' k b) b.1
      (hb' k b) hB
  have hiso := fun p : Σ k, G k ↦ isIso_restrict_basicOpen X _ F' _ α'
    f.coequifibered_normalizationDiagramMap hα' ι hι g hg₁ hg₂ (V p.1) (b' p.1 p.2) (hbij p)
    (Wp p) rfl
  refine isOpenImmersion_comp_of_isIso_restrict f.toNormalization g (⨆ p, Wp p)
    (isIso_morphismRestrict_iSup g Wp fun p ↦ (hiso p).1) ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨k, hk⟩ := hV (f x)
  obtain ⟨b, hbG, hxb⟩ := hGcov k x hk
  have h2 := (hiso ⟨k, ⟨b, hbG⟩⟩).2
  rw [hb' k ⟨b, hbG⟩] at h2
  have h3 : f.toNormalization x ∈ SetLike.coe (g ⁻¹ᵁ Wp ⟨k, ⟨b, hbG⟩⟩) := by rw [h2]; exact hxb
  exact g.preimage_mono (le_iSup Wp ⟨k, ⟨b, hbG⟩⟩) h3

end GlobalTheory.ZMTFin
end

open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_comp_openImmersion_of_quasiFinite : ∀ (U X : Scheme.{0}) (f : U ⟶ X), IsNoetherian X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → LocallyQuasiFinite f → ∃ (T : Scheme.{0}) (q : T ⟶ X) (j : U ⟶ T), IsFinite q ∧ IsOpenImmersion j ∧ j ≫ q = f := by
  atlas_forward_decl GlobalTheory.ZMTFin.exists_finite_openImmersion
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ZmtNbhd

theorem quasiFiniteAt_of_isolated : ∀ (H X : Scheme.{0}) (φ : H ⟶ X), LocallyOfFiniteType φ →
    ∀ (z : H) (O : H.Opens), z ∈ O → (∀ w ∈ O, φ w = φ z → w = z) → φ.QuasiFiniteAt z := by
  intro H X φ _ z O hzO hO
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← (φ.fiberHomeo (φ z)).isOpen_image]
  simp only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
  rw [isOpen_induced_iff]
  refine ⟨O, O.isOpen, ?_⟩
  ext ⟨w, hw⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext (hO w h hw)
  · intro h
    have : w = z := congrArg Subtype.val h
    exact this ▸ hzO

theorem exists_image_of_isOpenImmersion : ∀ (U T X : Scheme.{0}) (j : U ⟶ T) (q : T ⟶ X),
    IsOpenImmersion j → QuasiCompact j → IsFinite q →
    ∃ (X' : Scheme.{0}) (ν : X' ⟶ X) (i : U ⟶ X'), IsFinite ν ∧ IsOpenImmersion i ∧
      i ≫ ν = j ≫ q ∧ IsDominant i ∧ ∀ V : X'.Opens, Function.Injective (i.app V).hom := by
  intro U T X j q _ _ _
  refine ⟨j.image, j.imageι ≫ q, j.toImage, inferInstance, inferInstance, by simp, inferInstance, ?_⟩
  intro V
  exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (C := CommRingCat)
    (F := j.image.sheaf) j.toImage.c V (fun x _ => j.stalkFunctor_toImage_injective x)

theorem exists_finite_openImmersion_nbhd : ∀ (H X : Scheme.{0}) (φ : H ⟶ X), IsNoetherian X → IsSeparated φ → LocallyOfFiniteType φ → QuasiCompact φ → ∀ Z : Set H, (∀ z ∈ Z, ∃ O : H.Opens, z ∈ O ∧ ∀ w ∈ O, φ w = φ z → w = z) → ∃ (H' : H.Opens) (X' : Scheme.{0}) (ν : X' ⟶ X) (i : H'.toScheme ⟶ X'), Z ⊆ H' ∧ IsFinite ν ∧ IsOpenImmersion i ∧ i ≫ ν = H'.ι ≫ φ ∧ IsDominant i ∧ ∀ V : X'.Opens, Function.Injective (i.app V).hom := by
  intro H X φ hX hsep hloft hqc Z hZ
  let H' := φ.quasiFiniteLocus
  have hZH : Z ⊆ (H' : Set H) := fun z hz => by
    obtain ⟨O, hzO, hO⟩ := hZ z hz
    exact quasiFiniteAt_of_isolated H X φ hloft z O hzO hO
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian φ
  have : QuasiCompact H'.ι := inferInstance
  obtain ⟨T, q, j, hq, hj, hjq⟩ := GlobalTheory.T.exists_finite_comp_openImmersion_of_quasiFinite H'.toScheme X (H'.ι ≫ φ) hX inferInstance
    inferInstance inferInstance inferInstance
  have : QuasiCompact j := by
    have : QuasiCompact (j ≫ q) := by rw [hjq]; infer_instance
    exact QuasiCompact.of_comp j q
  obtain ⟨X', ν, i, hν, hi, hiν, hdom, hinj⟩ := exists_image_of_isOpenImmersion H'.toScheme T X j q hj this hq
  exact ⟨H', X', ν, i, hZH, hν, hi, by rw [hiν, hjq], hdom, hinj⟩

end GlobalTheory.ZmtNbhd
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_openImmersion_nbhd_isolatedFibrePoints : ∀ (H X : Scheme.{0}) (φ : H ⟶ X), IsNoetherian X → IsSeparated φ → LocallyOfFiniteType φ → QuasiCompact φ → ∀ Z : Set H, (∀ z ∈ Z, ∃ O : H.Opens, z ∈ O ∧ ∀ w ∈ O, φ w = φ z → w = z) → ∃ (H' : H.Opens) (X' : Scheme.{0}) (ν : X' ⟶ X) (i : H'.toScheme ⟶ X'), Z ⊆ H' ∧ IsFinite ν ∧ IsOpenImmersion i ∧ i ≫ ν = H'.ι ≫ φ ∧ IsDominant i ∧ ∀ V : X'.Opens, Function.Injective (i.app V).hom := by
  atlas_forward_decl GlobalTheory.ZmtNbhd.exists_finite_openImmersion_nbhd
end
