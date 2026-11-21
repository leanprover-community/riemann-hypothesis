import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetEtaleLevelStructureExistsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientDescendsEtaleSurjectiveCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeomPtRangeEq
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfGeometricPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtSetOfLists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndEtaleOfCompOfFiniteEtaleCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsogOfSurjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientClassifyingMapIsogenyUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEtaleHasHeckeQuotientNoetherianDomain

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkTuple

theorem exists_equiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S) (hg : T.hom ≫ f = g) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk g ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  subst hg
  exact GlobalTheory.HkSetPull.exists_equiv h T

theorem exists_tuples {S : Scheme.{0}} (G : Over S) [GrpObj G] (N n : ℕ) (hG : IsAbelianScheme G)
    (hn : IsUnit (N : Γ(S, ⊤))) :
    ∃ (Z : Scheme.{0}) (a : Z ⟶ S) (x : Fin n → (Over.mk a ⟶ G)), IsFinite a ∧ Etale a ∧ (∀ j, x j ^ N = 1) ∧
      ∀ (T : Over S) (y : Fin n → (T ⟶ G)), (∀ j, y j ^ N = 1) → ∃! h : T ⟶ Over.mk a, ∀ j, h ≫ x j = y j := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  have key : ∃ (Z : Over S) (x : Fin n → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ j, x j ^ N = 1) ∧
      ∀ (T : Over S) (y : Fin n → (T ⟶ G)), (∀ j, y j ^ N = 1) → ∃! h : T ⟶ Z, ∀ j, h ≫ x j = y j := by
    refine ⟨Out.powObj (torsion G N) n, fun i => Out.powPr (torsion G N) i ≫ torsion.ι G N,
      LatticeTorsion.prop_powObj @IsFinite _ hfin n, LatticeTorsion.prop_powObj @Etale _ het n, fun i => ?_,
      fun T y' hy' => ?_⟩
    · rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
    · choose y hy hyu using fun i : Fin n => LatticeTorsion.existsUnique_torsion G N (y' i) (hy' i)
      let h : T ⟶ Out.powObj (torsion G N) n := (Out.powIsLimit (torsion G N) n).lift (Fan.mk T y)
      have hh : ∀ i, h ≫ Out.powPr (torsion G N) i = y i := fun i =>
        (Out.powIsLimit (torsion G N) n).fac (Fan.mk T y) ⟨i⟩
      refine ⟨h, fun i => by rw [← hy i, ← hh i, Category.assoc], fun h' hh' => ?_⟩
      refine (Out.powIsLimit (torsion G N) n).hom_ext fun ⟨i⟩ => ?_
      exact (hyu i _ ((Category.assoc _ _ _).trans (hh' i))).trans (hh i).symm
  obtain ⟨Z, x, h⟩ := key
  exact ⟨Z.left, Z.hom, x, h⟩

theorem eq_of_mem_range {S : Scheme.{0}} {G : Over S} (τ : 𝟙_ (Over S) ⟶ G) {k : Type} [Field k] {x : Sp k ⟶ S}
    (z : Over.mk x ⟶ G) (u : Sp k) (hu : z.left u ∈ Set.range τ.left) : z = toUnit _ ≫ τ := by
  have w : τ.left ≫ G.hom = 𝟙 S := Over.w _
  have i₁ : IsImmersion τ.left := by
    have : IsImmersion (τ.left ≫ G.hom) := by rw [w]; exact inferInstanceAs (IsImmersion (𝟙 S))
    exact IsImmersion.of_comp _ G.hom
  have r : Set.range (pullback.fst z.left τ.left) = Set.univ := by
    rw [Scheme.Pullback.range_fst]
    refine Set.eq_univ_of_forall fun v => ?_
    rw [show v = u from Subsingleton.elim (α := PrimeSpectrum k) _ _]
    exact hu
  have i₂ : IsClosedImmersion (pullback.fst z.left τ.left) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [r]; exact isClosed_univ)
  have i₃ : Surjective (pullback.fst z.left τ.left) := ⟨Set.range_eq_univ.1 r⟩
  have i₄ : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have i₅ : IsIso (pullback.fst z.left τ.left) := isIso_of_isClosedImmersion_of_surjective _
  refine Over.OverMorphism.ext ?_
  have tu : (toUnit (Over.mk x)).left = x := by simp
  have wz : z.left ≫ G.hom = x := Over.w _
  rw [Over.comp_left, tu, ← cancel_epi (pullback.fst z.left τ.left)]
  have e : pullback.fst z.left τ.left ≫ z.left ≫ G.hom ≫ τ.left = pullback.fst z.left τ.left ≫ z.left := by
    rw [pullback.condition_assoc, reassoc_of% w, pullback.condition]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ.left) (Category.comp_id _))
  rw [← e, reassoc_of% wz]

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} {n : ℕ} (τ : Fin n → (𝟙_ (Over S) ⟶ G)) {k : Type} [Field k]
    {x : Sp k ⟶ S} (z : Over.mk x ⟶ G) :
    Set.range z.left ⊆ (⋃ j, Set.range (τ j).left) ↔ z ∈ Set.range fun j => toUnit (Over.mk x) ≫ τ j := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨(default : PrimeSpectrum k), rfl⟩)
    exact ⟨j, (eq_of_mem_range (τ j) z _ hj).symm⟩
  · rintro ⟨j, rfl⟩ _ ⟨u, rfl⟩
    refine Set.mem_iUnion.2 ⟨j, (toUnit (Over.mk x)).left u, ?_⟩
    exact (Scheme.Hom.comp_apply _ _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem listed_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (D : Datum H) (P : Ideal (𝓞 E))
    (p i : ℕ) (m : SABMap t' t f) {n : ℕ} (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)) (τ : Fin n → (𝟙_ (Over S') ⟶ t'.G))
    (e : ∀ j, (τ j).left ≫ m.φ = f ≫ (σ j).left) {k : Type} [Field k] (x : Sp k ⟶ S') :
    ((Function.Injective fun j => x ≫ (τ j).left) ∧ ∃ C : Subgroup (Over.mk x ⟶ t'.G),
      (C : Set _) = Set.range (fun j => toUnit (Over.mk x) ≫ τ j) ∧ t'.HeckeKer (Over.mk x) D P p i C) ↔
    ((Function.Injective fun j => (x ≫ f) ≫ (σ j).left) ∧ ∃ C : Subgroup (Over.mk (x ≫ f) ⟶ t.G),
      (C : Set _) = Set.range (fun j => toUnit (Over.mk (x ≫ f)) ≫ σ j) ∧
        t.HeckeKer (Over.mk (x ≫ f)) D P p i C) := by
  obtain ⟨ρ, e₀⟩ := exists_equiv m.cart (Over.mk x) (x ≫ f) rfl
  have tu : (toUnit (Over.mk x)).left = x := by simp
  have tu' : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := by simp
  have l₁ : ∀ j, (toUnit (Over.mk x) ≫ τ j).left = x ≫ (τ j).left := fun j => by rw [Over.comp_left, tu]
  have l₂ : ∀ j, (toUnit (Over.mk (x ≫ f)) ≫ σ j).left = (x ≫ f) ≫ (σ j).left := fun j => by
    rw [Over.comp_left, tu']
  have e₁ : ∀ j, ρ (toUnit (Over.mk x) ≫ τ j) = toUnit (Over.mk (x ≫ f)) ≫ σ j := fun j =>
    Over.OverMorphism.ext (by
      rw [e₀, l₁, l₂]
      exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) (e j)).trans (Category.assoc _ _ _).symm))
  have mem : ∀ u, u ∈ Set.range (fun j => toUnit (Over.mk x) ≫ τ j) ↔
      ρ u ∈ Set.range (fun j => toUnit (Over.mk (x ≫ f)) ≫ σ j) := fun u =>
    exists_congr fun j => by beta_reduce; rw [← e₁]; exact ρ.injective.eq_iff.symm
  have eq : ∀ (u : Over.mk x ⟶ t'.G) (v : Over.mk (x ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → v = ρ u :=
    fun u v h => Over.OverMorphism.ext (h.trans (e₀ u).symm)
  refine and_congr (forall₂_congr fun a b => imp_congr_left ?_) ⟨?_, ?_⟩
  · beta_reduce
    rw [← l₁, ← l₁, ← l₂, ← l₂]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← e₁, ← e₁, Over.OverMorphism.ext h]
    · have := Over.OverMorphism.ext h
      rw [← e₁, ← e₁] at this
      rw [ρ.injective this]
  · rintro ⟨C', h₁, h₂⟩
    refine ⟨C'.comap ρ.symm.toMonoidHom, Set.ext fun v => ?_,
      (GlobalTheory.HkSetPull.heckeKer_iff D P p i m (Over.mk x) C' _ fun u v h => ?_).1 h₂⟩
    · obtain ⟨u, rfl⟩ := ρ.surjective v
      rw [← mem, ← h₁]
      show ρ.symm (ρ u) ∈ C' ↔ _
      rw [ρ.symm_apply_apply]
      rfl
    · rw [eq u v h]
      show _ ↔ ρ.symm (ρ u) ∈ C'
      rw [ρ.symm_apply_apply]
  · rintro ⟨C, h₁, h₂⟩
    refine ⟨C.comap ρ.toMonoidHom, Set.ext fun u => ?_,
      (GlobalTheory.HkSetPull.heckeKer_iff D P p i m (Over.mk x) _ C fun u v h => ?_).2 h₂⟩
    · rw [mem, ← h₁]
      rfl
    · rw [eq u v h]
      rfl

theorem range_subset_of_geom {T Z : Scheme.{0}} (h : T ⟶ Z) (V : Set Z)
    (hV : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), Set.range (x ≫ h) ⊆ V) : Set.range h ⊆ V := by
  rintro _ ⟨y, rfl⟩
  let k := AlgebraicClosure (T.residueField y)
  let z : Sp k ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap (T.residueField y) k)) ≫ T.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  exact hV k z ⟨(default : PrimeSpectrum k), (Scheme.Hom.comp_apply _ _ _).trans (congrArg h (hz _))⟩

end GlobalTheory.HkTuple

open GlobalTheory.HkTuple in

theorem GlobalTheory.exists_finiteEtale_heckeLists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s), admitted l 𝔓 p → ∃ (Y : Scheme.{0}) (a : Y ⟶ S) (oY : Ob D l (a ≫ s)) (m : ObjMap oY o a) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite a ∧ Etale a ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t : SAB H T) (mu : SABMap t o.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃! h : T ⟶ Y, h ≫ a = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  intro E _ _ _ H D l P p i n S s o adm
  have hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have := ((baseKA l).unit (p ^ 2) (pow_pos adm.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  have specMap_id₂ : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  obtain ⟨Z, b, x, hf, he, hx, huniv⟩ := exists_tuples o.t.G (p ^ 2) n (GlobalTheory.ObjDim.isAbelianScheme o) hu
  obtain ⟨oZ, ⟨mZ⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S Z s (b ≫ s) b rfl rfl
    (by rw [specMap_id₂, Category.comp_id]) o
  obtain ⟨ρ, e₀⟩ := exists_equiv mZ.cart (𝟙_ (Over Z)) b (Category.id_comp b)
  let σZ : Fin n → (𝟙_ (Over Z) ⟶ oZ.t.G) := fun j => ρ.symm (x j)
  have eZ : ∀ j, (σZ j).left ≫ mZ.toSABMap.φ = (x j).left := fun j => by
    rw [← e₀, ρ.apply_symm_apply]
  have pZ : ∀ j, σZ j ^ p ^ 2 = 1 := fun j => by rw [← map_pow, hx, map_one]
  obtain ⟨V, hc, hV⟩ := GlobalTheory.T.exists_clopen_locus_torsionSections_heckeKernel E H D l P p i n Z (b ≫ s) oZ σZ adm pZ
  obtain ⟨oY, ⟨mY⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) Z V (b ≫ s) ((V.ι ≫ b) ≫ s) V.ι
    rfl rfl (by rw [specMap_id₂, Category.comp_id, Category.assoc]) oZ
  obtain ⟨m, hm⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o oZ oY).2 b V.ι mZ).1 mY
  obtain ⟨ρ', e₀'⟩ := exists_equiv mY.cart (𝟙_ (Over V.toScheme)) V.ι (Category.id_comp _)
  let σ : Fin n → (𝟙_ (Over V.toScheme) ⟶ oY.t.G) := fun j => ρ'.symm (toUnit _ ≫ σZ j)
  have tu : (toUnit (Over.mk V.ι)).left = V.ι := by simp
  have eY : ∀ j, (σ j).left ≫ mY.toSABMap.φ = V.ι ≫ (σZ j).left := fun j => by
    rw [← e₀', ρ'.apply_symm_apply, Over.comp_left, tu]
  have eσ : ∀ j, (σ j).left ≫ m.toSABMap.φ = V.ι ≫ (x j).left := fun j => by
    rw [hm, ← eZ]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ mZ.toSABMap.φ) (eY j)).trans (Category.assoc _ _ _))
  have hY := fun (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ V.toScheme) =>
    (listed_iff D P p i mY.toSABMap σZ σ eY y).2 ((hV k (y ≫ V.ι)).1 (by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact (y u).2))
  have ci : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  refine ⟨V, V.ι ≫ b, oY, m, σ, ⋃ j, Set.range (σ j).left, inferInstance, inferInstance,
    ⟨fun j => ?_, rfl, fun k _ _ y => (hY k y).1⟩, fun k _ _ y => ?_, ?_⟩
  · rw [← map_pow, ← MonObj.comp_pow, pZ, MonObj.comp_one, map_one]
  · obtain ⟨C, h₁, h₂⟩ := (hY k y).2
    exact ⟨C, fun z => by rw [range_subset_iff, ← h₁]; rfl, h₂⟩
  · rintro T f t mu τ K' ⟨hτ, rfl, hinj⟩ hK
    obtain ⟨ρ₂, e₂⟩ := exists_equiv mu.cart (𝟙_ (Over T)) f (Category.id_comp _)
    obtain ⟨h₀, hh₀, hh₀u⟩ := huniv (Over.mk f) (fun j => ρ₂ (τ j)) (fun j => by rw [← map_pow, hτ, map_one])
    have e₃ : ∀ j, h₀.left ≫ (x j).left = (τ j).left ≫ mu.φ := fun j => by
      rw [← e₂, ← hh₀, Over.comp_left]
    have uq : ∀ g : T ⟶ Z, g ≫ b = f → (∀ j, g ≫ (x j).left = (τ j).left ≫ mu.φ) → g = h₀.left := fun g w hg =>
      congrArg (·.left) (hh₀u (Over.homMk g w) fun j => Over.OverMorphism.ext ((hg j).trans (e₂ _).symm))
    obtain ⟨g, w, e₄, uq'⟩ : ∃ g : T ⟶ Z, g ≫ b = f ∧ (∀ j, g ≫ (x j).left = (τ j).left ≫ mu.φ) ∧
        ∀ g' : T ⟶ Z, g' ≫ b = f → (∀ j, g' ≫ (x j).left = (τ j).left ≫ mu.φ) → g' = g :=
      ⟨h₀.left, Over.w h₀, e₃, uq⟩
    clear uq e₃ hh₀u hh₀ h₀ e₂ ρ₂
    subst w
    obtain ⟨mu', hmu⟩ := GlobalTheory.ObjMaps.exists_sab_cancel mZ.toSABMap mu
    have e₅ : ∀ j, (τ j).left ≫ mu'.φ = g ≫ (σZ j).left := fun j => by
      have w₁ : (τ j).left ≫ t.G.hom = 𝟙 T := Over.w _
      have w₂ : (σZ j).left ≫ oZ.t.G.hom = 𝟙 Z := Over.w _
      refine mZ.cart.1.hom_ext ?_ ?_
      · exact (Category.assoc _ _ _).trans ((congrArg ((τ j).left ≫ ·) hmu.symm).trans ((e₄ j).symm.trans
          ((congrArg (g ≫ ·) (eZ j).symm).trans (Category.assoc _ _ _).symm)))
      · exact (Category.assoc _ _ _).trans ((congrArg ((τ j).left ≫ ·) mu'.cart.1.w).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) w₁).trans ((Category.id_comp g).trans
          ((Category.comp_id g).symm.trans ((congrArg (g ≫ ·) w₂.symm).trans (Category.assoc _ _ _).symm))))))
    have hr : Set.range g ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      refine range_subset_of_geom g _ fun k _ _ y => (hV k (y ≫ g)).2
        ((listed_iff D P p i mu' σZ τ e₅ y).1 ⟨hinj k y, ?_⟩)
      obtain ⟨C, h₁, h₂⟩ := hK k y
      exact ⟨C, Set.ext fun z => (h₁ z).trans (range_subset_iff τ z), h₂⟩
    refine ⟨IsOpenImmersion.lift V.ι g hr, ⟨by rw [IsOpenImmersion.lift_fac_assoc], fun j => ?_⟩, ?_⟩
    · exact (congrArg (IsOpenImmersion.lift V.ι g hr ≫ ·) (eσ j)).trans
        ((IsOpenImmersion.lift_fac_assoc _ _ _ _).trans (e₄ j))
    · rintro h ⟨w, hh⟩
      rw [← cancel_mono V.ι, IsOpenImmersion.lift_fac]
      exact uq' _ ((Category.assoc _ _ _).trans w) fun j =>
        (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) (eσ j).symm).trans (hh j))
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_heckeKernel_lists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s), admitted l 𝔓 p → ∃ (Y : Scheme.{0}) (a : Y ⟶ S) (oY : Ob D l (a ≫ s)) (m : ObjMap oY o a) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite a ∧ Etale a ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t : SAB H T) (mu : SABMap t o.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃! h : T ⟶ Y, h ≫ a = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  atlas_forward_decl GlobalTheory.exists_finiteEtale_heckeLists
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkPerm

theorem lists_perm {S : Scheme.{0}} {G : Over S} [GrpObj G] {N n : ℕ} {σ : Fin n → (𝟙_ (Over S) ⟶ G)}
    {K : Set G.left} (h : Lists N σ K) (g : Equiv.Perm (Fin n)) : Lists N (fun j => σ (g j)) K := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨fun j => h₁ _, ?_, fun k _ _ x => (h₃ k x).comp g.injective⟩
  rw [h₂]
  exact (g.surjective.iUnion_comp (fun j => Set.range (σ j).left)).symm

theorem exists_perm {α : Type} {n : ℕ} {u v : Fin n → α} (hu : Function.Injective u) (hv : Function.Injective v)
    (h : Set.range u = Set.range v) : ∃ g : Equiv.Perm (Fin n), ∀ j, u (g j) = v j := by
  have : ∀ j, ∃ i, u i = v j := fun j => by
    have : v j ∈ Set.range u := h ▸ Set.mem_range_self j
    exact this
  choose g hg using this
  have gi : Function.Injective g := fun a b e => hv (by rw [← hg, ← hg, e])
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 gi), hg⟩

theorem exists_lists_mod_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ), admitted l 𝔓 p → ∃ (Y Hk : Scheme.{0}) (q : Y ⟶ Hk) (π₁ : Hk ⟶ Xo.X) (oY : Ob D l ((q ≫ π₁) ≫ Xo.s)) (m : ObjMap oY Xo.univ (q ≫ π₁)) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite q ∧ Etale q ∧ Surjective q ∧ IsFinite π₁ ∧ Etale π₁ ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q ↔ Set.range (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ) = Set.range (fun j => y' ≫ (σ j).left ≫ m.toSABMap.φ) ∧ y ≫ q ≫ π₁ = y' ≫ q ≫ π₁) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ Xo.X) (t : SAB H T) (mu : SABMap t Xo.univ.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃ h : T ⟶ Y, h ≫ q ≫ π₁ = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  intro E _ _ _ H D l Xo P p i n hA
  obtain ⟨Y, a, oY, m, σ, K, fa, ea, hL, hK, hu⟩ := GlobalTheory.T.exists_finiteEtale_heckeKernel_lists E H D l P p i n Xo.X Xo.s Xo.univ hA
  have hρ := fun g : Equiv.Perm (Fin n) => hu Y a oY.t m.toSABMap (fun j => σ (g j)) K (lists_perm hL g) hK
  choose ρ hρ₁ hρ₂ using hρ
  have r₁ : ∀ g, ρ g ≫ a = a := fun g => (hρ₁ g).1
  have r₂ : ∀ g j, ρ g ≫ (σ j).left ≫ m.toSABMap.φ = (σ (g j)).left ≫ m.toSABMap.φ := fun g => (hρ₁ g).2
  have one : ρ 1 = 𝟙 Y := (hρ₂ 1 _ ⟨by simp, fun j => by simp⟩).symm
  have mul : ∀ g c, ρ (g * c) = ρ g ≫ ρ c := fun g c =>
    (hρ₂ (g * c) _ ⟨by rw [Category.assoc, r₁, r₁], fun j => by
      rw [Category.assoc, r₂, r₂]; rfl⟩).symm
  have inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y),
      Function.Injective fun j => y ≫ (σ j).left ≫ m.toSABMap.φ := by
    intro k _ _ y b c e
    apply hL.2.2 k y
    have w : ∀ j, (σ j).left ≫ oY.t.G.hom = 𝟙 Y := fun j => Over.w _
    refine m.toSABMap.cart.1.hom_ext ?_ ?_
    · simpa only [Category.assoc] using e
    · simp only [Category.assoc, w]
  have free : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (g : Equiv.Perm (Fin n)), y ≫ ρ g = y → g = 1 := by
    intro k _ _ y g e
    ext1 j
    apply inj k y
    change y ≫ (σ (g j)).left ≫ m.toSABMap.φ = y ≫ (σ j).left ≫ m.toSABMap.φ
    rw [← r₂, ← Category.assoc, e]
  have uq : ∀ (T : Scheme.{0}) (y y' : T ⟶ Y), y ≫ a = y' ≫ a →
      (∀ j, y ≫ (σ j).left ≫ m.toSABMap.φ = y' ≫ (σ j).left ≫ m.toSABMap.φ) → y = y' := by
    intro T y y' e₁ e₂
    obtain ⟨_, _, _, _, _, m', -⟩ := sabPull Out.CubePf.cubePull y oY.t
    obtain ⟨mu, hmu⟩ := GlobalTheory.ObjMaps.exists_sab_comp m.toSABMap m'
    obtain ⟨τ, hτ, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m'.cart K _ n σ hL
    have hτ' : ∀ j, y ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := fun j => by
      rw [hmu, ← Category.assoc, ← hτ, Category.assoc]
    exact (hu T (y ≫ a) _ mu τ _ hL' (GlobalTheory.HkSetPull.heckeSet_pull D P p i m' K hK)).unique ⟨rfl, hτ'⟩
      ⟨e₁.symm, fun j => (e₂ j).symm.trans (hτ' j)⟩
  have hq := GlobalTheory.isQProjOver_comp_of_isFinite_noetherian (KA l) Y Xo.X a Xo.s fa Xo.qproj
  obtain ⟨Hk, q, sH, hs, hG, sep, lft, -⟩ := GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver (KA l) Y (a ≫ Xo.s)
    (Equiv.Perm (Fin n)) ρ hq one mul (fun g => by rw [← Category.assoc, r₁]) free
  have hd := (GlobalTheory.ZM.galoisCover_descent Y Hk q _ ρ hG).1
  obtain ⟨π₁, rfl, -⟩ := hd Xo.X a r₁
  have hs' : π₁ ≫ Xo.s = sH := (hd _ ((q ≫ π₁) ≫ Xo.s) (fun g => by rw [← Category.assoc, r₁])).unique
    (Category.assoc _ _ _).symm hs
  subst hs'
  have : IsSeparated π₁ := IsSeparated.of_comp π₁ Xo.s
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : LocallyOfFiniteType π₁ := locallyOfFiniteType_of_comp π₁ Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨f₁, e₁⟩ := isFinite_and_etale_of_comp_of_finite_etale_cover Y Hk Xo.X q π₁ hG.fin hG.etale hG.onto fa ea
    inferInstance inferInstance
  refine ⟨Y, Hk, q, π₁, oY, m, σ, K, hG.fin, hG.etale, hG.onto, f₁, e₁, hL, hK, fun k _ _ y y' => ⟨fun e => ?_, fun e => ?_⟩,
    fun T f t mu τ K' h₁ h₂ => (hu T f t mu τ K' h₁ h₂).exists⟩
  · obtain ⟨g, rfl, -⟩ := hG.fibre k y y' e
    refine ⟨?_, by rw [← Category.assoc, e, Category.assoc]⟩
    simp only [Category.assoc, r₂]
    exact (g.surjective.range_comp (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ)).symm
  · obtain ⟨g, hg⟩ := exists_perm (inj k y) (inj k y') e.1
    have : y ≫ ρ g = y' := uq _ _ _ (by rw [Category.assoc, r₁]; exact e.2) fun j => by
      rw [Category.assoc, r₂]; exact hg j
    rw [← this, Category.assoc, hG.inv]

end GlobalTheory.HkPerm
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernelLists_modulo_permutations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ), admitted l 𝔓 p → ∃ (Y Hk : Scheme.{0}) (q : Y ⟶ Hk) (π₁ : Hk ⟶ Xo.X) (oY : Ob D l ((q ≫ π₁) ≫ Xo.s)) (m : ObjMap oY Xo.univ (q ≫ π₁)) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite q ∧ Etale q ∧ Surjective q ∧ IsFinite π₁ ∧ Etale π₁ ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q ↔ Set.range (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ) = Set.range (fun j => y' ≫ (σ j).left ≫ m.toSABMap.φ) ∧ y ≫ q ≫ π₁ = y' ≫ q ≫ π₁) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ Xo.X) (t : SAB H T) (mu : SABMap t Xo.univ.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃ h : T ⟶ Y, h ≫ q ≫ π₁ = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  atlas_forward_decl GlobalTheory.HkPerm.exists_lists_mod_perm
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam.KerSch

theorem exists_lift_of_finite {k : Type} [Field k] [IsAlgClosed k] {Y Z : Scheme.{0}} (q : Y ⟶ Z)
    [IsFinite q] [Surjective q] (x : Sp k ⟶ Z) : ∃ y : Sp k ⟶ Y, y ≫ q = x := by
  have : CompactSpace ↥(pullback q x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q x)
  obtain ⟨p, -⟩ := (pullback.snd q x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback q x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd q x) z hz ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem exists_lift_ext {k : Type} [Field k] {Y Z : Scheme.{0}} (f : Y ⟶ Z) (u : Sp k ⟶ Z) (t : Sp k) (y₀ : Y)
    (h : f y₀ = u t) : ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (a : Sp k' ⟶ Sp k) (y : Sp k' ⟶ Y),
      Epi a ∧ y ≫ f = a ≫ u := by
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y₀ t h
  obtain ⟨k', _, _, z, -⟩ := exists_geomPt_range_eq (pullback f u) w
  refine ⟨k', inferInstance, inferInstance, z ≫ pullback.snd f u, z ≫ pullback.fst f u, ?_, ?_⟩
  · generalize z ≫ pullback.snd f u = a
    have : Surjective a := ⟨fun x => ⟨(default : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have : Flat a := inferInstance
    exact Flat.epi_of_flat_of_surjective a
  · rw [Category.assoc, Category.assoc, pullback.condition]

section

variable {A X G₁ Z GY Y : Scheme.{0}} {α : A ⟶ X} {g₁ : G₁ ⟶ Z} {gY : GY ⟶ Y} {φ : G₁ ⟶ A} {ψ : GY ⟶ G₁}
  {π : Z ⟶ X} {q : Y ⟶ Z} {n : ℕ} {σ : Fin n → (Y ⟶ GY)}

theorem range_subset_iff (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {k : Type} [Field k] (y : Sp k ⟶ Y) (u : Sp k ⟶ G₁) (hu : u ≫ g₁ = y ≫ q) :
    Set.range u ⊆ ψ '' (⋃ j, Set.range (σ j)) ↔ ∃ j, u = y ≫ σ j ≫ ψ := by
  have hs : ∀ j, σ j ≫ ψ ≫ g₁ = q := fun j => by rw [h₂.w, reassoc_of% hσ j]
  constructor
  · intro h
    obtain ⟨w, hw, e⟩ := h ⟨(default : PrimeSpectrum k), rfl⟩
    obtain ⟨j, y₀, rfl⟩ := Set.mem_iUnion.1 hw
    obtain ⟨k', _, _, a, y', ha, e'⟩ := exists_lift_ext (σ j ≫ ψ) u _ y₀ (by rw [Scheme.Hom.comp_apply]; exact e)
    have e₁ : y' ≫ q = (a ≫ y) ≫ q := by
      rw [Category.assoc, ← hu, ← reassoc_of% e', hs j]
    have e₂ : y' ≫ σ j ≫ ψ ≫ φ ∈ Set.range (fun j => (a ≫ y) ≫ σ j ≫ ψ ≫ φ) := hfib k' _ _ e₁ ▸ ⟨j, rfl⟩
    obtain ⟨j', e₃⟩ := e₂
    refine ⟨j', h₁.hom_ext ?_ ?_⟩
    · rw [← cancel_epi a, ← reassoc_of% e']
      simpa using e₃.symm
    · simp only [Category.assoc, hs, hu]
  · rintro ⟨j, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨σ j (y t), Set.mem_iUnion.2 ⟨j, _, rfl⟩, by simp⟩

theorem preimage_eq (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {GT T : Scheme.{0}} {gT : GT ⟶ T} {ν : GT ⟶ G₁} {h : T ⟶ Y} (h₃ : IsPullback ν gT g₁ (h ≫ q))
    {τ : Fin n → (T ⟶ GT)} (hτ : ∀ j, τ j ≫ gT = 𝟙 T) (hh : ∀ j, τ j ≫ ν = h ≫ σ j ≫ ψ) :
    (⋃ j, Set.range (τ j)) = ν ⁻¹' (ψ '' (⋃ j, Set.range (σ j))) := by
  ext w
  constructor
  · intro hw
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.1 hw
    refine ⟨σ j (h t), Set.mem_iUnion.2 ⟨j, _, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hh]
  · intro hw
    obtain ⟨k, _, _, z, hz⟩ := exists_geomPt_range_eq GT w
    have hzw : ∀ t, z t = w := fun t => by
      have : z t ∈ Set.range z := ⟨_, rfl⟩
      rwa [hz] at this
    obtain ⟨t₀⟩ : Nonempty (Sp k) := ⟨(default : PrimeSpectrum k)⟩
    obtain ⟨j, e⟩ := (range_subset_iff h₁ h₂ hσ hfib (z ≫ gT ≫ h) (z ≫ ν) (by simp [h₃.w])).1 (by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Hom.comp_apply, hzw]
      exact hw)
    have e' : z = z ≫ gT ≫ τ j := h₃.hom_ext (by simp [e, hh]) (by simp [hτ])
    refine Set.mem_iUnion.2 ⟨j, gT w, ?_⟩
    rw [← hzw t₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← e']

theorem range_subset_range (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {k : Type} [Field k] (y y' : Sp k ⟶ Y) (e : y ≫ q ≫ π = y' ≫ q ≫ π)
    (H : ∀ u u' : Sp k ⟶ G₁, u ≫ g₁ = y ≫ q → u' ≫ g₁ = y' ≫ q → u ≫ φ = u' ≫ φ →
      Set.range u ⊆ ψ '' (⋃ j, Set.range (σ j)) → Set.range u' ⊆ ψ '' (⋃ j, Set.range (σ j))) :
    Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) ⊆ Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ) := by
  have hs : ∀ j, σ j ≫ ψ ≫ g₁ = q := fun j => by rw [h₂.w, reassoc_of% hσ j]
  rintro _ ⟨j, rfl⟩
  have w : (y ≫ σ j ≫ ψ ≫ φ) ≫ α = (y' ≫ q) ≫ π := by
    simp only [Category.assoc, h₁.w, reassoc_of% hs, e]
  have hu : (y ≫ σ j ≫ ψ) ≫ g₁ = y ≫ q := by simp only [Category.assoc, hs]
  have := H (y ≫ σ j ≫ ψ) (h₁.lift _ _ w) hu (h₁.lift_snd _ _ _) (by simp)
    ((range_subset_iff h₁ h₂ hσ hfib y _ hu).2 ⟨j, rfl⟩)
  obtain ⟨j', e'⟩ := (range_subset_iff h₁ h₂ hσ hfib y' _ (h₁.lift_snd _ _ w)).1 this
  refine ⟨j', ?_⟩
  have := h₁.lift_fst _ _ w
  rw [e'] at this
  simpa using this

end

end GlobalTheory.HkFam.KerSch

namespace GlobalTheory.HkFam

open KerSch

theorem exists_heckeKernelScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ (Hk : Scheme.{0}) (π₁ : Hk ⟶ Xo.X) (o₁ : Ob D l (π₁ ≫ Xo.s)) (m₁ : ObjMap o₁ Xo.univ π₁) (K : Set o₁.t.G.left), IsFinite π₁ ∧ Etale π₁ ∧ HeckeSet D o₁.t 𝔓 p i K ∧ EtSet o₁.t.G K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Hk) (z' : Sp k ⟶ Hk), z ≫ π₁ = z' ≫ π₁ → (∀ (u : Over.mk z ⟶ o₁.t.G) (u' : Over.mk z' ⟶ o₁.t.G), u.left ≫ m₁.toSABMap.φ = u'.left ≫ m₁.toSABMap.φ → (Set.range u.left ⊆ K ↔ Set.range u'.left ⊆ K)) → z = z') ∧ ∀ (T : Scheme.{0}) (s : T ⟶ Sp (KA l)) (o : Ob D l s) (f : T ⟶ Xo.X) (mu : ObjMap o Xo.univ f) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over T) ⟶ o.t.G)) (K' : Set o.t.G.left), Lists (p ^ 2) τ K' → HeckeSet D o.t 𝔓 p i K' → ∃ (h : T ⟶ Hk) (n : ObjMap o o₁ h), h ≫ π₁ = f ∧ n.toSABMap.φ ≫ m₁.toSABMap.φ = mu.toSABMap.φ ∧ K' = n.toSABMap.φ ⁻¹' K := by
  intro E _ _ _ H D l Xo 𝔓 p i hA
  obtain ⟨Y, Hk, q, π₁, oY, m, σ, K, hqf, hqe, hqs, hπf, hπe, hL, hK, hfib, huniv⟩ :=
    GlobalTheory.T.exists_heckeKernelLists_modulo_permutations E H D l Xo 𝔓 p i (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) hA
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (π₁ ≫ Xo.s) π₁ rfl rfl
    (by simp [spMap]) Xo.univ
  obtain ⟨m', hm'⟩ := ((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ oY).2 π₁ q m₁).2 m
  have h₁ := m₁.cart.1
  have h₂ := m'.cart.1
  have hσ : ∀ j, (σ j).left ≫ oY.t.G.hom = 𝟙 Y := fun j => Over.w (σ j)
  rw [hm'] at hfib
  have hfib' := fun (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y) e => ((hfib k y y').1 e).1
  have hKσ := hL.2.1
  have hpre : K = m'.toSABMap.φ ⁻¹' (m'.toSABMap.φ '' K) := by
    have := preimage_eq (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' (h := 𝟙 Y) (ν := m'.toSABMap.φ)
      (gT := oY.t.G.hom) (by simpa using h₂) (τ := fun j => (σ j).left) hσ (fun j => by simp)
    rw [hKσ]; exact this
  refine ⟨Hk, π₁, o₁, m₁, m'.toSABMap.φ '' K, hπf, hπe, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.heckeSet_descends E H D l 𝔓 p i _ _ _ _ q o₁ oY m' _ hA hqs (hpre ▸ hK)
  · refine etSet_of_lists _ _ q _ _ m'.toSABMap.φ (p ^ 2) _ σ _ (ObjDim.isAbelianScheme o₁) m'.cart ?_ hqf hqe hqs
      (hpre ▸ hL)
    have := ((baseKA l).unit (p ^ 2) (pow_pos hA.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ (π₁ ≫ Xo.s).appTop).hom
    rwa [map_natCast] at this
  · intro k _ _ z z' e h
    obtain ⟨y, rfl⟩ := exists_lift_of_finite q z
    obtain ⟨y', rfl⟩ := exists_lift_of_finite q z'
    rw [Category.assoc, Category.assoc] at e
    rw [hKσ] at h
    refine (hfib k y y').2 ⟨subset_antisymm ?_ ?_, e⟩
    · exact range_subset_range (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' y y' e fun u u' hu hu' e' =>
        (h (Over.homMk u hu) (Over.homMk u' hu') e').1
    · exact range_subset_range (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' y' y e.symm fun u u' hu hu' e' =>
        (h (Over.homMk u' hu') (Over.homMk u hu) e'.symm).2
  · intro T s o f mu τ K' hL' hK'
    obtain ⟨h, hf, hh⟩ := huniv T f o.t mu.toSABMap τ K' hL' hK'
    rw [← Category.assoc] at hf
    subst hf
    obtain ⟨n, hn⟩ := ((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ (h ≫ q) m₁).2 mu
    have h₃ := n.cart.1
    have hτ : ∀ j, (τ j).left ≫ o.t.G.hom = 𝟙 T := fun j => Over.w (τ j)
    refine ⟨h ≫ q, n, rfl, hn.symm, ?_⟩
    rw [hL'.2.1, hKσ]
    refine preimage_eq (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' h₃ (τ := fun j => (τ j).left) hτ fun j => ?_
    refine h₁.hom_ext ?_ ?_
    · have := hh j
      rw [hm', hn] at this
      simpa using this.symm
    · have e₁ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (h ≫ q)) (hτ j))
      have e₂ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) (hσ j))
      simp only [Category.assoc, h₃.w, h₂.w]
      exact (e₁.trans (Category.id_comp _)).trans (congrArg (h ≫ ·) (e₂.trans (Category.id_comp _)).symm)

end GlobalTheory.HkFam
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernel_scheme_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ (Hk : Scheme.{0}) (π₁ : Hk ⟶ Xo.X) (o₁ : Ob D l (π₁ ≫ Xo.s)) (m₁ : ObjMap o₁ Xo.univ π₁) (K : Set o₁.t.G.left), IsFinite π₁ ∧ Etale π₁ ∧ HeckeSet D o₁.t 𝔓 p i K ∧ EtSet o₁.t.G K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Hk) (z' : Sp k ⟶ Hk), z ≫ π₁ = z' ≫ π₁ → (∀ (u : Over.mk z ⟶ o₁.t.G) (u' : Over.mk z' ⟶ o₁.t.G), u.left ≫ m₁.toSABMap.φ = u'.left ≫ m₁.toSABMap.φ → (Set.range u.left ⊆ K ↔ Set.range u'.left ⊆ K)) → z = z') ∧ ∀ (T : Scheme.{0}) (s : T ⟶ Sp (KA l)) (o : Ob D l s) (f : T ⟶ Xo.X) (mu : ObjMap o Xo.univ f) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over T) ⟶ o.t.G)) (K' : Set o.t.G.left), Lists (p ^ 2) τ K' → HeckeSet D o.t 𝔓 p i K' → ∃ (h : T ⟶ Hk) (n : ObjMap o o₁ h), h ≫ π₁ = f ∧ n.toSABMap.φ ≫ m₁.toSABMap.φ = mu.toSABMap.φ ∧ K' = n.toSABMap.φ ⁻¹' K := by
  atlas_forward_decl GlobalTheory.HkFam.exists_heckeKernelScheme
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem range_subset_iff_of_charts {X Hk S S₁ S₂ U G₀ G G₁ G₂ P : Scheme.{0}} {g₀ : G₀ ⟶ Hk} {gU : U ⟶ X}
    {m₁ : G₀ ⟶ U} {f : S ⟶ X} {g : G ⟶ S} {mu : G ⟶ U} (hmu : IsPullback mu g gU f)
    {K : Set G₀} {K' : Set G}
    {q₁ : S₁ ⟶ S} {g₁ : G₁ ⟶ S₁} {a₁ : G₁ ⟶ G} (ha₁ : a₁ ≫ g = g₁ ≫ q₁) {h₁ : S₁ ⟶ Hk} {n₁ : G₁ ⟶ G₀}
    (hn₁ : IsPullback n₁ g₁ g₀ h₁) (e₁ : n₁ ≫ m₁ = a₁ ≫ mu) (k₁ : a₁ ⁻¹' K' = n₁ ⁻¹' K)
    {q₂ : S₂ ⟶ S} {g₂ : G₂ ⟶ S₂} {a₂ : G₂ ⟶ G} (ha₂ : a₂ ≫ g = g₂ ≫ q₂) {h₂ : S₂ ⟶ Hk} {n₂ : G₂ ⟶ G₀}
    (hn₂ : IsPullback n₂ g₂ g₀ h₂) (e₂ : n₂ ≫ m₁ = a₂ ≫ mu) (k₂ : a₂ ⁻¹' K' = n₂ ⁻¹' K)
    (x₁ : P ⟶ S₁) (x₂ : P ⟶ S₂) (hx : x₁ ≫ q₁ = x₂ ≫ q₂)
    (u₁ u₂ : P ⟶ G₀) (hu₁ : u₁ ≫ g₀ = x₁ ≫ h₁) (hu₂ : u₂ ≫ g₀ = x₂ ≫ h₂) (hu : u₁ ≫ m₁ = u₂ ≫ m₁) :
    (Set.range u₁ ⊆ K ↔ Set.range u₂ ⊆ K) := by
  have key : ∀ {A B : Scheme.{0}} (w : P ⟶ A) (c : A ⟶ B) (L : Set B),
      Set.range (w ≫ c) ⊆ L ↔ Set.range w ⊆ c ⁻¹' L := by
    intro A B w c L
    simp [Set.range_subset_iff]
  obtain ⟨w₁, hw₁, hw₁'⟩ := hn₁.exists_lift u₁ x₁ hu₁
  obtain ⟨w₂, hw₂, hw₂'⟩ := hn₂.exists_lift u₂ x₂ hu₂
  have hw : w₁ ≫ a₁ = w₂ ≫ a₂ := by
    apply hmu.hom_ext
    · rw [Category.assoc, Category.assoc, ← e₁, ← e₂, ← Category.assoc, ← Category.assoc, hw₁, hw₂, hu]
    · rw [Category.assoc, Category.assoc, ha₁, ha₂, ← Category.assoc, ← Category.assoc, hw₁', hw₂', hx]
  rw [← hw₁, ← hw₂, key, key, ← k₁, ← k₂, ← key, ← key, hw]

theorem exists_kerScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ Z : KerScheme Xo 𝔓 p i, EtSet Z.o₁.t.G Z.K := by
  intro E _ _ _ H D l Xo 𝔓 p i hA
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨Hk, π₁, o₁, m₁, K, fin₁, et₁, hK, hE, hpt, hex⟩ := GlobalTheory.T.exists_heckeKernel_scheme_universal E H D l Xo 𝔓 p i hA
  refine ⟨⟨Hk, π₁, fin₁, et₁, o₁, m₁, K, hK, hE, ?_⟩, hE⟩
  intro S s hS o K' hE' hK'
  obtain ⟨f, ⟨hf, ⟨mu⟩⟩, hfu⟩ := Xo.rep S s hS o
  obtain ⟨S', π, o', m, τ, hπ₁, hπ₂, hπ₃, hL⟩ := GlobalTheory.T.hecke_set_etale_level_structure_exists E H D l 𝔓 p i S s o K' hA hE' hK'
  have hK'' := ((GlobalTheory.heckeSets_pull E H D 𝔓 p i S S' o.t o'.t π m.toSABMap o.proper).2 K').1 hK'
  obtain ⟨mu', hmu'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 f π mu).1 m
  obtain ⟨h', n', hh', hn', hKn'⟩ := hex S' (π ≫ s) o' (π ≫ f) mu' τ _ hL hK''
  have cm := m.cart.1
  have cm₁ := m₁.cart.1
  have cn' := n'.cart.1
  haveI : IsReduced S' := GlobalTheory.isReduced_of_smooth_of_isReduced π
  haveI : IsReduced (pullback π π : Scheme.{0}) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst π π)
  have hd : pullback.fst π π ≫ h' = pullback.snd π π ≫ h' := by
    have h0 : (pullback.fst π π ≫ h') ≫ π₁ = (pullback.snd π π ≫ h') ≫ π₁ := by
      rw [Category.assoc, Category.assoc, hh', pullback.condition_assoc]
    refine hom_ext_of_geometric_points _ _ _ π₁ _ _ h0 ?_
    intro k _ _ x
    refine hpt k _ _ (by rw [Category.assoc, Category.assoc x, h0]) ?_
    intro u u' huu
    exact range_subset_iff_of_charts mu.cart.1 cm.w cn' (hn'.trans hmu') hKn' cm.w cn' (hn'.trans hmu') hKn'
      (x ≫ pullback.fst π π) (x ≫ pullback.snd π π) (by rw [Category.assoc, Category.assoc, pullback.condition])
      u.left u'.left (by rw [Category.assoc]; exact Over.w u) (by rw [Category.assoc]; exact Over.w u') huu
  obtain ⟨h, hh⟩ : ∃ h : S ⟶ Hk, π ≫ h = h' := by
    suffices hc : ∀ {Z : Scheme.{0}} (a b : Z ⟶ S'), a ≫ π = b ≫ π → a ≫ h' = b ≫ h' from
      ⟨EffectiveEpi.desc π h' hc, EffectiveEpi.fac π h' hc⟩
    focus
      intro Z a b hab
      have := congrArg (pullback.lift a b hab ≫ ·) hd
      simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  have hhf : h ≫ π₁ = f := by
    rw [← cancel_epi π, ← Category.assoc, hh, hh']
  subst hhf
  obtain ⟨n, hn⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ h m₁).2 mu
  have cn := n.cart.1
  have hmn : m.toSABMap.φ ≫ n.toSABMap.φ = n'.toSABMap.φ := by
    apply cm₁.hom_ext
    · rw [Category.assoc, ← hn]
      exact (hn'.trans hmu').symm
    · rw [Category.assoc, cn.w, cn'.w, ← Category.assoc, cm.w, Category.assoc, hh]
  have hsurj : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback cm.flip hπ₃
  have hKn : K' = n.toSABMap.φ ⁻¹' K := by
    apply hsurj.surj.preimage_injective
    rw [hKn', ← hmn]
    ext y
    simp
  refine ⟨h, ⟨by rw [← Category.assoc, hf], n, hKn⟩, ?_⟩
  rintro h₂ ⟨hs₂, n₂, hKn₂⟩
  obtain ⟨mu₂, hmu₂⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ h₂ m₁).1 n₂
  have h0 : h₂ ≫ π₁ = h ≫ π₁ := hfu _ ⟨by rw [Category.assoc, hs₂], ⟨mu₂⟩⟩
  have hrig : ∀ (f₂ : S ⟶ Xo.X) (mu₂ : ObjMap o Xo.univ f₂), f₂ = h ≫ π₁ → mu₂.toSABMap.φ = mu.toSABMap.φ := by
    intro f₂ mu₂ e
    subst e
    exact GlobalTheory.obj_rigid_closed laws E H D l _ _ _ _ _ _ _ _ Xo.univ o _ (Or.inl hS) _ _
      fun a => ⟨_, mu₂.eta a, mu.eta a⟩
  have e₂ := hmu₂.symm.trans (hrig _ mu₂ h0)
  refine hom_ext_of_geometric_points _ _ _ π₁ _ _ h0 ?_
  intro k _ _ x
  refine hpt k _ _ (by rw [Category.assoc, Category.assoc x, h0]) ?_
  intro u u' huu
  exact range_subset_iff_of_charts (q₁ := 𝟙 S) (q₂ := 𝟙 S) (a₁ := 𝟙 _) (a₂ := 𝟙 _) (K' := K') mu.cart.1 (by simp) n₂.cart.1
    (by rw [Category.id_comp]; exact e₂) (by rw [← hKn₂]; simp) (by simp) cn (by rw [Category.id_comp]; exact hn.symm)
    (by rw [← hKn]; simp) x x rfl u.left u'.left (Over.w u) (Over.w u') huu

end GlobalTheory.HkFam
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernelScheme_universal_reduced_bases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ Z : KerScheme Xo 𝔓 p i, EtSet Z.o₁.t.G Z.K := by
  atlas_forward_decl GlobalTheory.HkFam.exists_kerScheme
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G), (∃! ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left) ∧ ∀ ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → (IsIsog o₁ o₂ p ψ → IsIsog o₁' o₂' p ψ') ∧ ∀ K, IsMonHom ψ → KerSet ψ K → KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) := by
  first | exact @GlobalTheory.HkFam.isog_pull | exact GlobalTheory.HkFam.isog_pull | (intros; apply GlobalTheory.HkFam.isog_pull <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.QuotGlue

section Cover

variable {I : Type} {X Y S : Scheme.{0}} {V : I → Scheme.{0}}

theorem cover_ext (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x) {a b : X ⟶ Y}
    (h : ∀ i, f i ≫ a = f i ≫ b) : a = b :=
  Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers I V f hc) a b h

theorem cover_glue (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x) (g : ∀ i, V i ⟶ Y)
    (h : ∀ i j, pullback.fst (f i) (f j) ≫ g i = pullback.snd _ _ ≫ g j) : ∃ a : X ⟶ Y, ∀ i, f i ≫ a = g i :=
  ⟨Scheme.Cover.glueMorphisms (Scheme.Cover.mkOfCovers I V f hc) g h,
    Scheme.Cover.ι_glueMorphisms (Scheme.Cover.mkOfCovers I V f hc) g h⟩

theorem cover_pull {f : ∀ i, V i ⟶ S} (hc : ∀ x, ∃ i y, f i y = x) {p : X ⟶ S} {W : I → Scheme.{0}}
    {φ : ∀ i, W i ⟶ X} {q : ∀ i, W i ⟶ V i} (h : ∀ i, IsPullback (φ i) (q i) p (f i)) (x : X) : ∃ i y, φ i y = x := by
  obtain ⟨i, y, hy⟩ := hc (p x)
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (h i) x y hy.symm
  exact ⟨i, z, hz⟩

theorem cover_prop (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q] (f : ∀ i, V i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x) {p : X ⟶ S} {W : I → Scheme.{0}}
    {φ : ∀ i, W i ⟶ X} {q : ∀ i, W i ⟶ V i} (h : ∀ i, IsPullback (φ i) (q i) p (f i)) (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers I V f hc) fun i => ?_
  change Q (pullback.snd p (f i))
  rw [← (h i).isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso Q]
  exact hq i

theorem exists_point_lift (f : ∀ i, V i ⟶ S) [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x)
    {k : Type} [Field k] (x : Sp k ⟶ S) : ∃ (i : I) (x' : Sp k ⟶ V i), x' ≫ f i = x := by
  obtain ⟨i, y, hy⟩ := hc (x (default : PrimeSpectrum k))
  refine ⟨i, IsOpenImmersion.lift (f i) x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨a, rfl⟩
  exact ⟨y, hy.trans (congrArg x (Subsingleton.elim (α := PrimeSpectrum k) _ _))⟩

end Cover

section Grp

variable {I : Type} {S : Scheme.{0}} {V : I → Scheme.{0}} {f : ∀ i, V i ⟶ S} [∀ i, IsOpenImmersion (f i)]
  {G₁ G₂ : Over S} {G₁' G₂' : ∀ i, Over (V i)}
  [GrpObj G₁] [GrpObj G₂] [∀ i, GrpObj (G₁' i)] [∀ i, GrpObj (G₂' i)]
  {φ₁ : ∀ i, (G₁' i).left ⟶ G₁.left} {φ₂ : ∀ i, (G₂' i).left ⟶ G₂.left}

theorem mul_comp (hc : ∀ x, ∃ i y, f i y = x) (h₁ : ∀ i, IsGrpPullback (G₁' i) G₁ (f i) (φ₁ i))
    (h₂ : ∀ i, IsGrpPullback (G₂' i) G₂ (f i) (φ₂ i)) (ψ : G₁ ⟶ G₂) (ψ' : ∀ i, G₁' i ⟶ G₂' i) [∀ i, IsMonHom (ψ' i)]
    (hψ : ∀ i, (ψ' i).left ≫ φ₂ i = φ₁ i ≫ ψ.left) (T : Over S) (x y : T ⟶ G₁) :
    (x * y) ≫ ψ = (x ≫ ψ) * (y ≫ ψ) := by
  refine Over.OverMorphism.ext (cover_ext (fun i => pullback.fst T.hom (f i))
    (cover_pull hc fun i => IsPullback.of_hasPullback T.hom (f i)) fun i => ?_)
  have H := IsPullback.of_hasPullback T.hom (f i)
  let q := pullback.fst T.hom (f i)
  let W : Over (V i) := Over.mk (pullback.snd T.hom (f i))
  let l : (T ⟶ G₁) → (W ⟶ G₁' i) := fun z => Over.homMk
    ((h₁ i).1.lift (q ≫ z.left) (pullback.snd T.hom (f i)) (by rw [Category.assoc, Over.w z]; exact H.w))
    ((h₁ i).1.lift_snd _ _ _)
  have hl : ∀ z, (l z).left ≫ φ₁ i = q ≫ z.left := fun z => (h₁ i).1.lift_fst _ _ _
  let q' : Over.mk (W.hom ≫ f i) ⟶ T := Over.homMk q H.w
  have hl' : ∀ z, (q' ≫ z ≫ ψ).left = (l z ≫ ψ' i).left ≫ φ₂ i := fun z => by
    show q ≫ z.left ≫ ψ.left = ((l z).left ≫ (ψ' i).left) ≫ φ₂ i
    rw [Category.assoc, hψ, ← Category.assoc (l z).left, hl, Category.assoc]
  have e₁ := (h₁ i).2 W (l x) (l y) (q' ≫ x) (q' ≫ y) (hl x).symm (hl y).symm
  have e₂ := (h₂ i).2 W (l x ≫ ψ' i) (l y ≫ ψ' i) (q' ≫ x ≫ ψ) (q' ≫ y ≫ ψ) (hl' x) (hl' y)
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← MonObj.mul_comp (l x) (l y) (ψ' i)] at e₂
  replace e₂ : _ = (l x * l y).left ≫ (ψ' i).left ≫ φ₂ i := e₂.trans (Category.assoc _ _ _)
  rw [hψ, ← Category.assoc, ← e₁] at e₂
  refine Eq.trans ?_ e₂.symm
  exact (Category.assoc _ _ _).symm

theorem isMonHom (hc : ∀ x, ∃ i y, f i y = x) (h₁ : ∀ i, IsGrpPullback (G₁' i) G₁ (f i) (φ₁ i))
    (h₂ : ∀ i, IsGrpPullback (G₂' i) G₂ (f i) (φ₂ i)) (ψ : G₁ ⟶ G₂) (ψ' : ∀ i, G₁' i ⟶ G₂' i) [∀ i, IsMonHom (ψ' i)]
    (hψ : ∀ i, (ψ' i).left ≫ φ₂ i = φ₁ i ≫ ψ.left) : IsMonHom ψ := by
  refine ⟨?_, ?_⟩
  · have h := mul_comp hc h₁ h₂ ψ ψ' hψ (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S) ⟶ G₁) ≫ ψ = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul_comp hc h₁ h₂ ψ ψ' hψ (G₁ ⊗ G₁) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

omit [GrpObj G₁] [∀ i, GrpObj (G₁' i)] in

theorem kerSet (hc : ∀ x, ∃ i y, f i y = x) (h₁ : ∀ i, IsPullback (φ₁ i) (G₁' i).hom G₁.hom (f i))
    (h₂ : ∀ i, IsPullback (φ₂ i) (G₂' i).hom G₂.hom (f i))
    (he : ∀ i, η[G₂' i].left ≫ φ₂ i = f i ≫ η[G₂].left) (ψ : G₁ ⟶ G₂) (ψ' : ∀ i, G₁' i ⟶ G₂' i)
    (hψ : ∀ i, (ψ' i).left ≫ φ₂ i = φ₁ i ≫ ψ.left) (K : Set G₁.left) (hK : ∀ i, KerSet (ψ' i) (φ₁ i ⁻¹' K)) :
    KerSet ψ K := by
  intro k _ _ x z
  obtain ⟨i, x', hj⟩ := exists_point_lift f hc x
  let z' : Over.mk x' ⟶ G₁' i := Over.homMk ((h₁ i).lift z.left x' (by rw [Over.w z]; exact hj.symm))
    ((h₁ i).lift_snd _ _ _)
  have hz : z'.left ≫ φ₁ i = z.left := (h₁ i).lift_fst _ _ _
  have a₁ : (z' ≫ ψ' i).left ≫ φ₂ i = (z ≫ ψ).left := by
    rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc, hz]
    rfl
  have a₂ : (1 : Over.mk x' ⟶ G₂' i).left ≫ φ₂ i = (1 : Over.mk x ⟶ G₂).left := by
    show (x' ≫ η[G₂' i].left) ≫ φ₂ i = x ≫ η[G₂].left
    rw [Category.assoc, he, ← Category.assoc, hj]
  have b₁ : z ≫ ψ = 1 ↔ z' ≫ ψ' i = 1 :=
    ⟨fun h => Over.OverMorphism.ext ((h₂ i).hom_ext (by rw [a₁, a₂, h]) ((Over.w _).trans (Over.w _).symm)),
      fun h => Over.OverMorphism.ext (by rw [← a₁, ← a₂, h])⟩
  have pt : ∀ a, φ₁ i (z'.left a) = z.left a := fun a => congrArg (fun q => q a) hz
  rw [b₁, hK i k x' z']
  constructor
  · rintro h _ ⟨a, rfl⟩
    rw [← pt]
    exact h ⟨a, rfl⟩
  · rintro h _ ⟨a, rfl⟩
    show φ₁ i (z'.left a) ∈ K
    rw [pt]
    exact h ⟨_, rfl⟩

end Grp

theorem lbIso_of_cover {I : Type} {S : Scheme.{0}} {V X' : I → Scheme.{0}} [IsReduced S] (A : Over S) [GrpObj A]
    [IsCommMonObj A] (M : LB A.left) (hA : IsAbelianScheme A) (hM : M.IsLB) (ha : Out.RelAmple A M)
    {f : ∀ i, V i ⟶ S} (hc : ∀ x, ∃ i y, f i y = x)
    {φ : ∀ i, X' i ⟶ A.left} {g : ∀ i, X' i ⟶ V i} (h : ∀ i, IsPullback (φ i) (g i) A.hom (f i)) {P Q : LB A.left}
    (hP : P.IsLB) (hQ : Q.IsLB) (hi : ∀ i, LBIso (P.pull (φ i)) (Q.pull (φ i))) (s : (P.pull (eSec A)).Gen)
    (hs : s.IsGen) (t : (Q.pull (eSec A)).Gen) (ht : t.IsGen) : LBIso P Q := by
  refine GlobalTheory.seesaw_reduced_of_dense GlobalTheory.globalFns_holds S A M hA hM ha S A.left (𝟙 S) (𝟙 _) A.hom (LB.div Q P)
    (IsPullback.id_horiz _) (LB.isLB_div hQ hP) ?_ (eSec A) (Over.w η[A]) ?_
  · refine dense_univ.mono fun p _ => ?_
    obtain ⟨i, p', rfl⟩ := hc p
    obtain ⟨w, hw⟩ := hi i
    obtain ⟨c, hc⟩ := gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q (φ i)) w hw
    let x' : Sp ((V i).residueField p') ⟶ V i := (V i).fromSpecResidueField p'
    refine ⟨(V i).residueField p', inferInstance, x' ≫ f i, pullback (g i) x', pullback.fst (g i) x' ≫ φ i,
      pullback.snd (g i) x',
      ⟨(default : PrimeSpectrum ((V i).residueField p')), congrArg (f i) (Scheme.fromSpecResidueField_apply p' _)⟩,
      (IsPullback.of_hasPullback (g i) x').paste_horiz (h i), ?_⟩
    exact gen_chartPull (chartPullSame (LB.div Q P) (K := PUnit) _ (fun _ => φ i) (fun _ => 1) (pullback.fst (g i) x')
      fun _ => rfl) c hc
  · obtain ⟨w, hw⟩ := GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    exact gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q _) w hw

set_option backward.isDefEq.respectTransparency.types false in
theorem isFinite_local : IsZariskiLocalAtTarget @IsFinite.{0} := inferInstance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem isIsog_of_cover {I : Type} {p : ℕ} {S : Scheme.{0}} [IsReduced S] {s : S ⟶ Sp (KA l)} {V : I → Scheme.{0}}
    {s' : ∀ i, V i ⟶ Sp (KA l)} {f : ∀ i, V i ⟶ S} [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x)
    {o₁ o₂ : Ob D l s} {o₁' o₂' : ∀ i, Ob D l (s' i)} (n₁ : ∀ i, ObjMap (o₁' i) o₁ (f i))
    (n₂ : ∀ i, ObjMap (o₂' i) o₂ (f i)) (ψ : o₁.t.G ⟶ o₂.t.G) (ψ' : ∀ i, (o₁' i).t.G ⟶ (o₂' i).t.G)
    (hψ : ∀ i, (ψ' i).left ≫ (n₂ i).cm.F = (n₁ i).cm.F ≫ ψ.left) (hI : ∀ i, IsIsog (o₁' i) (o₂' i) p (ψ' i)) :
    IsIsog o₁ o₂ p ψ := by
  have hm := fun i => (hI i).1.1
  have io₁ : ∀ i, IsOpenImmersion (n₁ i).cm.F := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n₁ i).cart.1.flip inferInstance
  have io₂ : ∀ i, IsOpenImmersion (n₂ i).cm.F := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n₂ i).cart.1.flip inferInstance
  have c₁ := cover_pull hc fun i => (n₁ i).cart.1
  have c₂ := cover_pull hc fun i => (n₂ i).cart.1
  have pb : ∀ i, IsPullback (n₁ i).cm.F (ψ' i).left ψ.left (n₂ i).cm.F := fun i => by
    refine IsPullback.of_bot ?_ (hψ i).symm (n₂ i).cart.1
    rw [Over.w, Over.w]
    exact (n₁ i).cart.1
  have hmon : IsMonHom ψ := isMonHom hc (fun i => (n₁ i).cart) (fun i => (n₂ i).cart) ψ ψ' hψ
  have sec : ∀ {a : 𝟙_ (Over S) ⟶ o₁.t.G} {b : 𝟙_ (Over S) ⟶ o₂.t.G} {a' : ∀ i, 𝟙_ (Over (V i)) ⟶ (o₁' i).t.G}
      {b' : ∀ i, 𝟙_ (Over (V i)) ⟶ (o₂' i).t.G}, (∀ i, (a' i).left ≫ (n₁ i).cm.F = f i ≫ a.left) →
      (∀ i, (b' i).left ≫ (n₂ i).cm.F = f i ≫ b.left) →
      (∀ i, a' i ≫ ψ' i = b' i) → a ≫ ψ = b := fun {a b a' b'} ha hb h =>
    Over.OverMorphism.ext (cover_ext f hc fun i => by
      rw [← hb, ← h, Over.comp_left, Over.comp_left, Category.assoc, hψ, ← Category.assoc, ← Category.assoc, ha])
  have : IsZariskiLocalAtTarget @Etale.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale)
  have := isFinite_local
  refine ⟨⟨hmon, cover_prop @IsFinite _ c₂ pb fun i => (hI i).1.2.1, cover_prop @Etale _ c₂ pb fun i => (hI i).1.2.2.1,
    cover_prop @Surjective _ c₂ pb fun i => (hI i).1.2.2.2.1,
    fun a => Over.OverMorphism.ext (cover_ext _ c₁ fun i => ?_), ?_⟩, fun p' hp a =>
    ⟨sec (fun i => (n₁ i).eta _) (fun i => (n₂ i).eta _) fun i => ((hI i).2 p' hp a).1,
      sec (fun i => (n₁ i).etaA _) (fun i => (n₂ i).etaA _) fun i => ((hI i).2 p' hp a).2⟩⟩
  · have e := congrArg (fun q => q.left) ((hI i).1.2.2.2.2.1 a)
    simp only [Over.comp_left] at e ⊢
    rw [← Category.assoc, ← (n₁ i).act, Category.assoc, ← hψ, ← Category.assoc, e, Category.assoc, (n₂ i).act,
      ← Category.assoc, hψ, Category.assoc]
  · have hP : (lbPow o₁.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb o₁.t.PP.isLB _ _
    have hQ := pull_isLB o₂.t.PP.isLB ψ.left
    obtain ⟨c, hc'⟩ := GlobalTheory.IsogDescent.exists_gen_pow o₁.t.PP.L _ ((p ^ 2 : ℕ) : ℤ) o₁.t.PP.rig o₁.t.PP.rigGen
    obtain ⟨d₁, hd₁⟩ := gen_chartPull (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ))
      (eSec o₁.t.G) (fun _ => eSec o₁.t.G) fun _ => (Category.comp_id _).symm) c hc'
    obtain ⟨d₂, hd₂⟩ := gen_chartPull (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) (fun _ => 1)
      (eSec o₁.t.G) (fun _ => eSec o₂.t.G) fun _ => (congrArg (fun q => q.left) hmon.one_hom).symm)
      o₂.t.PP.rig o₂.t.PP.rigGen
    refine lbIso_of_cover o₁.t.G o₁.t.PP.L (GlobalTheory.ObjDim.isAbelianScheme o₁) o₁.t.PP.isLB o₁.ample hc
      (fun i => (n₁ i).cart.1) hP hQ (fun i => ?_) d₁ hd₁ d₂ hd₂
    have hP' : (lbPow (o₁' i).t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb (o₁' i).t.PP.isLB _ _
    obtain ⟨w₁, hw₁, -⟩ := (n₁ i).lin
    obtain ⟨w₂, hw₂, -⟩ := (n₂ i).lin
    have i₁ : LBIso (lbPow (o₁' i).t.PP.L (p ^ 2)) ((lbPow o₁.t.PP.L (p ^ 2)).pull (n₁ i).cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) _ (n₁ i).cm.F _
        fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
        (iso_linComb ((isGen_iff w₁).1 hw₁) (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ)))
    have i₂ : LBIso ((o₂' i).t.PP.L.pull (ψ' i).left) ((o₂.t.PP.L.pull ψ.left).pull (n₁ i).cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) _ (n₁ i).cm.F _
        fun _ => hψ i)
        (iso_linComb ((isGen_iff w₂).1 hw₂) (K := PUnit) (fun _ => (ψ' i).left) (fun _ => 1))
    exact LBIso.trans (pull_isLB hP _) hP' (pull_isLB hQ _) i₁.symm
      (LBIso.trans hP' (pull_isLB (o₂' i).t.PP.isLB _) (pull_isLB hQ _) (hI i).1.2.2.2.2.2 i₂)

theorem exists_pull {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} (f : S' ⟶ S) (hf : f ≫ s = s')
    (o : Ob D l s) : ∃ o' : Ob D l s', Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s s' f rfl rfl
    (by rw [hf]; exact ((congrArg (s' ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)).symm) o

theorem exists_comp {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} (m : ObjMap o' o f)
    (m' : ObjMap o'' o' f') : ∃ m'' : ObjMap o'' o (f' ≫ f), m''.cm.F = m'.cm.F ≫ m.cm.F :=
  ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).1 m'

theorem exists_cancel {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {g : S'' ⟶ S} (hg : f' ≫ f = g)
    (m : ObjMap o' o f) (m'' : ObjMap o'' o g) : ∃ m' : ObjMap o'' o' f', m''.cm.F = m'.cm.F ≫ m.cm.F := by
  subst hg
  exact ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).2 m''

theorem exists_restrict {p : ℕ} {S V T X : Scheme.{0}} {s : S ⟶ Sp (KA l)} {sV : V ⟶ Sp (KA l)} {sT : T ⟶ Sp (KA l)}
    {sX : X ⟶ Sp (KA l)} {o : Ob D l s} {K : Set o.t.G.left} {f : V ⟶ S} {oV a : Ob D l sV} (m : ObjMap oV o f)
    {ψ : oV.t.G ⟶ a.t.G} (hI : IsIsog oV a p ψ) (hK : KerSet ψ (m.cm.F ⁻¹' K)) {u : Ob D l sX} {c : V ⟶ X}
    (n : ObjMap a u c) {g : T ⟶ S} {oT : Ob D l sT} (mT : ObjMap oT o g) (g' : T ⟶ V) (hg : g' ≫ f = g)
    (hs : g' ≫ sV = sT) :
    ∃ (r : oT.t.G.left ⟶ oV.t.G.left) (aT : Ob D l sT) (ψT : oT.t.G ⟶ aT.t.G) (nT : ObjMap aT u (g' ≫ c)),
      r ≫ m.cm.F = mT.cm.F ∧ IsIsog oT aT p ψT ∧ KerSet ψT (mT.cm.F ⁻¹' K) ∧
        ψT.left ≫ nT.cm.F = r ≫ ψ.left ≫ n.cm.F := by
  obtain ⟨r, hr⟩ := exists_cancel hg m mT
  obtain ⟨aT, ⟨b⟩⟩ := exists_pull g' hs a
  obtain ⟨⟨ψT, hψ, -⟩, h⟩ := GlobalTheory.HkFam.isog_pull E H D l p V T sV sT g' oV a oT aT r b ψ
  obtain ⟨nT, hn⟩ := exists_comp n b
  have hψ' : ψT.left ≫ b.cm.F = r.cm.F ≫ ψ.left := hψ
  refine ⟨r.cm.F, aT, ψT, nT, hr.symm, (h ψT hψ).1 hI, ?_, ?_⟩
  · have := (h ψT hψ).2 _ hI.1.1 hK
    rw [hr]
    convert this using 1
    ext x
    simp only [Set.mem_preimage, Scheme.Hom.comp_apply]
  · rw [hn, reassoc_of% hψ']

theorem overlap (Xo : Moduli D l) {𝔓 : Ideal (𝓞 E)} {p i : ℕ} {S V₁ V₂ : Scheme.{0}} [IsReduced S]
    {s : S ⟶ Sp (KA l)} {o : Ob D l s} {K : Set o.t.G.left} (hA : admitted l 𝔓 p) (hH : HeckeSet D o.t 𝔓 p i K)
    {f₁ : V₁ ⟶ S} {f₂ : V₂ ⟶ S} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {o₁ a₁ : Ob D l (f₁ ≫ s)} {o₂ a₂ : Ob D l (f₂ ≫ s)} (m₁ : ObjMap o₁ o f₁) (m₂ : ObjMap o₂ o f₂)
    {ψ₁ : o₁.t.G ⟶ a₁.t.G} {ψ₂ : o₂.t.G ⟶ a₂.t.G} (hI₁ : IsIsog o₁ a₁ p ψ₁) (hI₂ : IsIsog o₂ a₂ p ψ₂)
    (hK₁ : KerSet ψ₁ (m₁.cm.F ⁻¹' K)) (hK₂ : KerSet ψ₂ (m₂.cm.F ⁻¹' K)) {c₁ : V₁ ⟶ Xo.X} {c₂ : V₂ ⟶ Xo.X}
    (hc₁ : c₁ ≫ Xo.s = f₁ ≫ s) (hc₂ : c₂ ≫ Xo.s = f₂ ≫ s) (n₁ : ObjMap a₁ Xo.univ c₁) (n₂ : ObjMap a₂ Xo.univ c₂) :
    pullback.fst f₁ f₂ ≫ c₁ = pullback.snd f₁ f₂ ≫ c₂ ∧
      pullback.fst m₁.cm.F m₂.cm.F ≫ ψ₁.left ≫ n₁.cm.F = pullback.snd m₁.cm.F m₂.cm.F ≫ ψ₂.left ≫ n₂.cm.F := by
  let g : pullback f₁ f₂ ⟶ S := pullback.fst f₁ f₂ ≫ f₁
  have : IsReduced (pullback f₁ f₂) := isReduced_of_isOpenImmersion g
  have e₂ : pullback.snd f₁ f₂ ≫ f₂ = g := pullback.condition.symm
  obtain ⟨oT, ⟨mT⟩⟩ := exists_pull g rfl o
  have hs₁ : pullback.fst f₁ f₂ ≫ f₁ ≫ s = g ≫ s := (Category.assoc _ _ _).symm
  have hs₂ : pullback.snd f₁ f₂ ≫ f₂ ≫ s = g ≫ s := by rw [← e₂, Category.assoc]
  obtain ⟨r₁, b₁, χ₁, k₁, hr₁, hJ₁, hL₁, hk₁⟩ := exists_restrict m₁ hI₁ hK₁ n₁ mT (pullback.fst f₁ f₂) rfl hs₁
  obtain ⟨r₂, b₂, χ₂, k₂, hr₂, hJ₂, hL₂, hk₂⟩ := exists_restrict m₂ hI₂ hK₂ n₂ mT (pullback.snd f₁ f₂) e₂ hs₂
  have hHT := ((GlobalTheory.heckeSets_pull E H D 𝔓 p i S _ o.t oT.t g mT.toSABMap o.proper).2 K).1 hH
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.heckeQuotient_classifyingMap_isogeny_unique E H D l Xo 𝔓 p i _ (g ≫ s) oT b₁ b₂ χ₁ χ₂ _ _ _ k₁ k₂ hA hHT
    (by rw [Category.assoc, hc₁, hs₁]) (by rw [Category.assoc, hc₂, hs₂]) hJ₁ hJ₂ hL₁ hL₂
  refine ⟨h₁, ?_⟩
  have h₃ : r₁ ≫ ψ₁.left ≫ n₁.cm.F = r₂ ≫ ψ₂.left ≫ n₂.cm.F := hk₁.symm.trans (Eq.trans h₂ hk₂)
  have io₁ : IsOpenImmersion m₁.cm.F :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) m₁.cart.1.flip inferInstance
  have io₂ : IsOpenImmersion m₂.cm.F :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) m₂.cart.1.flip inferInstance
  let t : pullback m₁.cm.F m₂.cm.F ⟶ pullback f₁ f₂ :=
    pullback.lift (pullback.fst _ _ ≫ o₁.t.G.hom) (pullback.snd _ _ ≫ o₂.t.G.hom) (by
      rw [Category.assoc, Category.assoc, ← m₁.cart.1.w, ← m₂.cart.1.w, pullback.condition_assoc])
  let w : pullback m₁.cm.F m₂.cm.F ⟶ oT.t.G.left := mT.cart.1.lift (pullback.fst _ _ ≫ m₁.cm.F) t (by
    rw [Category.assoc, m₁.cart.1.w]
    simp only [t, g, pullback.lift_fst_assoc, Category.assoc])
  have hw : w ≫ mT.cm.F = pullback.fst _ _ ≫ m₁.cm.F := mT.cart.1.lift_fst _ _ _
  have w₁ : w ≫ r₁ = pullback.fst _ _ := by
    rw [← cancel_mono m₁.cm.F, Category.assoc, hr₁, hw]
  have w₂ : w ≫ r₂ = pullback.snd _ _ := by
    rw [← cancel_mono m₂.cm.F, Category.assoc, hr₂, hw, pullback.condition]
  rw [← w₁, ← w₂]
  exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) h₃).trans (Category.assoc _ _ _).symm)

end GlobalTheory.QuotGlue

open GlobalTheory.QuotGlue in

theorem GlobalTheory.hasQuot_of_openCover :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → (∀ q : S, ∃ (U : S.Opens) (o' : Ob D l (U.ι ≫ s)) (m : ObjMap o' o U.ι), q ∈ U ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K)) → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i S _ s o K hA hH h
  choose U o' m hU a ψ hI hK using h
  have hrep : ∀ q, ∃ c : (U q).toScheme ⟶ Xo.X, c ≫ Xo.s = (U q).ι ≫ s ∧ Nonempty (ObjMap (a q) Xo.univ c) :=
    fun q => (Xo.rep _ _ (isReduced_of_isOpenImmersion (U q).ι) (a q)).exists
  choose c hc hn using hrep
  have n := fun q => (hn q).some
  have cov : ∀ x : S, ∃ (q : S) (y : (U q).toScheme), (U q).ι y = x := fun x => ⟨x, ⟨x, hU x⟩, rfl⟩
  have io : ∀ q, IsOpenImmersion (m q).cm.F := fun q =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (m q).cart.1.flip inferInstance
  have covG := cover_pull cov fun q => (m q).cart.1
  have ov := fun q q' => overlap Xo hA hH (m q) (m q') (hI q) (hI q') (hK q) (hK q') (hc q) (hc q') (n q) (n q')
  obtain ⟨F, hF⟩ := cover_glue (fun q => (U q).ι) cov c fun q q' => (ov q q').1
  obtain ⟨Φ, hΦ⟩ := cover_glue (fun q => (m q).cm.F) covG (fun q => (ψ q).left ≫ (n q).cm.F) fun q q' => (ov q q').2
  have hFs : F ≫ Xo.s = s := cover_ext _ cov fun q => by rw [← Category.assoc, hF, hc]
  obtain ⟨o₂, ⟨n₂⟩⟩ := exists_pull F hFs Xo.univ
  have hw : Φ ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ F := cover_ext _ covG fun q => by
    rw [← Category.assoc, hΦ, Category.assoc, (n q).cart.1.w, ← Category.assoc, Over.w, ← Category.assoc,
      (m q).cart.1.w, Category.assoc, hF]
  let χ : o.t.G ⟶ o₂.t.G := Over.homMk (n₂.cart.1.lift Φ o.t.G.hom hw) (n₂.cart.1.lift_snd _ _ _)
  have hχ : χ.left ≫ n₂.cm.F = Φ := n₂.cart.1.lift_fst _ _ _
  choose b hb using fun q => exists_cancel (hF q) n₂ (n q)
  have hψ : ∀ q, (ψ q).left ≫ (b q).cm.F = (m q).cm.F ≫ χ.left := fun q => by
    refine n₂.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hχ, hΦ, hb]
    · rw [Category.assoc, Category.assoc, Over.w, (b q).cart.1.w, (m q).cart.1.w, ← Category.assoc, Over.w]
  exact ⟨o₂, χ, isIsog_of_cover cov m b χ ψ hψ hI, kerSet cov (fun q => (m q).cart.1) (fun q => (b q).cart.1)
    (fun q => (b q).cm.e_comm.trans (by rw [(b q).base]; rfl)) χ ψ hψ K hK⟩

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_of_open_cover_reduced_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → (∀ q : S, ∃ (U : S.Opens) (o' : Ob D l (U.ι ≫ s)) (m : ObjMap o' o U.ι), q ∈ U ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K)) → HasQuot o p K := by
  atlas_forward_decl GlobalTheory.hasQuot_of_openCover
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSplit

theorem exists_affine_isDomain {Z : Scheme.{0}} [IsLocallyNoetherian Z] (hZ : Geo.Tor.IsNormalScheme Z) (p : Z) :
    ∃ W : Z.Opens, IsAffineOpen W ∧ p ∈ W ∧ IsDomain Γ(Z, W) := by
  have := GlobalTheory.IsNormalScheme.of_pred hZ
  have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents p)
  obtain ⟨W, hW, hpW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, hC⟩) (x := p) mem_irreducibleComponent
  exact ⟨W, hW, hpW, (GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible
    ⟨⟨p, hpW⟩, (isIrreducible_irreducibleComponent (x := p)).2.open_subset W.isOpen fun q hq => hle hq⟩).1⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (f : S' ⟶ S) (o : Ob D l s) :
    ∃ o' : Ob D l (f ≫ s), Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s (f ≫ s) f rfl rfl
    (by rw [show spMap (RingHom.id (KA l)) = 𝟙 _ from Spec.map_id _, Category.comp_id]) o

theorem hasQuot_image (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) {S S' : Scheme.{0}} [IsReduced S] [IsNoetherian S']
    (s : S ⟶ Sp (KA l)) (g : S' ⟶ S) [Etale g] (o : Ob D l s) (s' : S' ⟶ Sp (KA l)) (hs : s' = g ≫ s)
    (o' : Ob D l s') (m : ObjMap o' o g) (K : Set o.t.G.left) (hA : admitted l 𝔓 p) (hK : HeckeSet D o.t 𝔓 p i K)
    (hQ : HasQuot o' p (m.toSABMap.φ ⁻¹' K)) (q : S) (hq : q ∈ Set.range g) :
    ∃ (U : S.Opens) (o₁ : Ob D l (U.ι ≫ s)) (m₁ : ObjMap o₁ o U.ι), q ∈ U ∧ HasQuot o₁ p (m₁.toSABMap.φ ⁻¹' K) := by
  let U : S.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  obtain ⟨g', hg'⟩ : ∃ g' : S' ⟶ U.toScheme, g' ≫ U.ι = g :=
    ⟨IsOpenImmersion.lift U.ι g (by simp [U]), IsOpenImmersion.lift_fac _ _ _⟩
  have hU : ∀ x : S, x ∈ U → x ∈ Set.range g := fun _ h => h
  have hqU : q ∈ U := hq
  clear_value U
  subst hg'
  rw [Category.assoc] at hs
  subst hs
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull s U.ι o
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 U.ι g' m₁).2 m
  have he : Etale g' := Etale.of_comp g' U.ι
  have hsur : Surjective g' := ⟨fun y => by
    obtain ⟨x, hx⟩ := hU (U.ι y) y.2
    exact ⟨x, U.ι.isOpenEmbedding.injective (by simpa using hx)⟩⟩
  refine ⟨U, o₁, m₁, hqU, GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover E H D l Xo 𝔓 p i _ _ _ g' o₁ o' m' _ hA
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK) he hsur inferInstance ?_⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hQ
  exact hQ

end GlobalTheory.HkSplit

theorem GlobalTheory.hasQuot_of_lists_of_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → Smooth s → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i n S s o σ K hD hA hs hL hK
  obtain ⟨hr, hN, hn⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ S s hs
  refine GlobalTheory.T.heckeQuotient_of_open_cover_reduced_base E H D l Xo 𝔓 p i S s o K hA hK fun q => ?_
  obtain ⟨W, hW, hq, hd⟩ := GlobalTheory.HkSplit.exists_affine_isDomain hN q
  have hR : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let j : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hj : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  obtain ⟨x, hx⟩ : q ∈ Set.range j := by
    rw [show Set.range j = W from hW.range_fromSpec]; exact hq
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.HkSplit.exists_pull s j o
  obtain ⟨σ', -, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m₁.toSABMap.cart K _ n σ hL
  obtain ⟨R', _, π, o', m, he, ⟨y, hy⟩, hQ⟩ := GlobalTheory.T.exists_etale_hasHeckeQuotient_noetherian_domain E H D l 𝔓 p i n Γ(S, W) (j ≫ s) o₁ σ' _ x hD hA hL'
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK)
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 j π m₁).1 m
  have : IsLocallyNoetherian (Sp R') := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian (Sp R') := {}
  refine GlobalTheory.HkSplit.hasQuot_image Xo 𝔓 p i s (π ≫ j) o _ (Category.assoc _ _ _).symm o' m' K hA hK ?_ q
    ⟨y, by rw [Scheme.Hom.comp_apply, hy, hx]⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  exact hQ
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_exists_listed_kernels_smooth_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → Smooth s → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  atlas_forward_decl GlobalTheory.hasQuot_of_lists_of_smooth
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem corr_kerSet_unique {S : Scheme.{0}} {G G' : Over S} [GrpObj G'] {ψ : G ⟶ G'} {K K' : Set G.left}
    (h : KerSet ψ K) (h' : KerSet ψ K') : K = K' := by
  ext g
  obtain ⟨k, _, _, z₀, hz⟩ := exists_geomPt_range_eq G.left g
  let z : Over.mk (z₀ ≫ G.hom) ⟶ G := Over.homMk z₀ rfl
  have h1 := h k _ z
  have h2 := h' k _ z
  have hzl : z.left = z₀ := rfl
  rw [hzl, hz, Set.singleton_subset_iff] at h1 h2
  exact h1.symm.trans h2

theorem corr_heckeSet_kill {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {S : Scheme.{0}} (t : SAB H S) {P : Ideal (𝓞 E)} {p i : ℕ} {K : Set t.G.left} (hpP : (p : 𝓞 E) ∈ P)
    (hK : HeckeSet D t P p i K) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ t.G)
    (hz : Set.range z.left ⊆ K) : z ^ p ^ 2 = 1 := by
  have hnat : ∀ {T : Over S} (x : T ⟶ t.G) (n : ℕ), x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
    intro T x n
    induction n with
    | zero =>
      have h := t.act.add 0 0
      rw [add_zero] at h
      have h0 : t.act.act 0 = 1 := by simpa using h
      rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]
  obtain ⟨C, hC, hH⟩ := hK k x
  have hzC := hH.2.2.1 ((hC z).2 hz)
  have hbar : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this
  have h := hzC ((p ^ 2 : ℕ) : 𝓞 E) (by
    rw [Nat.cast_pow, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hbar)
  rwa [hnat] at h

theorem corr_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), 1 ≤ D.p + D.q → admitted l 𝔓 p → Nonempty (Corr Xo 𝔓 p i) := by
  intro E _ _ _ H D l Xo P p i hr hA
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_heckeKernelScheme_universal_reduced_bases E H D l Xo P p i hA
  have := Z.et₁
  have := Xo.smooth
  have hXs : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hs : Smooth (Z.π₁ ≫ Xo.s) := inferInstance
  have hred : IsReduced Z.Hk :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hs).1
  obtain ⟨S', π, o', m, τ, hf, he, hsu, hL⟩ :=
    GlobalTheory.T.hecke_set_etale_level_structure_exists E H D l P p i Z.Hk _ Z.o₁ Z.K hA hZ Z.hecke
  have hH' := ((GlobalTheory.heckeSets_pull E H D P p i _ _ _ _ _ m.toSABMap Z.o₁.proper).2 Z.K).1 Z.hecke
  have hq' := GlobalTheory.T.heckeQuotient_exists_listed_kernels_smooth_base E H D l Xo P p i _ S' _ o' τ _ hr hA inferInstance hL hH'
  obtain ⟨o₂, ψ, hi, hk⟩ := GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover E H D l Xo P p i Z.Hk S' _ π Z.o₁ o' m Z.K hA Z.hecke he hsu
    inferInstance hq'
  obtain ⟨π₂, ⟨hb, ⟨m₂⟩⟩, -⟩ := Xo.rep _ _ hred o₂
  refine ⟨{ toKerScheme := Z, π₂ := π₂, base₂ := hb, o₂ := o₂, m₂ := m₂, ψ := ψ, isog := hi, ker := hk, univ := ?_ }⟩
  intro S s hS o o' ψ' ⟨hi', K', hk', hH⟩
  have := o'.proper
  have het := (etSet_of_kerSet S _ _ ψ' K' inferInstance hi'.1.2.1 hi'.1.2.2.1 hk').1
  obtain ⟨h, ⟨hh, n₁, hn₁⟩, hu⟩ := Z.rep S s hS o K' het hH
  refine ⟨h, ⟨hh, ?_⟩, ?_⟩
  · obtain ⟨o₃, ⟨n₃⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ s h rfl rfl
      (by rw [hh]; simp [spMap]) o₂
    obtain ⟨⟨ψ₃, hψ₃, -⟩, hall⟩ := GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject E H D l p _ _ _ _ h Z.o₁ o₂ o o₃ n₁ n₃ ψ
    obtain ⟨hi₃, hk₃⟩ := hall ψ₃ hψ₃
    have hk₃' := hk₃ Z.K hi.1.1 hk
    rw [← hn₁] at hk₃'
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base E H D l p S s o o' o₃ ψ' ψ₃ K' hA.2.2.1 hA.2.2.2.2 hi' (hi₃ hi) hk' hk₃'
      (corr_heckeSet_kill o.t hA.2.2.2.1 hH)
    have hc := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o₂ o₃ o').2 h (𝟙 S) n₃).1 m
    have hc' : ∀ g : S ⟶ Z.Hk, g = h → (∃ m'' : ObjMap o' o₂ g, m''.toSABMap.φ = m.toSABMap.φ ≫ n₃.toSABMap.φ) →
        ∃ m'' : ObjMap o' o₂ h, m''.toSABMap.φ = m.toSABMap.φ ≫ n₃.toSABMap.φ := by
      rintro g rfl hg
      exact hg
    obtain ⟨n₂, hn₂⟩ := hc' _ (Category.id_comp h) hc
    exact ⟨n₁, n₂, by rw [hn₂, ← Category.assoc, hm, hψ₃]⟩
  · rintro h' ⟨hh', n₁', n₂', e⟩
    have hk₃ := ((GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject E H D l p _ _ _ _ h' Z.o₁ o₂ o o' n₁' n₂' ψ).2 ψ' e).2 Z.K hi.1.1 hk
    exact hu h' ⟨hh', n₁', corr_kerSet_unique hk' hk₃⟩

end GlobalTheory.HkFam
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_heckeCorrespondenceScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), 1 ≤ D.p + D.q → admitted l 𝔓 p → Nonempty (Corr Xo 𝔓 p i) := by
  atlas_forward_decl GlobalTheory.HkFam.corr_nonempty
end
