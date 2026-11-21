import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFinrankEqNormPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri

section
open scoped NumberField

namespace GlobalTheory.TateTorsion

theorem natCard_eq_of_surj_fibres {α β γ : Type*} (g : α → β) (f : α → γ)
    (hg : Function.Surjective g) (hf : Function.Surjective f)
    (h : ∀ x y, g x = g y ↔ f x = f y) : Nat.card β = Nat.card γ := by
  refine Nat.card_congr
    { toFun := fun b => f (Function.surjInv hg b)
      invFun := fun c => g (Function.surjInv hf c)
      left_inv := ?_
      right_inv := ?_ }
  · intro b
    have h1 := Function.surjInv_eq hf (f (Function.surjInv hg b))
    show g (Function.surjInv hf (f (Function.surjInv hg b))) = b
    rw [(h _ _).mpr h1, Function.surjInv_eq hg]
  · intro c
    have h1 := Function.surjInv_eq hg (g (Function.surjInv hf c))
    show f (Function.surjInv hg (g (Function.surjInv hf c))) = c
    rw [(h _ _).mp h1, Function.surjInv_eq hf]

theorem repr_mod_eq_zero_iff {M : Type*} [AddCommGroup M] {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (l : ℕ)
    (z : M) : (∀ i, ((b.equivFun z i : ℤ) : ZMod l) = 0) ↔ ∃ y, z = l • y := by
  constructor
  · intro hz
    refine ⟨b.equivFun.symm (fun i => b.equivFun z i / (l : ℤ)), ?_⟩
    apply b.equivFun.injective
    rw [← Nat.cast_smul_eq_nsmul ℤ, map_zsmul, LinearEquiv.apply_symm_apply]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hz i))]
  · rintro ⟨y, rfl⟩ i
    rw [← Nat.cast_smul_eq_nsmul ℤ, map_zsmul]
    simp

end GlobalTheory.TateTorsion

open GlobalTheory.TateTorsion in
theorem GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (l : ℕ),
    l.Prime → l ≠ p → Nat.card {q : Q // q ^ l = 1} = l ^ (D.m * D.n * Module.finrank ℚ D.F) := by
  intro p hp D k _ Q _ act e I l hl hne
  haveI := D.freeLa
  haveI := D.finLa
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hl0 : 0 < l := hl.pos
  have hcop : l.Coprime p := (Nat.coprime_primes hl hp.out).mpr hne
  let b := Module.finBasisOfFinrankEq ℤ D.La D.rankLa
  let g : D.La → {q : Q // q ^ l = 1} := fun x => ⟨I.ev l x, (I.onto l hl0 hcop _).mpr ⟨x, rfl⟩⟩
  let f : D.La → (Fin (D.m * D.n * Module.finrank ℚ D.F) → ZMod l) :=
    fun x i => ((b.equivFun x i : ℤ) : ZMod l)
  have hg : Function.Surjective g := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx⟩ := (I.onto l hl0 hcop q).mp hq
    exact ⟨x, Subtype.ext hx⟩
  have hf : Function.Surjective f := by
    intro c
    refine ⟨b.equivFun.symm (fun i => ((c i).val : ℤ)), ?_⟩
    funext i
    simp only [f, LinearEquiv.apply_symm_apply, Int.cast_natCast, ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id]
  have hgf : ∀ x y, g x = g y ↔ f x = f y := by
    intro x y
    have e1 : g x = g y ↔ I.ev l (x - y) = 1 := by
      rw [Subtype.ext_iff]
      show I.ev l x = I.ev l y ↔ _
      have : I.ev l x = I.ev l (x - y) * I.ev l y := by rw [← I.add, sub_add_cancel]
      rw [this]
      constructor
      · intro h; simpa using h
      · intro h; simp [h]
    have e2 : f x = f y ↔ ∀ i, ((b.equivFun (x - y) i : ℤ) : ZMod l) = 0 := by
      simp only [f, map_sub, Pi.sub_apply, Int.cast_sub, sub_eq_zero, funext_iff]
    rw [e1, e2, repr_mod_eq_zero_iff, I.ker l hl0 hcop]
  rw [natCard_eq_of_surj_fibres g f hg hf hgf, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
end

section
open scoped NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lTorsion_eq_pow_of_tateSimilitude : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (l : ℕ),
    l.Prime → l ≠ p → Nat.card {q : Q // q ^ l = 1} = l ^ (D.m * D.n * Module.finrank ℚ D.F) := by
  first | (exact @GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one) | (exact GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one) | (intros; apply GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

theorem isIsogDeg_of_isFinite_of_finrank_origin :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (φ : A ⟶ A), IsMonHom φ → IsFinite φ.left → ∀ d : ℕ,
    φ.left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) = d →
    GlobalTheory.IwLevel.IsIsogDeg φ d := by
  intro k _ _ A _ hA φ _ hfin d hd
  obtain ⟨hflat, hsurj⟩ := GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A hA φ inferInstance hfin
  have := hA.smooth
  have := hA.geomConnected
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have : LocallyOfFinitePresentation (φ.left ≫ A.hom) := by
    rw [Over.w]; infer_instance
  have := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp φ.left A.hom
  refine ⟨hfin, hflat, hsurj, fun y => ?_⟩
  rw [← hd]
  exact (Scheme.Hom.isLocallyConstant_finrank φ.left).apply_eq_of_preconnectedSpace y _

end GlobalTheory.IwLevel
end
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_degree_of_fibre_rank : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (φ : A ⟶ A), IsMonHom φ → IsFinite φ.left → ∀ d : ℕ,
    φ.left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) = d →
    GlobalTheory.IwLevel.IsIsogDeg φ d := by
  first | (exact @GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin) | (exact GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin) | (intros; apply GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_and_finrank_act_eq_norm_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ), l.Prime → (l : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F) →
    ∀ c : 𝓞 F, c ≠ 0 → IsFinite (ρ.act c).left ∧
      (ρ.act c).left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) =
        (Algebra.norm ℤ c).natAbs ^ d := by
  first | (exact @GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow) | (exact GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow) | (intros; apply GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbEnd

theorem isFinite_of_isFinite_geomFibres :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (φ : A ⟶ A),
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), IsFinite ((Over.pullback t).map φ).left) →
    IsFinite φ.left := by
  intro S A _ hA φ hgeo
  haveI : IsProper A.hom := hA.proper
  haveI : IsProper (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance
  haveI : IsProper φ.left := IsProper.of_comp φ.left A.hom
  haveI : LocallyQuasiFinite φ.left := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton φ.left fun y => ?_
    let K := AlgebraicClosure (A.left.residueField y)
    let u : Spec (CommRingCat.of K) ⟶ A.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (A.left.residueField y) K)) ≫
        A.left.fromSpecResidueField y
    let t := u ≫ A.hom
    haveI := hgeo K t
    let φ' := ((Over.pullback t).map φ).left
    let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
    have hup : u p = y := Scheme.fromSpecResidueField_apply y _
    let v : Spec (CommRingCat.of K) ⟶ pullback A.hom t := pullback.lift u (𝟙 _) (by simp [t])
    refine ((φ'.finite_preimage_singleton (v p)).image (pullback.fst A.hom t)).subset fun x hx => ?_
    have hx' : φ.left x = u p := by rw [hup]; exact hx
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := u) x p hx'
    let m : pullback φ.left u ⟶ pullback A.hom t :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
        rw [← Over.w φ, ← Category.assoc, pullback.condition, Category.assoc])
    have hm1 : m ≫ pullback.fst A.hom t = pullback.fst _ _ := pullback.lift_fst _ _ _
    have hφ1 : φ' ≫ pullback.fst A.hom t = pullback.fst A.hom t ≫ φ.left :=
      (GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ).w.symm
    have hφ2 : φ' ≫ pullback.snd A.hom t = pullback.snd A.hom t := pullback.lift_snd _ _ _
    have hmv : m ≫ φ' = pullback.snd φ.left u ≫ v := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφ1, ← Category.assoc, hm1, Category.assoc, pullback.lift_fst, pullback.condition]
      · rw [Category.assoc, hφ2, pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    refine ⟨m w, ?_, ?_⟩
    · change φ' (m w) = v p
      rw [← Scheme.Hom.comp_apply, hmv, Scheme.Hom.comp_apply, hw2]
    · rw [← Scheme.Hom.comp_apply, hm1, hw1]
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ.left

end GlobalTheory.AbEnd
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_endomorphism_finite_of_geometric_fibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (φ : A ⟶ A),
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), IsFinite ((Over.pullback t).map φ).left) →
    IsFinite φ.left := by
  first | (exact @GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres) | (exact GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres) | (intros; apply GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem flat_of_isFinite_of_flat_geometric_fibres_over :
    ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom →
    LocallyOfFinitePresentation Y.hom → IsFinite f.left →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Flat ((Over.pullback t).map f).left) →
    Flat f.left :=
  fun S X Y f h1 h0 h2 h3 H =>
    flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S X Y f h1 h0 h2 h3 H

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_finite_flat_geometric_fibres_over_base : ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom →
    LocallyOfFinitePresentation Y.hom → IsFinite f.left →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Flat ((Over.pullback t).map f).left) →
    Flat f.left := by
  first | (exact @GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over) | (exact GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over) | (intros; apply GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTTors

theorem isIsogDeg_of_geomFibres (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (φ : A ⟶ A)
    (d : ℕ) (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S),
      GlobalTheory.IwLevel.IsIsogDeg ((Over.pullback t).map φ) d) : GlobalTheory.IwLevel.IsIsogDeg φ d := by
  have := hA.smooth
  have hfin : IsFinite φ.left := GlobalTheory.T.abelianScheme_endomorphism_finite_of_geometric_fibres S A hA φ fun k _ _ t => (h k t).fin
  have hflat : Flat φ.left :=
    GlobalTheory.T.flat_of_finite_flat_geometric_fibres_over_base S A A φ inferInstance inferInstance inferInstance hfin fun k _ _ t => (h k t).flat
  refine ⟨hfin, hflat, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres φ fun k _ _ t => (h k t).surj, fun y => ?_⟩
  let K := AlgebraicClosure (A.left.residueField y)
  let u : Sp K ⟶ A.left := spMap (algebraMap (A.left.residueField y) K) ≫ A.left.fromSpecResidueField y
  let t := u ≫ A.hom
  let q : Sp K := (⊥ : PrimeSpectrum K)
  let v : Sp K ⟶ pullback A.hom t := pullback.lift u (𝟙 _) (by simp [t])
  have hP := GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ hP (v q)
  have hv : pullback.fst A.hom t (v q) = y := by
    rw [← Scheme.Hom.comp_apply]
    have : v ≫ pullback.fst A.hom t = u := pullback.lift_fst _ _ _
    rw [this]
    exact (Scheme.Hom.comp_apply _ _ q).trans (Scheme.fromSpecResidueField_apply y _)
  rw [hv] at e
  rw [← e]
  exact (h K t).rank _

theorem isIsogDeg_fibre (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A)
    (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ) (hl : l.Prime) (hl0 : (l : k) ≠ 0)
    (hcard : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F))
    (c : 𝓞 F) (hc : c ≠ 0) : GlobalTheory.IwLevel.IsIsogDeg (ρ.act c) ((Algebra.norm ℤ c).natAbs ^ d) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isFinite_and_finrank_act_eq_norm_pow k A hA F ρ l d hl hl0 hcard c hc
  exact GlobalTheory.T.isogeny_degree_of_fibre_rank k A hA _ (ρ.hom c) h1 _ h2

def pullAct {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {S : Scheme.{0}} {A : Over S} [GrpObj A]
    [IsCommMonObj A] (act : GlobalTheory.UPel.HT.OActN D.O A) {T : Scheme.{0}} (t : T ⟶ S) :
    OAct (𝓞 D.F) ((Over.pullback t).obj A) where
  act c := (Over.pullback t).map (act.act (algebraMap (𝓞 D.F) D.O c))
  hom c := by have := act.hom (algebraMap (𝓞 D.F) D.O c); infer_instance
  one := by rw [map_one, act.one, CategoryTheory.Functor.map_id]
  mul a b := by rw [mul_comm a b, map_mul, act.mul, Functor.map_comp]
  add a b := by
    rw [map_add, act.add]
    exact map_mul (Over.pullback t).homMonoidHom _ _

theorem isIsogDeg_intAct : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (c : 𝓞 D.F),
    c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n)) := by
  intro p _ D R _ b N S s o c hc
  refine isIsogDeg_of_geomFibres S o.A o.ab _ _ fun k _ _ t => ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ s)
  have hβ : t ≫ s = spMap φ.hom := by rw [← hφ]; rfl
  obtain ⟨I, -⟩ := o.geom k t φ.hom hβ
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hlp' : l ≠ p := by omega
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out)).2 hlp'
  have hl0 : (l : k) ≠ 0 := by
    have := (b.unit l hcop).map φ.hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hcount := GlobalTheory.T.card_lTorsion_eq_pow_of_tateSimilitude p D k _ _ _ I l hl hlp'
  let e := GlobalTheory.TorsionLift.ptsEquiv t o.A (𝟙_ (Over (Sp k))) t (Category.id_comp t)
  have hc2 : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback t).obj o.A // x ^ l = 1} =
      l ^ ((D.m * D.n) * Module.finrank ℚ D.F) := by
    rw [← hcount]
    refine Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)
    show x ^ l = 1 ↔ e x ^ l = 1
    rw [← map_pow, map_eq_one_iff e e.injective]
  exact isIsogDeg_fibre k _ (GlobalTheory.isAbelianScheme_pullback_obj t o.A o.ab) D.F (pullAct o.act t) l _ hl hl0 hc2 c hc

end GlobalTheory.HTTors
end
end
