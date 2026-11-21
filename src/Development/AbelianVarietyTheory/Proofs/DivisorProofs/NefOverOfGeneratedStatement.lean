import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionOpenCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBound

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_open_cover : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (R : L.B.ι → X.functionFieldˣ), IsRatSec L.B R → ∀ (l n : ℕ) (U : X → X.Opens) (s : X → Fin n → X.functionField), (∀ x, x ∈ U x) → (∀ (x : X) (i : L.B.ι) (x₀ : X), x₀ ∈ U x → x₀ ∈ L.B.U i → (l : k) ∈ (p x₀).asIdeal → (∀ J, RegAt x₀ (s x J * R i)) ∧ (∃ J, UnitAt x₀ (s x J * R i)) ∧ ∀ x', x₀ ∈ U x' → ∀ J, ¬ UnitAt x₀ ((s x J - s x' J) * R i)) → NefOver L l := by
  first | exact @GlobalTheory.HtGenCurve.nefOver_of_localGen | exact GlobalTheory.HtGenCurve.nefOver_of_localGen | (intros; apply GlobalTheory.HtGenCurve.nefOver_of_localGen <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen.IntPt

theorem top_le_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (t : Sp R ⟶ X) {W : X.Opens}
    (h : t (IsLocalRing.closedPoint R) ∈ W) : ⊤ ≤ t ⁻¹ᵁ W := fun p _ =>
  ((IsLocalRing.specializes_closedPoint p).map t.continuous).mem_open W.isOpen h

theorem w_eq_one_iff {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (c : e.O) :
    e.w c = 1 ↔ IsUnit c :=
  ⟨fun h => RegCrit.isUnit_of_one_le e c h.ge, fun h => OfModel.w_unit e h⟩

open GlobalTheory.TrueGeo.HorizPt in

theorem exists_intPt : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (W : V.X.Opens) (x : V.X), x ∈ W → (l : 𝓞 F) ∈ (V.p x).asIdeal → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal ∧ z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ x ⤳ yt (IsLocalRing.closedPoint e.O) ∧ ∀ g : V.X.functionField, RegAt (yt (IsLocalRing.closedPoint e.O)) g → (e.w (TrueGeo.valAt (z ≫ V.j) g) = 1 ↔ UnitAt (yt (IsLocalRing.closedPoint e.O)) g) := by
  intro F _ _ Y V l W x hx hl
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨x, hxU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, -⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U) 𝔪 h𝔪 1 one_ne_zero
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  have hc : yt (IsLocalRing.closedPoint e.O) = hU.fromSpec ⟨𝔪, h𝔪.isPrime⟩ := by
    change hU.fromSpec (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O)) = _
    congr 1
    exact PrimeSpectrum.ext h₂
  have hsp : x ⤳ yt (IsLocalRing.closedPoint e.O) := by
    have h0 : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ⤳ hU.fromSpec ⟨𝔪, h𝔪.isPrime⟩ :=
      ((PrimeSpectrum.le_iff_specializes _ ⟨𝔪, h𝔪.isPrime⟩).1 hle').map hU.fromSpec.continuous
    rw [hU.fromSpec_primeIdealOf] at h0
    rw [hc]
    exact h0
  have hl' : algebraMap (𝓞 F) Γ(V.X, U) (l : 𝓞 F) ∈ 𝔪 := by
    apply hle'
    have e1 : V.p x = (Spec.map (HorizPt.strHom V.p U)) (hU.primeIdealOf ⟨x, hxU⟩) := by
      rw [← fromSpec_str V.p hU]
      change V.p x = V.p (hU.fromSpec _)
      rw [hU.fromSpec_primeIdealOf]
    rw [e1] at hl
    exact hl
  have hv : (l : 𝓞 F) ∈ v.asIdeal := by
    have hm : φ (algebraMap (𝓞 F) Γ(V.X, U) (l : 𝓞 F)) ∈ IsLocalRing.maximalIdeal e.O := by
      rw [← Ideal.mem_comap, h₂]
      exact hl'
    have hlt : e.w ((φ (algebraMap (𝓞 F) Γ(V.X, U) (l : 𝓞 F)) : e.O) : AlgebraicClosure F) < 1 := by
      refine lt_of_le_of_ne ((e.mem_O _).1 (φ _).2) fun h => ?_
      exact (IsLocalRing.mem_maximalIdeal _).1 hm (RegCrit.isUnit_of_one_le e _ h.ge)
    rw [h₁, e.w_alg] at hlt
    exact (v.adicAbv_coe_lt_one_iff _ _).1 hlt
  refine ⟨v, e, V.pb.lift _ _ hw, yt, hv, V.pb.lift_snd _ _ hw, hy.symm, ?_, hsp, ?_⟩
  · intro p _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro g hg
    obtain ⟨W₀, hW₀, s, hs⟩ := hg.exists_fnOf
    have ht : ⊤ ≤ yt ⁻¹ᵁ W₀ := top_le_of_closedPoint yt hW₀
    have hb : below (V.pb.lift _ _ hw ≫ V.j) ∈ W₀ := by
      change (V.pb.lift _ _ hw ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ W₀
      rw [hy]
      exact ht trivial
    have ht' : ⊤ ≤ (V.pb.lift _ _ hw ≫ V.j) ⁻¹ᵁ W₀ := fun p _ => by
      change (V.pb.lift _ _ hw ≫ V.j) p ∈ W₀
      rw [hy]
      exact ht (x := spMap e.O.subtype p) trivial
    have hev := OfModel.eval_pull e.O.subtype (𝟙 V.X) (V.pb.lift _ _ hw ≫ V.j) yt
      (hy.symm.trans (Category.comp_id _).symm) (U := W₀) (W := W₀) le_rfl ht' ht s
    have hid : ((𝟙 V.X : V.X ⟶ V.X).appLE W₀ W₀ le_rfl).hom s = s := by
      have : (𝟙 V.X : V.X ⟶ V.X).appLE W₀ W₀ le_rfl = 𝟙 _ :=
        (Category.id_comp _).trans (V.X.presheaf.map_id _)
      rw [this]
      rfl
    rw [hid] at hev
    rw [← hs, OfModel.valAt_fnOf _ hb ht', hev, unitAt_fnOf_iff hW₀, ← RegCrit.isUnit_eval_iff yt ht s]
    exact w_eq_one_iff e _

end GlobalTheory.HtGen.IntPt
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_closure_extension : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (W : V.X.Opens) (x : V.X), x ∈ W → (l : 𝓞 F) ∈ (V.p x).asIdeal → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal ∧ z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ x ⤳ yt (IsLocalRing.closedPoint e.O) ∧ ∀ g : V.X.functionField, RegAt (yt (IsLocalRing.closedPoint e.O)) g → (e.w (TrueGeo.valAt (z ≫ V.j) g) = 1 ↔ UnitAt (yt (IsLocalRing.closedPoint e.O)) g) := by
  first | exact @GlobalTheory.HtGen.IntPt.exists_intPt | exact GlobalTheory.HtGen.IntPt.exists_intPt | (intros; apply GlobalTheory.HtGen.IntPt.exists_intPt <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.HtGen.RegOver

theorem mem_range_j {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) {x : V.X}
    (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

open GlobalTheory.TrueGeo.HorizPt in

theorem exists_horizPt_over {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (W : V.X.Opens) (z : V.X)
    (g : Γ(V.X, W)) (hz : z ∈ W) (hg : g ≠ 0) (hzg : z ∉ V.X.basicOpen g) (a : 𝓞 F) (ha : a ∈ (V.p z).asIdeal) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      a ∈ v.asIdeal ∧ y ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = y ≫ V.j ∧
      ⊤ ≤ yt ⁻¹ᵁ W ∧ yt (IsLocalRing.closedPoint e.O) ∉ V.X.basicOpen g ∧ below (y ≫ V.j) ∈ V.X.basicOpen g := by
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (GlobalTheory.TrueGeo.HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  set g' : Γ(V.X, U) := V.X.presheaf.map (homOfLE hle).op g with hg'
  have hg0 : g' ≠ 0 := fun h => hg (map_injective_of_isIntegral V.X (homOfLE hle) (by rw [← hg', h, map_zero]))
  have hb : ∀ x : PrimeSpectrum Γ(V.X, U), hU.fromSpec x ∈ V.X.basicOpen g ↔ g' ∉ x.asIdeal := by
    intro x
    have h₁ : hU.fromSpec x ∈ U := by
      have := hU.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨x, rfl⟩
    have h₂ : hU.fromSpec x ∈ V.X.basicOpen g' ↔ g' ∉ x.asIdeal := by
      change x ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen g' ↔ _
      rw [hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← h₂, hg', Scheme.basicOpen_res]
    exact ⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩
  have hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra h
    have := (hb _).2 h
    rw [hU.fromSpec_primeIdealOf] at this
    exact hzg this
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U) 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  refine ⟨v, e, V.pb.lift _ _ hw, yt, ?_, V.pb.lift_snd _ _ hw, hy.symm, ?_, ?_, ?_⟩
  · have e₁ : V.p z = Spec.map (GlobalTheory.TrueGeo.HorizPt.strHom V.p U) (hU.primeIdealOf ⟨z, hzU⟩) := by
      rw [← fromSpec_str V.p hU]
      exact congrArg V.p (hU.fromSpec_primeIdealOf ⟨z, hzU⟩).symm
    rw [e₁] at ha
    have h₄ : algebraMap (𝓞 F) Γ(V.X, U) a ∈ 𝔪 := hle' ha
    rw [← h₂] at h₄
    by_contra hv
    refine (IsLocalRing.mem_maximalIdeal _).1 h₄ (GlobalTheory.TrueGeo.RegCrit.isUnit_of_one_le e _ ?_)
    rw [h₁ a, e.w_alg, ← FinitePlace.norm_embedding]
    exact ((FinitePlace.norm_eq_one_iff_notMem F v a).2 hv).ge
  · intro x _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro h
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (V.pb.lift _ _ hw ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
    have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'

open GlobalTheory.TrueGeo.RegCrit in

theorem regAt_of_integral_values_over : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (U : V.X.Opens) (g : V.X.functionField), (∀ z : V.G, V.j z ∈ U → RegAt (V.j z) g) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal → z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) → ∀ x ∈ U, (l : 𝓞 F) ∈ (V.p x).asIdeal → RegAt x g := by
  intro F _ _ Y V l U f hgen hf x hx hl
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  have : IsLocallyNoetherian V.X := LocallyOfFiniteType.isLocallyNoetherian V.p
  by_contra hreg
  obtain ⟨z, hz, hzero⟩ := GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal V.X V.normal x f hreg
  have hf0 : f ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have hzU : z ∈ U := hz.mem_open U.isOpen hx
  have hlz : (l : 𝓞 F) ∈ (V.p z).asIdeal := by
    have hne : (V.p z).asIdeal ≠ ⊥ := fun h => by
      obtain ⟨z', rfl⟩ := mem_range_j V h
      exact (zeroAt_iff.1 hzero).2 ((unitAt_iff (inv_ne_zero hf0)).2 ⟨hzero.regAt, (inv_inv f).symm ▸ hgen z' hzU⟩)
    have hle : (V.p z).asIdeal ≤ (V.p x).asIdeal :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2 (hz.map V.p.continuous))
    have hmax : (V.p z).asIdeal.IsMaximal := Ideal.IsPrime.isMaximal (R := 𝓞 F) (V.p z).isPrime hne
    rwa [hmax.eq_of_le (V.p x).isPrime.ne_top hle]
  obtain ⟨W₀, hzW, g₀, hg₀⟩ := hzero.regAt.exists_fnOf
  have hzW' : z ∈ W₀ ⊓ U := ⟨hzW, hzU⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(V.X, W₀ ⊓ U), ∀ h, fnOf _ h g = f⁻¹ :=
    ⟨resG V.X inf_le_left g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩
  have hg0 : g ≠ 0 := fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzW'), h, map_zero])
  have hzg : z ∉ V.X.basicOpen g := fun h =>
    (zeroAt_iff.1 hzero).2 (hg (gen_mem hzW') ▸ (unitAt_fnOf_iff hzW' _ g).2 h)
  obtain ⟨v, e, y, yt, hv, hy, hc, hW, hn, hu⟩ := exists_horizPt_over V _ z g hzW' hg0 hzg _ hlz
  have hle := hf v e y yt hv hy hc fun p hp => (hW hp).2
  have hu' : below (y ≫ V.j) ∈ V.X.basicOpen g := hu
  have hb : below (y ≫ V.j) ∈ W₀ ⊓ U := V.X.basicOpen_le g hu'
  have ht : ⊤ ≤ (y ≫ V.j) ⁻¹ᵁ (W₀ ⊓ U) := fun p _ => by
    change (y ≫ V.j) p ∈ W₀ ⊓ U
    rw [← hc]
    exact hW (x := spMap e.O.subtype p) trivial
  have hunit : UnitAt (below (y ≫ V.j)) f⁻¹ := hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'
  have hfu : UnitAt (below (y ≫ V.j)) f := inv_inv f ▸ hunit.inv
  have hmul := OfModel.valAt_mul (y ≫ V.j) hfu.regAt hunit.regAt
  have hone : TrueGeo.valAt (y ≫ V.j) (1 : V.X.functionField) = 1 := by
    have := OfModel.valAt_algebraMap (y ≫ V.j) 1
    rwa [map_one, map_one] at this
  have hev := OfModel.eval_pull e.O.subtype (𝟙 V.X) (y ≫ V.j) yt (hc.trans (Category.comp_id _).symm)
    (U := W₀ ⊓ U) (W := W₀ ⊓ U) le_rfl ht hW g
  have hid : ((𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl).hom g = g := by
    have : (𝟙 V.X : V.X ⟶ V.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl = 𝟙 _ :=
      (Category.id_comp _).trans (V.X.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev] at hmul
  refine hn ((isUnit_eval_iff yt hW g).1 (isUnit_of_one_le e _ ?_))
  have h₁ := congrArg e.w hmul
  rw [map_one, map_mul] at h₁
  exact h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hle)

end GlobalTheory.HtGen.RegOver
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_place_condition : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (U : V.X.Opens) (g : V.X.functionField), (∀ z : V.G, V.j z ∈ U → RegAt (V.j z) g) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal → z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) → ∀ x ∈ U, (l : 𝓞 F) ∈ (V.p x).asIdeal → RegAt x g := by
  first | exact @GlobalTheory.HtGen.RegOver.regAt_of_integral_values_over | exact GlobalTheory.HtGen.RegOver.regAt_of_integral_values_over | (intros; apply GlobalTheory.HtGen.RegOver.regAt_of_integral_values_over <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen.Crit

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem asIdeal_p_j (V : Cover Y) (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
  rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
  change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
  have := ((V.π ≫ Y.str) y).isPrime
  rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j (V : Cover Y) {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem j_gen_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans
        (asIdeal_p_j V _).le)
  obtain ⟨y, hy⟩ := mem_range_j V h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem nefOver_of_genOver : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p)
    (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (l : ℕ),
    Norms V L f a φ → GenOver V f φ l → NefOver L l := by
  intro F _ _ Y V L f a φ l ⟨r, hr, hu, _, hf⟩ ⟨n, U, s, hUx, hreg, hgen⟩
  haveI := CoverHt.isPreimmersion_j V
  have hη := j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)),
      ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) := fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ (y : Sp (AlgebraicClosure F) ⟶ V.G) (g : V.X.functionField), valAt (y ≫ V.j) g = valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hrg : ∀ (z : V.G) (g : V.X.functionField), RegAt (V.j z) g ↔ RegAt z (ρ g) :=
    fun z g => (SmallSec.regAt_fnMap_iff V.j hη).symm
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr

  let R : L.B.ι → V.X.functionFieldˣ := fun i => Units.map ρ.symm.toMonoidHom (r fun _ => i)
  let s' : V.X → Fin n → V.X.functionField := fun x J => ρ.symm (s x J)
  have eR : ∀ (t : V.G.functionField) (i : L.B.ι), t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) =
      ρ (ρ.symm t * (R i : V.X.functionField)) := by
    intro t i
    rw [map_mul, ρ.apply_symm_apply]
    exact congrArg _ (ρ.apply_symm_apply _).symm
  have mem_pull : ∀ (z : V.G) (i : L.B.ι), V.j z ∈ L.B.U i → z ∈ (L.B.pull V.j).U (fun _ => i) :=
    fun z i h => Set.mem_iInter.2 fun _ => h

  have split : ∀ (t : V.G.functionField) (i : L.B.ι) (z : V.G), V.j z ∈ L.B.U i →
      t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) =
        t / V.φ (f (V.π z)) * (V.φ (f (V.π z)) * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) := by
    intro t i z hz
    have h0 : V.φ (f (V.π z)) ≠ 0 := left_ne_zero_of_mul (hu _ _ (mem_pull z i hz)).ne_zero
    field_simp
  have regG : ∀ (t : V.G.functionField) (i : L.B.ι) (z : V.G), V.j z ∈ L.B.U i → RegAt z (t / V.φ (f (V.π z))) →
      RegAt z (t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) := by
    intro t i z hz ht
    rw [split t i z hz]
    exact ht.mul (hu _ _ (mem_pull z i hz)).regAt
  have valG : ∀ (t : V.G.functionField) (i : L.B.ι) (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v)
      (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (hz : z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F))),
      spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U i → RegAt (below z) (t / V.φ (f (V.π (below z)))) →
      e.w (valAt z (t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField))) =
        e.w (valAt z (t / V.φ (f (V.π (below z))))) *
          Real.exp (φ v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩) := by
    intro t i v e z yt hz e₂ hU ht
    have hpt : V.j (below z) ∈ L.B.U i := by
      change (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ _
      rw [← e₂]
      exact hU (Set.mem_univ _)
    have hun := hu _ _ (mem_pull _ i hpt)
    have H : φ v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ =
        Real.log (e.w (valAt z (V.φ (f (V.π (below z))) * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)))) :=
      hf v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt (fun _ => i) rfl e₂ hU
    rw [H, Real.exp_log (e.w.pos (SmallSec.valAt_ne_zero hun)), split t i _ hpt,
      SmallSec.valAt_mul ht hun.regAt, map_mul]
  refine GlobalTheory.T.regular_section_open_cover (𝓞 F) V.X V.p Y.dim V.ar L R hR l n U s' hUx ?_
  intro x i x₀ hx₀ hi₀ hl₀

  have regA : ∀ (J : Fin n) (c : V.X), c ∈ U x → c ∈ L.B.U i → (l : 𝓞 F) ∈ (V.p c).asIdeal →
      RegAt c (s' x J * R i) := by
    intro J c hc hic hlc
    refine GlobalTheory.T.integral_point_place_condition F Y V l (U x ⊓ L.B.U i) _ (fun z hz => ?_) (fun v e z yt hlv hz e₂ hU => ?_) c ⟨hc, hic⟩ hlc
    · rw [hrg, ← eR]
      exact regG _ i z hz.2 (hreg x J z hz.1)
    · have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ U x ⊓ L.B.U i := by
        rw [← e₂]
        exact hU (Set.mem_univ _)
      have hUx' : ⊤ ≤ yt ⁻¹ᵁ U x := fun w hw => (hU hw).1
      have hUi : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun w hw => (hU hw).2
      rw [hv, ← eR, valG _ i v e z yt hz e₂ hUi (hreg x J _ hpt.1)]
      exact (hgen v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt hlv rfl e₂ x hUx').1 J
  refine ⟨fun J => regA J x₀ hx₀ hi₀ hl₀, ?_, ?_⟩
  · obtain ⟨v, e, z, yt, hlv, hz, e₂, hW, hsp, hiff⟩ := GlobalTheory.T.integral_point_closure_extension F Y V l (U x ⊓ L.B.U i) x₀ ⟨hx₀, hi₀⟩ hl₀
    have hcW : yt (IsLocalRing.closedPoint e.O) ∈ U x ⊓ L.B.U i := hW (Set.mem_univ _)
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ U x ⊓ L.B.U i := by
      rw [← e₂]
      exact hW (Set.mem_univ _)
    have hlc : (l : 𝓞 F) ∈ (V.p (yt (IsLocalRing.closedPoint e.O))).asIdeal :=
      (PrimeSpectrum.le_iff_specializes _ _).2 (hsp.map V.p.continuous) hl₀
    have hUx' : ⊤ ≤ yt ⁻¹ᵁ U x := fun w hw => (hW hw).1
    have hUi : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun w hw => (hW hw).2
    obtain ⟨J, hJ⟩ := (hgen v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt hlv rfl e₂ x hUx').2.1
    have hunit : UnitAt (yt (IsLocalRing.closedPoint e.O)) (s' x J * R i) := by
      refine (hiff _ (regA J _ hcW.1 hcW.2 hlc)).1 ?_
      rw [hv, ← eR, valG _ i v e z yt hz e₂ hUi (hreg x J _ hpt.1)]
      exact hJ
    obtain ⟨W', hW', hall⟩ := hunit.exists_nhds
    exact ⟨J, hall x₀ (hsp.mem_open W'.isOpen hW')⟩
  · intro x' hx₀' J hJ
    obtain ⟨W', hW', hall⟩ := hJ.exists_nhds
    obtain ⟨v, e, z, yt, hlv, hz, e₂, hW, hsp, hiff⟩ :=
      GlobalTheory.T.integral_point_closure_extension F Y V l (W' ⊓ (U x ⊓ (U x' ⊓ L.B.U i))) x₀ ⟨hW', hx₀, hx₀', hi₀⟩ hl₀
    have hcW : yt (IsLocalRing.closedPoint e.O) ∈ W' ⊓ (U x ⊓ (U x' ⊓ L.B.U i)) := hW (Set.mem_univ _)
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ W' ⊓ (U x ⊓ (U x' ⊓ L.B.U i)) := by
      rw [← e₂]
      exact hW (Set.mem_univ _)
    have hUx' : ⊤ ≤ yt ⁻¹ᵁ U x := fun w hw => (hW hw).2.1
    have hUx'' : ⊤ ≤ yt ⁻¹ᵁ U x' := fun w hw => (hW hw).2.2.1
    have hUi : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun w hw => (hW hw).2.2.2
    have hc := hall _ hcW.1
    have h1 := (hiff _ hc.regAt).2 hc
    have hlt := (hgen v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt hlv rfl e₂ x hUx').2.2 x' hUx'' J
    have hd : RegAt (below z) ((s x J - s x' J) / V.φ (f (V.π (below z)))) := by
      have hm1 : RegAt (below z) (-1 : V.G.functionField) := ⟨-1, by simp⟩
      rw [show (s x J - s x' J) / V.φ (f (V.π (below z))) =
          s x J / V.φ (f (V.π (below z))) + (-1) * (s x' J / V.φ (f (V.π (below z)))) by ring]
      exact (hreg x J _ hpt.2.1).add (hm1.mul (hreg x' J _ hpt.2.2.1))
    have e₃ : s' x J - s' x' J = ρ.symm (s x J - s x' J) := (map_sub ρ.symm _ _).symm
    rw [e₃, hv, ← eR, valG _ i v e z yt hz e₂ hUi hd] at h1
    change e.w (valAt z ((s x J - s x' J) / V.φ (f (V.π (below z))))) * _ < 1 at hlt
    rw [h1] at hlt
    exact lt_irrefl _ hlt

end GlobalTheory.HtGen.Crit
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_over_of_generated : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (φ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (l : ℕ), Norms V L f a φ → GenOver V f φ l → NefOver L l := by
  first | exact @GlobalTheory.HtGen.Crit.nefOver_of_genOver | exact GlobalTheory.HtGen.Crit.nefOver_of_genOver | (intros; apply GlobalTheory.HtGen.Crit.nefOver_of_genOver <;> assumption)
end
