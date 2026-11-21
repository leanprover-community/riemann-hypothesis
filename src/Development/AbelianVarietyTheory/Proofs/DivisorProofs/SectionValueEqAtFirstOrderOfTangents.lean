import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.BaseCh

variable {K K' : Type} [Field K] [Field K']

abbrev prj (x : KeyIn K) (f : K →+* K') : ((Over.pullback (spMap f)).obj x.P.A).left ⟶ x.P.A.left :=
  pullback.fst x.P.A.hom (spMap f)

theorem isGrpPullback_prj (x : KeyIn K) (f : K →+* K') :
    IsGrpPullback ((Over.pullback (spMap f)).obj x.P.A) x.P.A (spMap f) (prj x f) :=
  isGrpPullback_pullback x.P.A (spMap f)

def pol (x : KeyIn K) (f : K →+* K') : Out.PolAV (Sp K') :=
  { A := (Over.pullback (spMap f)).obj x.P.A
    isAb := Out.TLinPf.isAb_pullback (spMap f) x.P.A x.P.isAb
    g := x.P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (isGrpPullback_prj x f).1
      x.P.smoothDim
    L := x.P.L.pull (prj x f)
    isLB := pull_isLB x.P.isLB (prj x f)
    rigid := PolBaseChange.rigidified_pull (isGrpPullback_prj x f) x.P.rigid
    sym := PolBaseChange.sym_pull (isGrpPullback_prj x f) x.P.sym
    ample := relAmple_pull (isGrpPullback_prj x f).1 x.P.isLB (pull_isLB x.P.isLB (prj x f))
      ((isGen_iff _).1 (idIso_isGen (pull_isLB x.P.isLB (prj x f)))) ⊤ (isAffineOpen_top _) (fun _ => trivial) x.P.ample
    ktriv := kTriv_pull (isGrpPullback_prj x f) x.P.isLB (pull_isLB x.P.isLB (prj x f))
      ((isGen_iff _).1 (idIso_isGen (pull_isLB x.P.isLB (prj x f)))) x.P.ktriv }

theorem eSec_prj (x : KeyIn K) (f : K →+* K') : eSec (pol x f).A ≫ prj x f = spMap f ≫ eSec x.P.A :=
  PolBaseChange.eSec_comm (isGrpPullback_prj x f)

theorem exists_th (x : KeyIn K) (f : K →+* K') :
    ∃ s' : (pol x f).L.Sec, ∀ (Z : Scheme) (r : Z ⟶ (pol x f).A.left) (z : Z) (j : x.P.L.ι) (k : (pol x f).L.ι),
      prj x f (r z) ∈ x.P.L.U j → r z ∈ (pol x f).L.U k →
        gs (r ≫ prj x f) z (x.P.L.U j) (x.th.f j) = ↑(gw (idIso (pol x f).L) r z j k) * gs r z ((pol x f).L.U k) (s'.f k) :=
  sec_pull_down ((isGen_iff _).1 (idIso_isGen (pull_isLB x.P.isLB (prj x f)))) x.P.isLB (pull_isLB x.P.isLB (prj x f)) x.th

def th (x : KeyIn K) (f : K →+* K') : (pol x f).L.Sec := Classical.choose (exists_th x f)

theorem th_spec (x : KeyIn K) (f : K →+* K') (Z : Scheme) (r : Z ⟶ (pol x f).A.left) (z : Z) (j : x.P.L.ι)
    (k : (pol x f).L.ι) (hj : prj x f (r z) ∈ x.P.L.U j) (hk : r z ∈ (pol x f).L.U k) :
    gs (r ≫ prj x f) z (x.P.L.U j) (x.th.f j) = ↑(gw (idIso (pol x f).L) r z j k) * gs r z ((pol x f).L.U k) ((th x f).f k) :=
  Classical.choose_spec (exists_th x f) Z r z j k hj hk

def rig (x : KeyIn K) (f : K →+* K') : ((pol x f).L.pull (eSec (pol x f).A)).Gen :=
  rigPullOf (G' := (pol x f).A) (G := x.P.A) (prj x f) (spMap f) (eSec_prj x f) x.P.L x.rig

theorem rig_isGen (x : KeyIn K) (f : K →+* K') : (rig x f).IsGen :=
  Out.LBxP.isGen_pullAlong x.P.L (prj x f) (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1)
    (fun _ => eSec (pol x f).A) (fun _ => eSec_prj x f) x.rig x.rig_gen

theorem vec_sq (x : KeyIn K) (f : K →+* K') (i : Fin x.P.g) :
    (spMap (Chart.dualMapR f) ≫ (x.v i).left) ≫ x.P.A.hom = (epsR K').hom ≫ spMap f := by
  rw [Category.assoc, Over.w]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

def vec (x : KeyIn K) (f : K →+* K') (i : Fin x.P.g) : epsR K' ⟶ (pol x f).A :=
  Over.homMk ((isGrpPullback_prj x f).1.lift _ _ (vec_sq x f i)) ((isGrpPullback_prj x f).1.lift_snd _ _ _)

theorem vec_prj (x : KeyIn K) (f : K →+* K') (i : Fin x.P.g) :
    (vec x f i).left ≫ prj x f = spMap (Chart.dualMapR f) ≫ (x.v i).left :=
  (isGrpPullback_prj x f).1.lift_fst _ _ _

theorem th_ne (x : KeyIn K) (f : K →+* K') (s : Sp K') :
    ∃ y, (pol x f).A.hom y = s ∧ y ∈ nonzeroLocus (th x f) := by
  have h := isGrpPullback_prj x f
  obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs (prj x f) y _ (x.th.f k)) := by rw [gs_stalkMap (prj x f) y _ hk]; exact u.map _
  have e := th_spec x f _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  erw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

def key (x : KeyIn K) (f : K →+* K') : KeyIn K' :=
  ⟨pol x f, x.g_pos, rig x f, rig_isGen x f, th x f, th_ne x f, vec x f,
    by have := x.P.isAb.smooth; exact Chart.isLieBasis_baseChange f (isGrpPullback_prj x f) x.basis (vec_prj x f)⟩

theorem powIso_le {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (n : ℕ)
    (p : (LB.div (lbPow (L.pull φ) n) ((lbPow L n).pull φ)).ι) :
    (LB.div (lbPow (L.pull φ) n) ((lbPow L n).pull φ)).U p ≤
      φ ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p.2 PUnit.unit PUnit.unit)) := by
  intro y hy
  obtain ⟨h1, h2⟩ := hy
  have a1 := Set.mem_iInter.1 (Set.mem_iInter.1 h1 PUnit.unit) PUnit.unit
  have a2 := Set.mem_iInter.1 (Set.mem_iInter.1 h2 PUnit.unit) PUnit.unit
  exact ⟨a1, a2⟩

def powIso {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (n : ℕ) : LB.Iso ((lbPow L n).pull φ) (lbPow (L.pull φ) n) :=
  ⟨fun p => res (powIso_le L φ n p)
      (pullU φ _ (L.g (p.1 PUnit.unit PUnit.unit) (p.2 PUnit.unit PUnit.unit))) ^ (n : ℤ)⟩

end GlobalTheory.MBLow.BaseCh
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.BaseChRig

theorem valR_map {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE h).op).hom s) = valR x U s := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => h (hV hq)
  unfold valR
  rw [dif_pos hV, dif_pos hU, ← Scheme.Hom.map_appLE x hV (homOfLE h).op]
  rfl

theorem valR_app {A : Type} [CommRing A] {X Y : Scheme.{0}} (x : Sp A ⟶ Y) (g : Y ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ U)) (s : Γ(X, U)) :
    valR x (g ⁻¹ᵁ U) ((g.app U).hom s) = valR (x ≫ g) U s := by
  have hU' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := hU
  unfold valR
  rw [dif_pos hU, dif_pos hU', Scheme.Hom.comp_appLE]
  rfl

theorem valR_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X)
    {U : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valR (spMap f ≫ x) U s = f (valR x U s) := by
  have hU' : ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U := fun q _ => hU (Set.mem_univ _)
  unfold valR
  rw [dif_pos hU, dif_pos hU']
  have e : (spMap f ≫ x).appLE U ⊤ hU' = x.appLE U ⊤ hU ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e]
  exact congrArg (fun φ => φ.hom ((x.appLE U ⊤ hU).hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s t : Γ(X, U)) : valR x U (s * t) = valR x U s * valR x U t := by
  unfold valR
  simp only [dif_pos hU, map_mul]

theorem valR_pow' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) (n : ℕ) : valR x U (s ^ n) = valR x U s ^ n := by
  unfold valR
  simp only [dif_pos hU, map_pow]

theorem valR_gen {A : Type} [CommRing A] {X : Scheme.{0}} (L : LB X) (e : Sp A ⟶ X) (r : (L.pull e).Gen)
    (hr : r.IsGen) (j i : L.ι) (hj : ⊤ ≤ e ⁻¹ᵁ L.U j) (hi : ⊤ ≤ e ⁻¹ᵁ L.U i) :
    valR (𝟙 _) _ (r.s fun _ => j).val = valR e _ (L.g j i).val * valR (𝟙 _) _ (r.s fun _ => i).val := by
  have hB : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ ((L.pull e).U (fun _ => j) ⊓ (L.pull e).U (fun _ => i)) :=
    fun q hq => ⟨Set.mem_iInter.2 fun _ => hj hq, Set.mem_iInter.2 fun _ => hi hq⟩
  have h := congrArg (fun v => valR (𝟙 (Sp A)) _ (Units.val v)) (hr (fun _ => j) (fun _ => i))
  replace h := h.trans (valR_mul' _ hB _ _)
  refine (valR_map _ _ hB _).symm.trans (h.trans (congrArg₂ (· * ·) ?_ (valR_map _ _ hB _)))
  show valR _ _ (Units.val (∏ _k : PUnit, (res _ (pullU e _ (L.g j i))) ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique, zpow_one]
  refine (valR_map _ _ hB _).trans ((valR_app (𝟙 _) e (U := L.U j ⊓ L.U i) (fun q hq => ⟨hj hq, hi hq⟩) _).trans ?_)
  rw [Category.id_comp]



end GlobalTheory.MBLow.BaseChRig
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TangentFirstOrder

theorem fst_eq_of_tangent : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := by
  intro K C _ _ _ P ρ k t i₀ hi v w hv hw yv yw hv1 hv2 hw1 hw2 a b a' b' ev ew
  have key : ∀ {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens) (s : Γ(X, U)),
      (valR y U s).fst = valR (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ y) U s := by
    intro X y U s
    by_cases h : ⊤ ≤ y ⁻¹ᵁ U
    · exact (GlobalTheory.MBLow.BaseChRig.valR_spMap (TrivSqZeroExt.fstHom C C C).toRingHom y h s).symm
    · have h' : ¬ ⊤ ≤ (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ y) ⁻¹ᵁ U :=
        fun h' => h ((GlobalTheory.ArcLie.le_iff_fst y U).2 h')
      unfold valR
      rw [dif_neg h, dif_neg h']
      rfl
  have sq : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap (dualMap (algebraMap K C)) =
      spMap (algebraMap K C) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    simp [dualMap]
  have e0 : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yv = spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yw := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, hv1, Category.assoc, hw1]
    · rw [Category.assoc, hv2, Category.assoc, hw2, ← Category.assoc, ← Category.assoc, sq, Category.assoc,
        Category.assoc, hv, hw]
  have hU : ⊤ ≤ (spMap (algebraMap K C)) ⁻¹ᵁ (P.L.pull (eSec P.A)).U (fun _ => i₀) :=
    fun q hq => Set.mem_iInter.2 fun _ => hi hq
  have hr : valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ≠ 0 := by
    unfold valR
    rw [dif_pos hU]
    exact (((ρ.s fun _ => i₀).isUnit.map _).map _).ne_zero
  have h1 := congrArg TrivSqZeroExt.fst ev
  have h2 := congrArg TrivSqZeroExt.fst ew
  rw [key] at h1 h2
  rw [e0, h2] at h1
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero] at h1
  exact (mul_left_cancel₀ (pow_ne_zero k hr) h1).symm

end GlobalTheory.TangentFirstOrder
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_eq_at_first_order_of_tangents : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := by
  atlas_forward_decl GlobalTheory.TangentFirstOrder.fst_eq_of_tangent
end
