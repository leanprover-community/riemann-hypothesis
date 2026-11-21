import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerZeroTangentTrivial

section
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InteriorKS

theorem subsingleton_sp_dualNumber (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem rigidity_dualNumber {K : Type} [Field K] (A₀ : Over (Sp K)) (A' G' : Over (Sp (DualNumber K))) [GrpObj A']
    [GrpObj G'] (j : A₀.left ⟶ A'.left) (a b : A' ⟶ G') (hA : IsAbelianScheme A')
    (hj : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI := subsingleton_sp_dualNumber K
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (hL.globalFns _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [Field K] {x₀ : Sp K ⟶ Xo.X} {x' : Sp (DualNumber K) ⟶ Xo.X}
  {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {π : A.left ⟶ Xo.univ.t.G.left}
  {π' : A'.left ⟶ Xo.univ.t.G.left} {i : A.left ⟶ A'.left} {q : A'.left ⟶ A.left}

theorem act_const (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg : g ≫ π' = m.cm.F) (hgw : g ≫ A'.hom = o.t.G.hom) (a : 𝓞 E) :
    (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  haveI := Xo.univ.t.act.hom a
  have wβ : (π ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A.hom ≫ x₀ := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ.1.w]
  let β : A ⟶ A := Over.homMk (hπ.1.lift _ A.hom wβ) (hπ.1.lift_snd _ _ _)
  have hβ : β.left ≫ π = π ≫ (Xo.univ.t.act.act a).left := hπ.1.lift_fst _ _ _
  haveI : IsMonHom β := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ hπ (Xo.univ.t.act.act a) β hβ
  have wα : (π' ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A'.hom ≫ x' := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ'.1.w]
  let α : A' ⟶ A' := Over.homMk (hπ'.1.lift _ A'.hom wα) (hπ'.1.lift_snd _ _ _)
  have hα : α.left ≫ π' = π' ≫ (Xo.univ.t.act.act a).left := hπ'.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ' hπ' (Xo.univ.t.act.act a) α hα
  have wδ : (q ≫ β.left) ≫ A.hom = A'.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w β, hq.1.w]
  let δ : A' ⟶ A' := Over.homMk (hq.1.lift _ A'.hom wδ) (hq.1.lift_snd _ _ _)
  have hδ : δ.left ≫ q = q ≫ β.left := hq.1.lift_fst _ _ _
  haveI : IsMonHom δ := GlobalTheory.UU.isMonHom_of_over_isMonHom hq hq β δ hδ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ'
  have e1 : i ≫ α.left = β.left ≫ i := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, reassoc_of% hiπ, hiπ, hβ]
    · simp only [Category.assoc]
      rw [Over.w α, hi.1.w, reassoc_of% (Over.w β)]
  have e2 : i ≫ δ.left = β.left ≫ i := by
    apply hq.1.hom_ext
    · simp only [Category.assoc]
      rw [hδ, reassoc_of% hiq, hiq, Category.comp_id]
    · simp only [Category.assoc]
      rw [Over.w δ, hi.1.w, reassoc_of% (Over.w β)]
  have hαδ : α = δ := rigidity_dualNumber A A' A' i α δ hA' hi.1 (e1.trans e2.symm)
    (by rw [IsMonHom.one_hom, IsMonHom.one_hom])
  have hga : (o.t.act.act a).left ≫ g = g ≫ α.left := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, hg, reassoc_of% hg]
      exact m.act a
    · simp only [Category.assoc]
      rw [hgw, Over.w α, hgw, Over.w (o.t.act.act a)]
  calc (o.t.act.act a).left ≫ (g ≫ q ≫ π) = g ≫ α.left ≫ q ≫ π := by rw [reassoc_of% hga]
    _ = g ≫ q ≫ π ≫ (Xo.univ.t.act.act a).left := by rw [hαδ, reassoc_of% hδ, hβ]
    _ = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by simp only [Category.assoc]

theorem cub_const (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg1 : g ≫ π' = m.cm.F) (hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π)) :
    (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    GlobalTheory.TangentConstLB.lbIso_tangent_const E H Dw l Xo c K x₀ x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)

theorem objMap_const (c : Coeff l) [Algebra c.F K] (hx : GlobalTheory.DeRham.epsRed K ≫ x' = x₀)
    (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') : Nonempty (ObjMap o Xo.univ (constPt x')) := by
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ x₀ = constPt x' := by
    rw [← hx]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]
  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.TorsConst.torsion_eq_const K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := act_const hi hπ hπ' hiπ hiq hq o m g hg hgw
    lin := cub_const c hi hπ hπ' hiπ hiq hq o m g hg hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩

theorem eq_constPt (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q) : x' = constPt x' := by
  obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  exact Xo.unram K x' o ⟨m⟩ (objMap_const c rfl hi (hi.comp hπ') hπ' rfl hiq hq o m)

end GlobalTheory.InteriorKS
end

section
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.KS GlobalTheory.KS.GlueDer GlobalTheory.LogKS

namespace GlobalTheory.InteriorKS

theorem glue_along {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (D : R → K) {I : Type} (W : I → X.Opens) (hW : ∀ y, ∃ i, m y ∈ W i)
    (e : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)) (he : ∀ i, LocDerK q p m D (W i) (e i))
    (hc : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, e i O f = e j O f) :
    ∃ d₁, LocDerK q p m D ⊤ d₁ ∧ ∀ (O : X.Opens) (f : Γ(X, O)) (s : Γ(Y, m ⁻¹ᵁ O)),
      (∀ i, resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = e i (O ⊓ W i) (resG X inf_le_left f)) → d₁ O f = s := by
  have cov : ∀ O : X.Opens, m ⁻¹ᵁ O ≤ ⨆ i, m ⁻¹ᵁ (O ⊓ W i) := by
    intro O y hy
    obtain ⟨i, hi⟩ := hW y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hy, hi⟩
  have ex : ∀ (O : X.Opens) (f : Γ(X, O)), ∃ s : Γ(Y, m ⁻¹ᵁ O), ∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = e i (O ⊓ W i) (resG X inf_le_left f) := by
    intro O f
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (cov O)
      (fun i => e i (O ⊓ W i) (resG X inf_le_left f)) (by
        intro i j
        have hi := (he i).res (O ⊓ W i) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_left inf_le_right (resG X inf_le_left f)
        have hj := (he j).res (O ⊓ W j) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_right inf_le_right (resG X inf_le_left f)
        rw [rsT_eq (pre_mono m inf_le_left), res_res] at hi
        rw [rsT_eq (pre_mono m inf_le_right), res_res] at hj
        have := hc i j ((O ⊓ W i) ⊓ (O ⊓ W j)) (inf_le_inf inf_le_right inf_le_right)
          (resG X (inf_le_left.trans inf_le_left) f)
        exact hi.symm.trans (this.trans hj))
    exact ⟨s, hs⟩
  have ext : ∀ (O : X.Opens) (s t : Γ(Y, m ⁻¹ᵁ O)), (∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) t) →
      s = t := fun O s t h =>
    Y.sheaf.eq_of_locally_eq' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (cov O) s t h
  choose d₁ hd using ex
  refine ⟨d₁, ⟨?_, ?_, ?_, ?_⟩, fun O f s hs => ext O _ _ fun i => (hd O f i).trans (hs i).symm⟩
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add, hd, hd, hd, map_add, (he i).add _ inf_le_right]
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add, map_mul, map_mul, hd, hd, hd, map_mul, (he i).mul _ inf_le_right,
      res_app m inf_le_left, res_app m inf_le_left]
  · intro O O' h _ f
    refine ext O' _ _ fun i => ?_
    have h' : O' ⊓ W i ≤ O ⊓ W i := inf_le_inf_right _ h
    have h1 := (he i).res (O ⊓ W i) (O' ⊓ W i) h' inf_le_right (resG X inf_le_left f)
    rw [rsT_eq (pre_mono m h'), res_res, ← hd, res_res] at h1
    rw [hd, rsT_eq (pre_mono m h), res_res, res_res, h1]
  · intro O _ r
    refine ext O _ _ fun i => ?_
    rw [hd, res_const, res_const, (he i).base _ inf_le_right]

theorem chart_appLE {X : Scheme.{0}} (U : X.affineOpens) (h : ⊤ ≤ chart U ⁻¹ᵁ U.1) :
    (chart U).appLE U.1 ⊤ h = (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
  have hU : IsAffineOpen U.1 := U.2
  show hU.fromSpec.app U.1 ≫ (Spec Γ(X, U.1)).presheaf.map (homOfLE h).op = _
  rw [hU.fromSpec_app_self, Category.assoc]
  erw [← Functor.map_comp]
  exact (congrArg (_ ≫ ·) ((Spec Γ(X, U.1)).presheaf.map_id _)).trans (Category.comp_id _)

theorem top_le_chart {X : Scheme.{0}} (U : X.affineOpens) : ⊤ ≤ chart U ⁻¹ᵁ U.1 :=
  U.2.fromSpec_preimage_self.ge

theorem appLE_eq_constFn {X Y : Scheme.{0}} (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (q : Y ⟶ Sp S) (a : Y ⟶ X) (ha : a = q ≫ spMap φ ≫ chart U) (W : Y.Opens) (h : W ≤ a ⁻¹ᵁ U.1) (r : Γ(X, U.1)) :
    (a.appLE U.1 W h).hom r = constFn q W (φ r) := by
  subst ha
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (φ r) =
      ((spMap φ).appTop).hom ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom r) :=
    congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have e : (q ≫ spMap φ ≫ chart U).appLE U.1 W h =
      (chart U).appLE U.1 ⊤ (top_le_chart U) ≫ (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) ≫
        q.appLE ⊤ W (fun _ _ => trivial) := by
    erw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [Category.assoc]
  rw [e, chart_appLE, constFn, h2, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem ext_affineOpen {X Y : Scheme.{0}} (U : X.affineOpens) (a b : Y ⟶ X) (ha : ⊤ ≤ a ⁻¹ᵁ U.1) (hb : ⊤ ≤ b ⁻¹ᵁ U.1)
    (h : a.appLE U.1 ⊤ ha = b.appLE U.1 ⊤ hb) : a = b := by
  have key : ∀ (a : Y ⟶ X) (ha : ⊤ ≤ a ⁻¹ᵁ U.1),
      a = Y.toSpecΓ ≫ Spec.map (a.appLE U.1 ⊤ ha) ≫ U.2.fromSpec := by
    intro a ha
    have := IsAffineOpen.isOpenImmersion_fromSpec (show IsAffineOpen U.1 from U.2)
    have hr : Set.range a ⊆ Set.range U.2.fromSpec := by
      rw [U.2.range_fromSpec]
      rintro _ ⟨y, rfl⟩
      exact ha (Set.mem_univ y)
    obtain ⟨a', rfl⟩ : ∃ a', a' ≫ U.2.fromSpec = a := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have e : (a' ≫ U.2.fromSpec).appLE U.1 ⊤ ha = (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ a'.appTop := by
      rw [← chart_appLE U (top_le_chart U), Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Spec.map_comp, ← Category.assoc, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc a',
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key a ha, key b hb, h]

theorem app_eq_zero_of_valR {Y Z : Scheme.{0}} (m : Y ⟶ Z) (O : Z.Opens) (f : Γ(Z, O))
    (h : ∀ Ω : Y.affineOpens, Ω.1 ≤ m ⁻¹ᵁ O → valR (chart Ω ≫ m) O f = 0) : (m.app O).hom f = 0 := by
  refine Y.sheaf.eq_of_locally_eq' (fun Ω : {Ω : Y.affineOpens // Ω.1 ≤ m ⁻¹ᵁ O} => Ω.1.1) (m ⁻¹ᵁ O)
    (fun Ω => homOfLE Ω.2) (fun y hy => ?_) _ _ fun Ω => ?_
  · obtain ⟨Ω, hΩ, hy', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨Ω, hΩ⟩, hle⟩, hy'⟩
  · have h0 : ⊤ ≤ (chart Ω.1 ≫ m) ⁻¹ᵁ O := fun p hp => Ω.2 (top_le_chart Ω.1 hp)
    have h1 := h Ω.1 Ω.2
    rw [valR, dif_pos h0, ← Scheme.Hom.appLE_comp_appLE (chart Ω.1) m O Ω.1.1 ⊤ Ω.2 (top_le_chart _), chart_appLE] at h1
    have h2 : (m.appLE O Ω.1.1 Ω.2).hom f = 0 := by
      refine Eq.trans ?_ h1
      exact (congrArg (fun ψ => ψ.hom ((m.appLE O Ω.1.1 Ω.2).hom f)) (Scheme.ΓSpecIso Γ(Y, Ω.1.1)).inv_hom_id).symm
    exact h2.trans (map_zero _).symm

theorem isField_intCast {Z : Scheme.{0}} {W O : Z.Opens} {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)} (hd : IsField W d)
    (hO : O ≤ W) (r : ℤ) : d O (r : Γ(Z, O)) = 0 := by
  let δ : Γ(Z, O) →+ Γ(Z, O) := AddMonoidHom.mk' (d O) (hd.1 O hO)
  have h1 : d O 1 = 0 := by
    have := hd.2.1 O hO 1 1
    rw [mul_one, one_mul] at this
    exact left_eq_add.1 this
  have : δ (r : Γ(Z, O)) = 0 := by
    rw [← zsmul_one, map_zsmul]
    exact (congrArg (r • ·) h1).trans (smul_zero r)
  exact this

theorem constFn_int {Z : Scheme.{0}} (p : Z ⟶ Sp ℤ) (O : Z.Opens) (r : ℤ) : constFn p O r = (r : Γ(Z, O)) :=
  eq_intCast ((p.appLE ⊤ O (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom) r

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (V : X.Opens)
  (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1))
  (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1))

theorem exists_global_lift (hv : ∀ a, IsTanAtG t (chart U) (v a)) (hKS : IsKS t V U v D Θ) {K : Type} [Field K]
    (φ₀ : Γ(X, U.1) →+* K) (hΘ : ∀ a b, φ₀ (Θ a b) = 0) (hV : ⊤ ≤ (spMap φ₀ ≫ chart U) ⁻¹ᵁ V) {Y : Scheme.{0}}
    (q : Y ⟶ Sp K) (m : Y ⟶ t.G.left) (hm : m ≫ t.G.hom = q ≫ spMap φ₀ ≫ chart U) (p : t.G.left ⟶ Sp ℤ) :
    ∃ d₁, LocDerK q p m (fun _ => 0) ⊤ d₁ ∧
      ∀ r, d₁ (t.G.hom ⁻¹ᵁ U.1) ((t.G.hom.app U.1).hom r) = constFn q _ (φ₀ (D r)) := by
  obtain ⟨J, W, j, d, hcov, -, hfield, hlift, hdiff⟩ := hKS
  have hW₀ : ∀ k, W k ≤ t.G.hom ⁻¹ᵁ U.1 := fun k p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov ▸ (le_iSup W k) hp
    exact this.1
  refine Exists.imp (fun d₁ h => ⟨h.1, fun r => h.2 _ _ _ fun i => ?_⟩)
    (glue_along q p m (fun _ => 0) W ?_ (fun i O f => (m.app O).hom (d i O f)) ?_ ?_)
  rotate_right
  · beta_reduce
    have e1 : resG t.G.left (inf_le_left : t.G.hom ⁻¹ᵁ U.1 ⊓ W i ≤ _) ((t.G.hom.app U.1).hom r) =
        resG t.G.left (inf_le_right : t.G.hom ⁻¹ᵁ U.1 ⊓ W i ≤ _) ((t.G.hom.appLE U.1 (W i) (hW₀ i)).hom r) :=
      (congrArg (fun ψ => ψ.hom r) (Scheme.Hom.appLE_map t.G.hom (hW₀ i)
        (homOfLE (inf_le_right : t.G.hom ⁻¹ᵁ U.1 ⊓ W i ≤ _)).op)).symm
    rw [res_const, e1, (hfield i).2.2 _ _ _ le_rfl, hlift i (hW₀ i), ← res_app m _ (pre_mono m inf_le_right),
      ← res_const q (pre_mono m (inf_le_right : t.G.hom ⁻¹ᵁ U.1 ⊓ W i ≤ _))]
    congr 1
    rw [← appLE_eq_constFn U φ₀ q _ hm _ (pre_mono m (hW₀ i)), Scheme.Hom.app_eq_appLE]
    exact (congrArg (fun ψ => ψ.hom (D r)) (Scheme.Hom.appLE_comp_appLE m t.G.hom U.1 (W i) _ (hW₀ i) le_rfl)).symm
  · intro y
    have h1 : (m ≫ t.G.hom) y ∈ U.1 ⊓ V := by
      rw [hm]
      exact ⟨top_le_chart U (Set.mem_univ ((q ≫ spMap φ₀) y)), hV (Set.mem_univ (q y))⟩
    have h2 : m y ∈ ⨆ k, W k := by
      rw [hcov]
      exact h1
    exact TopologicalSpace.Opens.mem_iSup.1 h2
  · intro i
    refine ⟨fun O hO f f' => ?_, fun O hO f f' => ?_, fun O O' h hO f => ?_, fun O hO r => ?_⟩
    · rw [(hfield i).1 O hO, map_add]
    · rw [(hfield i).2.1 O hO, map_add, map_mul, map_mul]
    · rw [(hfield i).2.2 O O' h hO, rsT_eq (pre_mono m h), res_app m h]
    · rw [constFn_int, isField_intCast (hfield i) hO, map_zero, constFn, map_zero, map_zero]
  · intro i i' O hO f
    rw [← sub_eq_zero, ← map_sub]
    refine app_eq_zero_of_valR m O _ fun Ω hΩ => ?_
    obtain ⟨ψ, hψ⟩ : ∃ ψ : K →+* Γ(Y, Ω.1), spMap ψ = chart Ω ≫ q :=
      ⟨(Spec.preimage (chart Ω ≫ q)).hom, Spec.map_preimage _⟩
    have hg : (chart Ω ≫ m) ≫ t.G.hom = spMap (ψ.comp φ₀) ≫ chart U := by
      rw [Category.assoc, hm, ← Category.assoc, ← hψ, ← Category.assoc, spMap_comp']
    choose w hw using fun a => (existsUnique_isTranslate t (ψ.comp φ₀) hg (hv a)).exists
    rw [hdiff i i' O hO f _ (ψ.comp φ₀) (chart Ω ≫ m) w hg (fun p hp => hΩ (top_le_chart Ω hp)) hw]
    simp [hΘ]

theorem exists_isConstK (hv : ∀ a, IsTanAtG t (chart U) (v a)) (hKS : IsKS t V U v D Θ) {K : Type} [Field K]
    (φ : Γ(X, U.1) →+* DualNumber K) (hφ : ∀ r, (φ r).snd = (φ (D r)).fst) (hΘ : ∀ a b, (φ (Θ a b)).fst = 0)
    (hV : ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ V) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (ι' : A'.left ⟶ t.G.left) (i : A.left ⟶ A'.left) (hA' : IsAbelianScheme A')
    (hι' : IsGrpPullback A' t.G (spMap φ ≫ chart U) ι')
    (hi : IsGrpPullback A A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) i) : ∃ ρ, IsConstK A' A ρ i := by
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hA' hi
  let φ₀ : Γ(X, U.1) →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom.comp φ
  have hφ₀ : spMap φ₀ = spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap φ := (spMap_comp' _ _).symm
  have hm : (i ≫ ι') ≫ t.G.hom = A.hom ≫ spMap φ₀ ≫ chart U := by
    rw [Category.assoc, hι'.1.w, ← Category.assoc, hi.1.w, hφ₀]
    simp only [Category.assoc]
  let p : t.G.left ⟶ Sp ℤ := specZIsTerminal.from _
  obtain ⟨d, hd, hdD⟩ := exists_global_lift t V U v D Θ hv hKS φ₀ hΘ (by
    rw [hφ₀, Category.assoc]
    exact fun z _ => hV (Set.mem_univ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom z))) A.hom (i ≫ ι') hm p
  have hfs : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  obtain ⟨C, ρ, π, P⟩ : ∃ (C : Scheme.{0}) (ρ : C ⟶ A.left) (π : C ⟶ Sp (DualNumber K)),
      IsPullback ρ π A.hom (spMap (algebraMap K (DualNumber K))) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  let j₀ : A.left ⟶ C :=
    P.lift (𝟙 _) (A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
      (by rw [Category.assoc, hfs, Category.id_comp, Category.comp_id])
  have e1 : j₀ ≫ ρ = 𝟙 _ := P.lift_fst _ _ _
  have e2 : j₀ ≫ π = A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := P.lift_snd _ _ _
  obtain ⟨hO, Pj, -⟩ := GlobalTheory.ConstThickening.structure_dualNumber K _ _ A.hom π ρ j₀ P e1 e2
  obtain ⟨Φ, hΦ1, -, hΦ3⟩ := GlobalTheory.KS.DerMorK.exists_hom_of_derivation K _ _ A.hom π ρ j₀ P e1 e2 ℤ
    (Int.castRingHom (DualNumber K)) t.G.left p (i ≫ ι') d (specZIsTerminal.hom_ext _ _) (by
      have : (fun r : ℤ => (Int.castRingHom (DualNumber K) r).snd) = fun _ => 0 := by
        funext r; simp
      rw [this]; exact hd)
  have hmU : ⊤ ≤ (i ≫ ι') ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    show ⊤ ≤ ((i ≫ ι') ≫ t.G.hom) ⁻¹ᵁ U.1
    rw [hm]
    exact fun z _ => top_le_chart U (Set.mem_univ ((A.hom ≫ spMap φ₀) z))
  have hT : ⊤ ≤ ρ ⁻¹ᵁ ((i ≫ ι') ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1)) := fun z _ => hmU (Set.mem_univ (ρ z))
  have hΦU : ρ ⁻¹ᵁ ((i ≫ ι') ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1)) ≤ Φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    rw [← hΦ1]
    exact (hO (Φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1))).le
  have hΦ2 : Φ ≫ t.G.hom = π ≫ spMap φ ≫ chart U := by
    have hb : ⊤ ≤ (π ≫ spMap φ ≫ chart U) ⁻¹ᵁ U.1 :=
      fun z _ => top_le_chart U (Set.mem_univ ((π ≫ spMap φ) z))
    refine ext_affineOpen U _ _ (hT.trans hΦU) hb ?_
    ext r
    have h3 := hΦ3 _ ((t.G.hom.app U.1).hom r)
    rw [hdD, pbT, dif_pos hΦU, pbT, dif_pos (by exact le_rfl), pbT, dif_pos le_rfl, ← Scheme.Hom.app_eq_appLE ρ,
      app_const _ A.hom π ρ P.w] at h3
    have h4 := congrArg (resG C hT) h3
    rw [map_add, map_mul, res_const, res_const] at h4
    have a1 : ((Φ ≫ t.G.hom).appLE U.1 ⊤ (hT.trans hΦU)).hom r =
        resG C hT ((Φ.appLE _ _ hΦU).hom ((t.G.hom.app U.1).hom r)) := by
      rw [Scheme.Hom.comp_appLE]
      exact (congrArg (fun ψ => ψ.hom ((t.G.hom.app U.1).hom r)) (Scheme.Hom.appLE_map Φ hΦU (homOfLE hT).op)).symm
    have a2 : resG C hT (((ρ ≫ i ≫ ι').appLE (t.G.hom ⁻¹ᵁ U.1) _ le_rfl).hom ((t.G.hom.app U.1).hom r)) =
        constFn π ⊤ (algebraMap K (DualNumber K) (φ₀ r)) := by
      rw [← RingHom.comp_apply (algebraMap K _), ← appLE_eq_constFn U _ π ((ρ ≫ i ≫ ι') ≫ t.G.hom) (by
        rw [Category.assoc, hm, ← Category.assoc, P.w, ← spMap_comp' φ₀ (algebraMap K (DualNumber K))]
        simp only [Category.assoc]) ⊤ hT, Scheme.Hom.comp_appLE]
      exact congrArg (fun ψ => ψ.hom ((t.G.hom.app U.1).hom r))
        (Scheme.Hom.appLE_map (ρ ≫ i ≫ ι') le_rfl (homOfLE hT).op)
    refine (a1.trans (h4.trans ?_)).trans (appLE_eq_constFn U φ π _ rfl ⊤ hb r).symm
    refine (congrArg (· + _) a2).trans ?_
    unfold constFn
    rw [← map_mul, ← map_add, ← map_mul, ← map_add]
    congr 2
    ext
    · simp [φ₀, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [φ₀, hφ, TrivSqZeroExt.algebraMap_eq_inl]
  let e := hι'.1.lift Φ π hΦ2
  have f1 : e ≫ ι' = Φ := hι'.1.lift_fst _ _ _
  have f2 : e ≫ A'.hom = π := hι'.1.lift_snd _ _ _
  have f3 : j₀ ≫ e = i := hι'.1.hom_ext (by rw [Category.assoc, f1, hΦ1])
    (by rw [Category.assoc, f2, e2, hi.1.w])
  have hflat₀ : Flat A.hom := inferInstance
  have hflat : Flat π := MorphismProperty.of_isPullback (P := @Flat) P hflat₀
  have : IsIso e := GlobalTheory.isIso_of_id_mod_eps K _ _ _ A.hom _ A'.hom j₀ i e Pj hi.1 hflat f2 f3
  refine exists_isConstK_of_isPullback GlobalTheory.abelianSchemeLaws_all.1 K A A' (inv e ≫ ρ) i hA hA' hi ?_ ?_
  · refine IsPullback.of_iso P (asIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simpa using f2.symm
    · simp
    · simp
  · rw [← f3, Category.assoc, IsIso.hom_inv_id_assoc, e1]

end GlobalTheory.InteriorKS
end
