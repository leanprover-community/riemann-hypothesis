import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPoint
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaGeneratorEqRootOfUnityMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemSmulTopOfNeatLevel

section
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevMoveFibre

theorem alg {R : Type} [CommRing R] {La : Type} [AddCommGroup La] [Module R La] {Q : Type} [Group Q]
    (Mb Mc : Ideal R) (M : ℕ) (hcop : Mb ⊔ Mc = ⊤) (hMb : (M : R) ∈ Mb) (hMc : (M : R) ∈ Mc)
    (act : R → Q → Q) (ev evM : La → Q) (hadd : ∀ a b, ev (a + b) = ev a * ev b)
    (hker : ∀ a ∈ Mb • (⊤ : Submodule R La), ev a = 1) (hag : ∀ a ∈ Mc • (⊤ : Submodule R La), ev a = evM a)
    (Ilin : ∀ (c : R) a, evM (c • a) = act c (evM a)) (Iker : ∀ a, evM a = 1 ↔ ∃ b, a = M • b)
    (Ionto : ∀ q : Q, q ^ M = 1 ↔ ∃ a, evM a = q) (hpow : ∀ q, act (M : R) q = q ^ M) :
    (∀ c a, ev (c • a) = act c (ev a)) ∧ (∀ a, ev a = 1 ↔ a ∈ Mb • (⊤ : Submodule R La)) ∧
      (∀ q, (∀ c ∈ Mb, act c q = 1) → ∃ a, ev a = q) := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : R) ∈ Mb ⊔ Mc)
  have hsplit : ∀ a : La, a = u • a + v • a := fun a => by rw [← add_smul, huv, one_smul]
  have hdec : ∀ a, ev a = evM (v • a) := fun a => by
    conv_lhs => rw [hsplit a]
    rw [hadd, hker _ (Submodule.smul_mem_smul hu trivial), _root_.one_mul,
      hag _ (Submodule.smul_mem_smul hv trivial)]
  have hMs : ∀ (I : Ideal R), (M : R) ∈ I → ∀ b : La, M • b ∈ I • (⊤ : Submodule R La) := fun I hI b => by
    rw [← Nat.cast_smul_eq_nsmul R]; exact Submodule.smul_mem_smul hI trivial
  refine ⟨fun c a => ?_, fun a => ⟨fun h => ?_, hker a⟩, fun q hq => ?_⟩
  · rw [hdec, hdec, smul_comm, Ilin]
  · rw [hdec, Iker] at h
    obtain ⟨b, hb⟩ := h
    rw [hsplit a, hb]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hu trivial) (hMs Mb hMb b)
  · obtain ⟨b, hb⟩ := (Ionto q).1 (by rw [← hpow]; exact hq _ hMb)
    have hub : evM (u • b) = 1 := by rw [Ilin, hb]; exact hq u hu
    obtain ⟨b', hb'⟩ := (Iker _).1 hub
    have hmem : b ∈ Mc • (⊤ : Submodule R La) := by
      rw [hsplit b, hb']
      exact Submodule.add_mem _ (hMs Mc hMc b') (Submodule.smul_mem_smul hv trivial)
    exact ⟨b, (hag b hmem).trans hb⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f f' : S' ⟶ S} (h : f = f')
    (n : SABMap t' t f) : ∃ n' : SABMap t' t f', n'.φ = n.φ := by
  subst h; exact ⟨n, rfl⟩

theorem iterate_eq {C : Type*} [Category C] {X : C} (θ : Aut X) (N : ℕ) :
    (fun f : X ⟶ X => f ≫ θ.hom)^[N] (𝟙 X) = (θ ^ N).hom := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    rfl

theorem act_natCast {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (α : OAct (𝓞 E) G)
    (q : T ⟶ G) (n : ℕ) : q ≫ α.act (n : 𝓞 E) = q ^ n := by
  have h0 : α.act 0 = 1 := by
    have : α.act 0 * α.act 0 = α.act 0 * 1 := by rw [_root_.mul_one, ← α.add, add_zero]
    exact mul_left_cancel this
  induction n with
  | zero => rw [Nat.cast_zero, h0, comp_one, pow_zero]
  | succ n ih => rw [Nat.cast_succ, α.add, comp_mul, ih, α.one, Category.comp_id, pow_succ]

theorem sec_move {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hc : IsGrpPullback G' G f φ) (e e' : 𝟙_ (Over S') ⟶ G') (ψ : G' ⟶ G')
    (ν : G.left ⟶ G.left) (ρ : S ⟶ S) (hψ : ψ.left ≫ φ = φ ≫ ν) (a b : 𝟙_ (Over S) ⟶ G)
    (he : e.left ≫ φ = f ≫ a.left) (he' : e'.left ≫ φ = f ≫ b.left) (hab : a.left ≫ ν = ρ ≫ b.left)
    (hf : f ≫ ρ = f) : e ≫ ψ = e' := by
  apply Over.OverMorphism.ext
  apply hc.1.hom_ext
  · rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc, he, Category.assoc, hab, ← Category.assoc, hf, he']
  · exact (Over.w _).trans (Over.w _).symm

end GlobalTheory.LevMoveFibre

open GlobalTheory.LevMoveFibre in

theorem GlobalTheory.LevMoveFibre.exists_fibreAut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (x : Sp ℂ ⟶ Xo.X) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La), Formalism.L2.Pj.IsLevMove ρ ν gM gA → x ≫ ρ = x → ∃ (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N : ℕ) (ev : Dw.La → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), IsMonHom θ ∧ 0 < N ∧ (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A ∧ (∀ a, act.act a ≫ θ = θ ≫ act.act a) ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act.act c) ∧ (∀ a, ev a = 1 ↔ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, (∀ c ∈ l.Mb, q ≫ act.act c = 1) → ∃ a, ev a = q) ∧ ∀ a, ev (gM a) ≫ θ = ev a := by
  intro E _ _ _ H Dw l Xo x ρ ν gM gA hlev hx
  obtain ⟨t', ⟨m⟩⟩ := exists_sab x Xo.univ.t
  obtain ⟨T, hT, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ (GlobalTheory.ModelCompare.objOfSABMap Xo.univ m)
  obtain rfl : T.t = t' := hT
  obtain ⟨n₀, hn₀⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Xo.univ.t T.t ρ x ν m
  obtain ⟨n, hn⟩ := exists_cast hx n₀
  obtain ⟨ψ, hψ, hφ, hact, -⟩ := sabMap_iso n m rfl rfl
  let θ : Aut T.t.G := ψ
  have hL := GlobalTheory.lawsFieldsSeparately
  obtain ⟨N, hN, hθN⟩ := GlobalTheory.AutFin.exists_pow_eq_one hL.2.2.2.2.2.1 hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    Xo.univ.proper Xo.univ.ample Xo.univ.ktriv m n θ hφ
  let o := GlobalTheory.ModelCompare.objOfSABMap Xo.univ m
  have hev : ∀ a, (o.eta a).left ≫ m.φ = x ≫ (Xo.univ.eta a).left := fun a =>
    (GlobalTheory.ModelCompare.objMapOfSABMap Xo.univ m).eta a
  obtain ⟨β, hβ⟩ : ∃ β : KA l →+* ℂ, x ≫ Xo.s = spMap β := ⟨(Spec.preimage (x ≫ Xo.s)).hom, by simp [spMap]⟩
  obtain ⟨-, I, -, -, hM⟩ := o.geom ℂ (𝟙 _) β (by rw [Category.id_comp]; exact hβ)
  have hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), o.eta a = I.ev l.M a := by
    intro a ha
    have := hM a ha
    rw [show toUnit (Over.mk (𝟙 (Sp ℂ))) = 𝟙 (𝟙_ (Over (Sp ℂ))) from toUnit_unique _ _] at this
    exact (Category.id_comp _).symm.trans this
  have hMM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have i1 : ∀ (c : 𝓞 E) (a : Dw.La), I.ev l.M (c • a) = I.ev l.M a ≫ T.t.act.act c := I.lin l.M
  have i2 : ∀ a, I.ev l.M a = 1 ↔ ∃ b, a = l.M • b := I.ker l.M hM0
  have i3 : ∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G, q ^ l.M = 1 ↔ ∃ a, I.ev l.M a = q := I.onto l.M hM0
  have e1 : ∀ a b, o.eta (a + b) = o.eta a * o.eta b := o.eta_add
  have e2 : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La), o.eta a = 1 := o.eta_ker
  have e3 : ∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G, q ≫ T.t.act.act ((l.M : ℕ) : 𝓞 E) = q ^ l.M := fun q => act_natCast _ q _
  let evM : Dw.La → (𝟙_ (Over (Sp ℂ)) ⟶ T.t.G) := I.ev l.M
  have hM'' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), o.eta a = evM a := hM'
  have i1' : ∀ (c : 𝓞 E) (a : Dw.La), evM (c • a) = (fun c g => g ≫ T.t.act.act c) c (evM a) := i1
  have i2' : ∀ a, evM a = 1 ↔ ∃ b, a = l.M • b := i2
  have i3' : ∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G, q ^ l.M = 1 ↔ ∃ a, evM a = q := i3
  have hMb : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) hMM
  have hMc : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := (Ideal.mul_le_right : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) hMM
  obtain ⟨hlin, hker, honto⟩ := alg (R := 𝓞 E) (La := Dw.La) (Q := 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G) l.Mb (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) l.M l.coprime hMb hMc (fun c g => g ≫ T.t.act.act c) o.eta evM e1 e2 hM'' i1' i2' i3' e3
  refine ⟨T.pol, T.t.act, ψ.hom, N, o.eta, hψ, hN, ?_, hact, e1, hlin, hker, honto, fun a => ?_⟩
  · rw [iterate_eq θ N, hθN]; rfl
  · exact sec_move m.cart (o.eta (gM a)) (o.eta a) ψ.hom ν.φ ρ (hφ.trans (hn.trans hn₀)) _ _ (hev _) (hev _)
      (hlev.2.1 a) hx
end

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteOrder_fibreAut_at_levelMove_fixedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (x : Sp ℂ ⟶ Xo.X) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La), Formalism.L2.Pj.IsLevMove ρ ν gM gA → x ≫ ρ = x → ∃ (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N : ℕ) (ev : Dw.La → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), IsMonHom θ ∧ 0 < N ∧ (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A ∧ (∀ a, act.act a ≫ θ = θ ≫ act.act a) ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act.act c) ∧ (∀ a, ev a = 1 ↔ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, (∀ c ∈ l.Mb, q ≫ act.act c = 1) → ∃ a, ev a = q) ∧ ∀ a, ev (gM a) ≫ θ = ev a := by
  atlas_forward_decl GlobalTheory.LevMoveFibre.exists_fibreAut
end

section
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodLattice

variable {P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)}

theorem one_comp_of_isMonHom (f : P.A ⟶ P.A) (hf : IsMonHom f) :
    (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) ≫ f = 1 :=
  (IsMonHom.monoidHom f (𝟙_ (Over (Sp ℂ)))).map_one

theorem comp_mul' (x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) (f g : P.A ⟶ P.A) : x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem comp_one' (x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) : x ≫ (1 : P.A ⟶ P.A) = 1 := by
  simp [Hom.one_def]

section Lift

variable (u : HolUnif P.A P.L P.g)

theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem ex_nsmul (k : ℕ) (z : Fin P.g → ℂ) : u.ex (k • z) = u.ex z ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ k ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem lift_unique (f : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (hF' : ∀ z, u.ex (F' z) = u.ex z ≫ f) : F = F' := by
  have hmem : ∀ z, (F - F') z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h := u.ex_add ((F - F') z) (F' z)
    rw [LinearMap.sub_apply, sub_add_cancel, hF, hF'] at h
    exact mul_eq_right.mp h.symm
  haveI := u.discrete
  let D : (Fin P.g → ℂ) → u.Λ := fun z => ⟨(F - F') z, hmem z⟩
  have hD : Continuous D :=
    Continuous.subtype_mk (LinearMap.continuous_of_finiteDimensional _) _
  refine LinearMap.ext fun z => ?_
  have h1 : D z = D 0 := PreconnectedSpace.constant inferInstance hD
  have h2 : (F - F') z = 0 := by
    have := congrArg Subtype.val h1
    simpa [D] using this
  exact sub_eq_zero.mp (by simpa using h2)

variable (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)

def lift (f : P.A ⟶ P.A) (hf : IsMonHom f) : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := Classical.choose (hl f hf)

theorem lift_spec (f : P.A ⟶ P.A) (hf : IsMonHom f) (z) : u.ex (lift u hl f hf z) = u.ex z ≫ f :=
  Classical.choose_spec (hl f hf) z

theorem lift_eq (f : P.A ⟶ P.A) (hf : IsMonHom f) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) : lift u hl f hf = F :=
  lift_unique u f _ _ (lift_spec u hl f hf) hF

theorem lift_mem (f : P.A ⟶ P.A) (hf : IsMonHom f) {z} (hz : z ∈ u.Λ) : lift u hl f hf z ∈ u.Λ := by
  rw [← u.ker] at hz ⊢
  rw [lift_spec, hz, one_comp_of_isMonHom f hf]

def liftZ (f : P.A ⟶ P.A) (hf : IsMonHom f) : Module.End ℤ u.Λ where
  toFun x := ⟨lift u hl f hf x, lift_mem u hl f hf x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_zsmul (lift u hl f hf) c (x : Fin P.g → ℂ))

@[simp] theorem liftZ_val (f : P.A ⟶ P.A) (hf : IsMonHom f) (x : u.Λ) :
    ((liftZ u hl f hf x : u.Λ) : Fin P.g → ℂ) = lift u hl f hf x := rfl

end Lift

section Ring

variable (u : HolUnif P.A P.L P.g)
  (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)
  {O : Type} [CommRing O] (act : OAct O P.A)

theorem act_zero : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

def ringAct : O →+* Module.End ℤ u.Λ where
  toFun c := liftZ u hl (act.act c) (act.hom c)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, Module.End.one_apply]
    rw [lift_eq u hl _ _ LinearMap.id (fun z => by rw [act.one, Category.comp_id]; rfl)]
    rfl
  map_mul' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, Module.End.mul_apply]
    rw [lift_eq u hl _ _ ((lift u hl (act.act a) (act.hom a)).comp (lift u hl (act.act b) (act.hom b)))
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc, ← act.mul, mul_comm])]
    rfl
  map_zero' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, LinearMap.zero_apply, ZeroMemClass.coe_zero]
    rw [lift_eq u hl _ _ 0 (fun z => by rw [LinearMap.zero_apply, ex_zero, act_zero, comp_one'])]
    rfl
  map_add' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [liftZ_val, LinearMap.add_apply, Submodule.coe_add]
    rw [lift_eq u hl _ _ (lift u hl (act.act a) (act.hom a) + lift u hl (act.act b) (act.hom b))
      (fun z => by rw [LinearMap.add_apply, u.ex_add, lift_spec, lift_spec, act.add, comp_mul'])]
    rfl

@[simp] theorem ringAct_val (c : O) (x : u.Λ) :
    ((ringAct u hl act c x : u.Λ) : Fin P.g → ℂ) = lift u hl (act.act c) (act.hom c) x := rfl

end Ring

section Main

variable (u : HolUnif P.A P.L P.g)
  (hl : ∀ f : P.A ⟶ P.A, IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f)

theorem lift_pow_spec (θ : P.A ⟶ P.A) (hθ : IsMonHom θ) (k : ℕ) (z : Fin P.g → ℂ) :
    u.ex ((lift u hl θ hθ ^ k) z) = u.ex z ≫ (fun f : P.A ⟶ P.A => f ≫ θ)^[k] (𝟙 P.A) := by
  induction k with
  | zero => rw [pow_zero, Module.End.one_apply, Function.iterate_zero, id, Category.comp_id]
  | succ k ih => rw [pow_succ', Module.End.mul_apply, lift_spec, ih, Function.iterate_succ_apply', Category.assoc]

include u hl in
theorem main_of_unif (E : Type) [Field E] [NumberField E] (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ)
    (hθ : IsMonHom θ) (hN : (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A)
    (hc : ∀ a, act.act a ≫ θ = θ ≫ act.act a) (hn : 0 < n) :
    ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)),
      Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
      (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧
      (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  letI inst : Module (𝓞 E) u.Λ := Module.compHom u.Λ (ringAct u hl act)
  have hsmul : ∀ (c : 𝓞 E) (x : u.Λ), ((c • x : u.Λ) : Fin P.g → ℂ) = lift u hl (act.act c) (act.hom c) x :=
    fun _ _ => rfl

  have hcomm : ∀ c, (lift u hl θ hθ).comp (lift u hl (act.act c) (act.hom c)) =
      (lift u hl (act.act c) (act.hom c)).comp (lift u hl θ hθ) := fun c =>
    lift_unique u (act.act c ≫ θ) _ _
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, lift_spec, lift_spec, Category.assoc, hc])
  let F : u.Λ →ₗ[𝓞 E] u.Λ :=
    { toFun := liftZ u hl θ hθ
      map_add' := map_add _
      map_smul' := fun c x => Subtype.ext (by
        simp only [RingHom.id_apply, hsmul, liftZ_val]
        exact (LinearMap.congr_fun (hcomm c) x : _)) }
  have hFval : ∀ x : u.Λ, ((F x : u.Λ) : Fin P.g → ℂ) = lift u hl θ hθ x := fun _ => rfl
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let ψ : u.Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) := fun a => u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ))
  have hψlift : ∀ (f : P.A ⟶ P.A) (hf : IsMonHom f) (a : u.Λ),
      u.ex ((n : ℂ)⁻¹ • lift u hl f hf a) = ψ a ≫ f := fun f hf a => by
    rw [← map_smul, lift_spec]
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI hZ : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  refine ⟨u.Λ, inferInstance, inst, F, ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) u.Λ
  · refine Module.IsTorsionFree.of_smul_eq_zero fun c x h => ?_
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    right
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    have hm : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc0
    have h1 : (Ideal.absNorm (Ideal.span {c}) : 𝓞 E) • x = 0 := by
      rw [← hr, mul_smul, h, smul_zero]
    rw [Nat.cast_smul_eq_nsmul] at h1
    have h2 := congrArg Subtype.val h1
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h2
    exact Subtype.ext ((smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hm))
  · have hpow : lift u hl θ hθ ^ N = 1 := by
      rw [lift_unique u (𝟙 P.A) (lift u hl θ hθ ^ N) 1
        (fun z => by rw [lift_pow_spec, hN]) (fun z => by rw [Module.End.one_apply, Category.comp_id])]
    have hit : ∀ (k : ℕ) (x : u.Λ), (((F ^ k) x : u.Λ) : Fin P.g → ℂ) = (lift u hl θ hθ ^ k) x := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ih => intro x; rw [pow_succ', Module.End.mul_apply, hFval, ih, pow_succ', Module.End.mul_apply]
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [hit, hpow]; rfl
  · intro a b
    simp only [ψ, Submodule.coe_add, smul_add, u.ex_add]
  · intro c a
    simp only [ψ]
    rw [hsmul, hψlift]
  · intro a
    simp only [ψ]
    rw [u.ker]
    constructor
    · intro h
      refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
      rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hn']
    · rintro ⟨b, rfl⟩
      rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hn']
      exact b.2
  · intro q hq
    obtain ⟨z, rfl⟩ := u.ex_onto q
    have hz : (n : ℂ) • z ∈ u.Λ := by
      rw [← u.ker, Nat.cast_smul_eq_nsmul, ex_nsmul, hq]
    refine ⟨⟨_, hz⟩, ?_⟩
    simp only [ψ]
    rw [inv_smul_smul₀ hn']
  · intro a
    simp only [ψ]
    rw [hFval, hψlift]

end Main

end GlobalTheory.PeriodLattice

theorem GlobalTheory.periodLattice_of_finiteOrder : ∀ (E : Type) [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ), IsMonHom θ → 0 < N → (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A → (∀ a, act.act a ≫ θ = θ ≫ act.act a) → 0 < n → ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧ (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  intro E _ _ P act θ N n hθ _ hN hc hn
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, -, -, -, -, -, -, -, hl, -⟩ := GlobalTheory.thetaUnifAV_all P rig hrig
  exact GlobalTheory.PeriodLattice.main_of_unif u hl E act θ N n hθ hN hc hn
end
end

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLattice_action_of_finiteOrder_automorphism : ∀ (E : Type) [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ), IsMonHom θ → 0 < N → (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A → (∀ a, act.act a ≫ θ = θ ≫ act.act a) → 0 < n → ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧ (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  atlas_forward_decl GlobalTheory.periodLattice_of_finiteOrder
end

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_mem_smul_top_of_neat_level_alt : ∀ (E : Type) [Field E] [NumberField E] (La Λ Q : Type) [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Q] [Module (𝓞 E) Q] (J : Ideal (𝓞 E)) (n N m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)) (ev : La →ₗ[𝓞 E] Q) (ψ : Λ →ₗ[𝓞 E] Q) (θ : Q →ₗ[𝓞 E] Q) (F : Λ →ₗ[𝓞 E] Λ) (gM : La →ₗ[𝓞 E] La), Module.Finite (𝓞 E) Λ → Module.IsTorsionFree (𝓞 E) Λ → 0 < n → (n : 𝓞 E) ∈ J → (∀ a, ev a = 0 ↔ a ∈ J • (⊤ : Submodule (𝓞 E) La)) → (∀ q : Q, (∀ c ∈ J, c • q = 0) → ∃ a, ev a = q) → (∀ b, ψ b = 0 ↔ ∃ b', b = n • b') → (∀ q : Q, n • q = 0 → ∃ b, ψ b = q) → (∀ b, ψ (F b) = θ (ψ b)) → (∀ a, θ (ev (gM a)) = ev a) → 0 < N → F ^ N = 1 → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → J ≤ I₁ → J ≤ I₂ → (∀ x, ((gM - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) La)) → (∀ x, ((gM - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) La)) → ∀ a, gM a - a ∈ J • (⊤ : Submodule (𝓞 E) La) := by
  first | exact @GlobalTheory.sub_mem_smul_top_of_neat_level | exact GlobalTheory.sub_mem_smul_top_of_neat_level | (intros; apply GlobalTheory.sub_mem_smul_top_of_neat_level <;> assumption)
end

section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FreeLev

@[instance_reducible] def ptModule {E : Type} [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) :
    letI := P.isAb.comm
    Module (𝓞 E) (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) :=
  letI := P.isAb.comm
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  { smul := fun c q => Additive.ofMul (q.toMul ≫ act.act c)
    one_smul := fun q => by
      show Additive.ofMul (q.toMul ≫ act.act 1) = q
      rw [act.one, Category.comp_id]; rfl
    mul_smul := fun a b q => by
      show Additive.ofMul (q.toMul ≫ act.act (a * b)) = Additive.ofMul ((q.toMul ≫ act.act b) ≫ act.act a)
      rw [mul_comm, act.mul, Category.assoc]
    smul_zero := fun c => by
      haveI := act.hom c
      show Additive.ofMul ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) ≫ act.act c) = Additive.ofMul 1
      rw [MonObj.one_comp]
    smul_add := fun c q q' => by
      haveI := act.hom c
      show Additive.ofMul ((q.toMul * q'.toMul) ≫ act.act c) = Additive.ofMul (q.toMul ≫ act.act c * q'.toMul ≫ act.act c)
      rw [MonObj.mul_comp]
    add_smul := fun a b q => by
      show Additive.ofMul (q.toMul ≫ act.act (a + b)) = Additive.ofMul (q.toMul ≫ act.act a * q.toMul ≫ act.act b)
      rw [act.add, MonObj.comp_mul]
    zero_smul := fun q => by
      show Additive.ofMul (q.toMul ≫ act.act 0) = Additive.ofMul 1
      rw [h0, MonObj.comp_one] }

set_option maxHeartbeats 800000 in

theorem free_of_unip : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (h : G → (Dw.La →ₗ[𝓞 E] Dw.La)) (m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)), 1 ≤ Dw.p + Dw.q → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → l.Mb ≤ I₁ → l.Mb ≤ I₂ → (∀ g x, ((h g - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g x, ((h g - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g, (∀ x, h g x - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → g = 1) → FreePt Xo c (fun g => (h g, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La))) := by
  intro E _ _ _ H Dw l Xo c G _ h m g₁ g₂ I₁ I₂ _ hg₁ hg₂ hne hI₁ hI₂ hm₁ hm₂ hMb₁ hMb₂ hu₁ hu₂ hfaith
  intro g k _ _ y y' hR hx
  obtain ⟨ρ, ν, -, hlev, hmove⟩ := hR
  have hfix : y.x ≫ ρ = y.x := hmove.1.symm.trans hx
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_fixed_complexPoint_of_fixed_fieldPoint E H Dw l Xo k y.x ρ hfix
  obtain ⟨P, act, θ, N, ev, hθ, hN, hθN, hcomm, hadd, hlin, hker, honto, hrel⟩ :=
    GlobalTheory.T.exists_finiteOrder_fibreAut_at_levelMove_fixedPoint E H Dw l Xo x' ρ ν (h g) LinearMap.id hlev hx'
  have hM0 : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Λ, _, _, F, ψ, hfin, htf, hFN, hψadd, hψlin, hψker, hψonto, hψF⟩ :=
    GlobalTheory.T.periodLattice_action_of_finiteOrder_automorphism E P act θ N l.M hθ hN hθN hcomm hM0
  letI := P.isAb.comm
  letI : Module (𝓞 E) (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) := ptModule P act
  let evL : Dw.La →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun a => Additive.ofMul (ev a)
      map_add' := fun a b => congrArg Additive.ofMul (hadd a b)
      map_smul' := fun c a => congrArg Additive.ofMul (hlin c a) }
  let ψL : Λ →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun a => Additive.ofMul (ψ a)
      map_add' := fun a b => congrArg Additive.ofMul (hψadd a b)
      map_smul' := fun c a => congrArg Additive.ofMul (hψlin c a) }
  let θL : Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun q => Additive.ofMul (q.toMul ≫ θ)
      map_add' := fun q q' => by
        show Additive.ofMul ((q.toMul * q'.toMul) ≫ θ) = Additive.ofMul (q.toMul ≫ θ * q'.toMul ≫ θ)
        rw [MonObj.mul_comp]
      map_smul' := fun c q => by
        show Additive.ofMul ((q.toMul ≫ act.act c) ≫ θ) = Additive.ofMul ((q.toMul ≫ θ) ≫ act.act c)
        rw [Category.assoc, Category.assoc, hcomm] }
  have hMmem : (l.M : 𝓞 E) ∈ l.Mb := by
    have h1 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at h1
    exact Ideal.mul_le_left h1
  refine hfaith g (GlobalTheory.T.sub_mem_smul_top_of_neat_level_alt E Dw.La Λ _ l.Mb l.M N m g₁ g₂ I₁ I₂ evL ψL θL F (h g) hfin htf hM0 hMmem
    (fun a => by
      show Additive.ofMul (ev a) = 0 ↔ _
      rw [← hker a]; exact ofMul_eq_zero)
    (fun q hq => by
      obtain ⟨a, ha⟩ := honto q.toMul (fun c hc => by
        have := hq c hc
        exact congrArg Additive.toMul this)
      exact ⟨a, congrArg Additive.ofMul ha⟩)
    (fun b => by
      show Additive.ofMul (ψ b) = 0 ↔ _
      rw [← hψker b]; exact ofMul_eq_zero)
    (fun q hq => by
      obtain ⟨b, hb⟩ := hψonto q.toMul (by
        have := congrArg Additive.toMul hq
        rwa [toMul_nsmul] at this)
      exact ⟨b, congrArg Additive.ofMul hb⟩)
    (fun b => congrArg Additive.ofMul (hψF b))
    (fun a => congrArg Additive.ofMul (hrel a))
    hN hFN hg₁ hg₂ hne hI₁ hI₂ hm₁ hm₂ hMb₁ hMb₂ (hu₁ g) (hu₂ g))

end GlobalTheory.FreeLev
end
end
