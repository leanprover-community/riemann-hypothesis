import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaXNonemptyProvisional

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.KudlaSiegelWeil

namespace GlobalTheory.SmallThetaModules

section Restricted

variable {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]

def AdmFun (s : ∀ i, N i) : Type := {l : ∀ i, N i →ₗ[ℂ] ℂ // {i | l i (s i) ≠ 1}.Finite}

def evFam (s : ∀ i, N i) (ξ : ∀ i, N i) : AdmFun s → ℂ := fun l => ∏ᶠ i, l.1 i (ξ i)

def RTens (s : ∀ i, N i) : Submodule ℂ (AdmFun s → ℂ) :=
  Submodule.span ℂ {z | ∃ ξ, Restr s ξ ∧ z = evFam s ξ}

open Classical in

def pureT (s : ∀ i, N i) (ξ : ∀ i, N i) : RTens s :=
  if h : Restr s ξ then ⟨evFam s ξ, Submodule.subset_span ⟨ξ, h, rfl⟩⟩ else 0

theorem coe_pureT {s ξ : ∀ i, N i} (h : Restr s ξ) : (pureT s ξ : AdmFun s → ℂ) = evFam s ξ := by
  unfold pureT; rw [dif_pos h]

omit [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] in
theorem restr_update [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (v : ι) (x : N v) :
    Restr s (Function.update ξ v x) := by
  refine (h.insert v).subset fun i hi => ?_
  by_cases hv : i = v
  · exact Or.inl hv
  · right
    simpa [Function.update_of_ne hv] using hi

theorem mulSupport_fin {s ξ : ∀ i, N i} (h : Restr s ξ) (l : AdmFun s) :
    (Function.mulSupport fun i => l.1 i (ξ i)).Finite := by
  refine (Set.Finite.union h l.2).subset fun i hi => ?_
  by_cases e : ξ i = s i
  · right
    simpa [e] using hi
  · exact Or.inl e

theorem evFam_update [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (l : AdmFun s) (v : ι) (x : N v) :
    evFam s (Function.update ξ v x) l = l.1 v x * ∏ᶠ (i) (_ : i ≠ v), l.1 i (ξ i) := by
  unfold evFam
  rw [← mul_finprod_cond_ne v (mulSupport_fin (restr_update h v x) l), Function.update_self]
  congr 1
  refine finprod_congr fun i => finprod_congr fun hi => ?_
  rw [Function.update_of_ne hi]

theorem pureT_mlin [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (v : ι) (c : ℂ) (x y : N v) :
    pureT s (Function.update ξ v (c • x + y)) =
      c • pureT s (Function.update ξ v x) + pureT s (Function.update ξ v y) := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, coe_pureT (restr_update h v _), coe_pureT (restr_update h v _),
    coe_pureT (restr_update h v _)]
  funext l
  simp only [Pi.add_apply, Pi.smul_apply, evFam_update h, map_add, map_smul, smul_eq_mul]
  ring

theorem pureT_span (s : ∀ i, N i) :
    Submodule.span ℂ {z | ∃ ξ, Restr s ξ ∧ z = pureT s ξ} = ⊤ := by
  apply Submodule.map_injective_of_injective (RTens s).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  change _ = Submodule.span ℂ _
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨ξ, h, rfl⟩, rfl⟩
    exact ⟨ξ, h, coe_pureT h⟩
  · rintro ⟨ξ, h, rfl⟩
    exact ⟨_, ⟨ξ, h, rfl⟩, coe_pureT h⟩

theorem pureT_sep (s : ∀ i, N i) (l : ∀ i, N i →ₗ[ℂ] ℂ) (hl : {i | l i (s i) ≠ 1}.Finite) :
    ∃ Λ : RTens s →ₗ[ℂ] ℂ, ∀ ξ, Restr s ξ → Λ (pureT s ξ) = ∏ᶠ i, l i (ξ i) :=
  ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : AdmFun s => ℂ) (show AdmFun s from ⟨l, hl⟩)).comp (RTens s).subtype,
    fun _ h => congrFun (coe_pureT h) (show AdmFun s from ⟨l, hl⟩)⟩

theorem exists_lift {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (m : ∀ i, M i)
    {S : Type} [AddCommGroup S] [Module ℂ S] (pu : (∀ i, M i) → S)
    (hsep : ∀ l : ∀ i, M i →ₗ[ℂ] ℂ, {i | l i (m i) ≠ 1}.Finite →
      ∃ Λ : S →ₗ[ℂ] ℂ, ∀ φ, Restr m φ → Λ (pu φ) = ∏ᶠ i, l i (φ i))
    (s : ∀ i, N i) (p : ∀ i, M i →ₗ[ℂ] N i) :
    ∃ P : S →ₗ[ℂ] RTens s, ∀ φ, Restr m φ → P (pu φ) = pureT s fun i => p i (φ i) := by
  by_cases hp : {i | p i (m i) ≠ s i}.Finite
  · have h1 : ∀ l : AdmFun s, ∃ Λ : S →ₗ[ℂ] ℂ, ∀ φ, Restr m φ → Λ (pu φ) = ∏ᶠ i, l.1 i (p i (φ i)) := by
      intro l
      refine hsep (fun i => (l.1 i).comp (p i)) ((hp.union l.2).subset fun i hi => ?_)
      by_cases e : p i (m i) = s i
      · right
        simpa [e] using hi
      · exact Or.inl e
    choose Λ hΛ using h1
    obtain ⟨r, hr⟩ := (RTens s).subtype.exists_leftInverse_of_injective (RTens s).ker_subtype
    refine ⟨r.comp (LinearMap.pi Λ), fun φ hφ => ?_⟩
    have h2 : Restr s fun i => p i (φ i) := by
      refine (Set.Finite.union hφ hp).subset fun i hi => ?_
      by_cases e : φ i = m i
      · right
        simpa [e] using hi
      · exact Or.inl e
    have h3 : LinearMap.pi Λ (pu φ) = (RTens s).subtype (pureT s fun i => p i (φ i)) := by
      rw [Submodule.subtype_apply, coe_pureT h2]
      funext l
      exact hΛ l φ hφ
    rw [LinearMap.comp_apply, h3, ← LinearMap.comp_apply, hr, LinearMap.id_apply]
  · refine ⟨0, fun φ hφ => ?_⟩
    have h2 : ¬ Restr s fun i => p i (φ i) := by
      intro h
      refine hp ((Set.Finite.union hφ h).subset fun i hi => ?_)
      by_cases e : φ i = m i
      · right
        simpa [e] using hi
      · exact Or.inl e
    unfold pureT
    rw [dif_neg h2, LinearMap.zero_apply]

end Restricted

variable {D : D7} {X : ThetaX D}

def PureSep (L : LocW D X) : Prop :=
  ∀ (V W : HS D) (l : ∀ v, L.SchL V W v →ₗ[ℂ] ℂ), {v | l v (L.vac V W v) ≠ 1}.Finite →
    ∃ Λ : X.Sch V W →ₗ[ℂ] ℂ, ∀ φ, Restr (L.vac V W) φ → Λ (L.pure V W φ) = ∏ᶠ v, l v (φ v)

theorem isThetaMap_zero (L : LocW D X) (V W : HS D) (χ₁ χ₂ : X.Chr) (v : Pl D) {N : Type} [AddCommGroup N]
    [Module ℂ N] (σ : Representation ℂ (L.Hloc W v) N) : IsThetaMap L V W χ₁ χ₂ v σ 0 := by
  intro g h φ
  simp

theorem exists_module (L : LocW D X) (V W : HS D) (χ₁ χ₂ : X.Chr) (v : Pl D) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (π : Representation ℂ (L.Hloc W v) M),
      HasSmallTheta L V W χ₁ χ₂ v → SmallTheta L V W χ₁ χ₂ v π := by
  by_cases h : HasSmallTheta L V W χ₁ χ₂ v
  · obtain ⟨M, i1, i2, π, hπ⟩ := h
    exact ⟨M, i1, i2, π, fun _ => hπ⟩
  · exact ⟨PUnit, inferInstance, inferInstance, 1, fun h' => absurd h' h⟩

theorem exists_thetaMap (L : LocW D X) (V W : HS D) (χ₁ χ₂ : X.Chr) (v : Pl D) {N : Type} [AddCommGroup N]
    [Module ℂ N] (σ : Representation ℂ (L.Hloc W v) N) (y : N) :
    ∃ p : L.SchL V W v →ₗ[ℂ] N, IsThetaMap L V W χ₁ χ₂ v σ p ∧
      ((∃ f, f ≠ 0 ∧ IsThetaMap L V W χ₁ χ₂ v σ f) → p ≠ 0) ∧
      ((∃ f, f ≠ 0 ∧ IsThetaMap L V W χ₁ χ₂ v σ f ∧ f (L.vac V W v) = y) → p (L.vac V W v) = y) := by
  by_cases h : ∃ f, f ≠ 0 ∧ IsThetaMap L V W χ₁ χ₂ v σ f ∧ f (L.vac V W v) = y
  · obtain ⟨f, h0, h1, h2⟩ := h
    exact ⟨f, h1, fun _ => h0, fun _ => h2⟩
  · by_cases h' : ∃ f, f ≠ 0 ∧ IsThetaMap L V W χ₁ χ₂ v σ f
    · obtain ⟨f, h0, h1⟩ := h'
      exact ⟨f, h1, fun _ => h0, fun k => absurd k h⟩
    · exact ⟨0, isThetaMap_zero L V W χ₁ χ₂ v σ, fun k => absurd k h', fun k => absurd k h⟩




section Collapse

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def colMon (V : HS D) : Pl D → Type
  | Sum.inl v => Matrix.GeneralLinearGroup (Fin V.rank) (v.adicCompletion (FF D))
  | Sum.inr _ => PUnit

instance (V : HS D) : ∀ v, Monoid (colMon V v)
  | Sum.inl v => inferInstanceAs (Monoid (Matrix.GeneralLinearGroup (Fin V.rank) (v.adicCompletion (FF D))))
  | Sum.inr _ => inferInstanceAs (Monoid PUnit)

def collapsed (X : ThetaX D) (hX : ∀ V W, X.kfin V W = ⊥) : LocW D X where
  sR := true
  ChrF := ℤˣ
  res := 1
  eta := -1
  eta_sq := by simp
  eta_ne := by decide
  cc := invMonoidHom
  cc_cc := fun χ => inv_inv χ
  res_cc := fun _ => rfl
  cc_inf := fun χ τ => by
    have h1 := X.infTy_mul 1 1 τ
    have h2 := X.infTy_mul χ⁻¹ χ τ
    rw [one_mul] at h1
    rw [inv_mul_cancel] at h2
    change X.infTy χ⁻¹ τ = _
    linarith
  unr := fun _ _ => True
  val := fun _ _ => 1
  unr_one := fun _ => ⟨trivial, rfl⟩
  unr_mul := fun _ _ _ _ _ => ⟨trivial, by simp⟩
  unr_inv := fun _ _ _ => trivial
  val_ram := fun _ _ h => absurd trivial h
  val_abs := fun _ _ _ => by simp
  unr_ae := fun _ => by simp
  valI := fun _ _ => 1
  valI_one := fun _ => rfl
  valI_mul := fun _ _ _ _ _ _ => by simp
  valI_prime := fun _ _ _ => rfl
  locChr := fun _ _ => 1
  locChr_mul := fun _ _ _ => by simp
  G := fun _ => PUnit
  μG := fun _ => Measure.dirac ()
  GF := fun _ => ⊤
  Fd := fun _ => Set.univ
  Fd_fund := fun _ =>
    ⟨nullMeasurableSet_univ, Filter.Eventually.of_forall fun _ => ⟨1, trivial⟩,
      fun a b h => absurd (Subsingleton.elim a b) h⟩
  ht := fun _ _ => 1
  ht_ge := fun _ _ => le_rfl
  ht_mul := fun _ _ _ => by simp
  Gk := fun _ => ⊤
  om := fun _ _ _ _ => 1
  thF := fun _ _ => 0
  thF_aut := by intros; rfl
  Hloc := colMon
  aug := fun _ _ => 1
  aug_fin := fun _ _ _ => rfl
  loc := fun _ _ => 1
  aug_loc := fun _ _ _ => rfl
  SchL := fun _ _ _ => ℂ
  omL := fun _ _ _ _ _ => 1
  vac := fun _ _ _ => 1
  pure := fun _ _ _ => 0
  pure_span := fun V W => by
    rw [hX, Submodule.span_eq_bot]
    rintro _ ⟨_, -, rfl⟩
    rfl
  pure_om := by intros; rfl
  pure_mlin := by intros; simp
  glL := fun V v _ _ => MonoidHom.id (Matrix.GeneralLinearGroup (Fin V.rank) (v.adicCompletion (FF D)))
  glL_bij := fun _ _ _ _ _ => Function.bijective_id
  linM := fun _ _ _ _ _ => LinearMap.pi fun _ => LinearMap.id
  linM_inj := fun _ _ _ _ _ _ a b h => congrFun h 0
  linM_eq := by
    intros
    exact ⟨1, one_ne_zero, fun φ => by rw [one_smul]; rfl⟩





end Collapse

end GlobalTheory.SmallThetaModules

end
