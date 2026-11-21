import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGlueCut
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocGlue

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section G3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def GlueFwd (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' →
    ∃ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩, IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ ∧
      ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂

def GlueBack (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) → MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ →
    ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩, IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ →
    ∃ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' ∧
      ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂

def GlueInj (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ Λ₂' : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' → H.IsGeneric ⟨Λ₂', f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂' φ φ' →
      (∀ m₁ m₂, GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂ ↔
        GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂' φ φ' m₁ m₂) → Λ₂ = Λ₂'

theorem mmInt_of_generic {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (Λ₂ : Submodule M.L.O V) (f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (hg : H.IsGeneric ⟨Λ₂, f₂, f₂', T, T'⟩) : MMInt H (⟨⊥, f₂, f₂', T, T'⟩ : Term V M r) := by
  have hsub : MMo H (⟨⊥, f₂, f₂', T, T'⟩ : Term V M r) ≤ Λ₂ := by
    refine (Submodule.span_le (R := M.L.O)).2 ?_
    rintro _ ⟨a, rfl⟩
    exact hg.2.1 a
  intro m hm m' hm'
  exact (hg.1.1.2.2 m).1 (hsub hm) m' (hsub hm')

theorem dd_ext {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    {t₁ t₂ : Term V M r} (θ θ' : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂)
    (h : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔ θ' (ddMk H t₁ m₁) = ddMk H t₂ m₂) : θ = θ' := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨m₁, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m₂, hm₂⟩ := Submodule.Quotient.mk_surjective _ (θ (Submodule.Quotient.mk m₁))
  have h₁ : θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ := hm₂.symm
  exact h₁.trans ((h m₁ m₂).1 h₁).symm

theorem glue_of (M : Model F E) (r n : ℕ) (hF : GlueFwd M r n) (hB : GlueBack M r n) (hI : GlueInj M r n) :
    Glue M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp
  have fw := hF V H hn t₁ f₂ f₂' φ φ' hyp
  have bk := hB V H hn t₁ f₂ f₂' φ φ' hyp
  have inj := hI V H hn t₁ f₂ f₂' φ φ' hyp
  let toθ : {Λ₂ : Submodule M.L.O V // H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ'} →
      {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ //
        IsUnit (H.Dl f₂ f₂' (r + 1)) ∧ MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ ∧
          IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ} :=
    fun x => ⟨(fw x.1 x.2.1 x.2.2).choose, x.2.1.1.2.2.2.1, mmInt_of_generic H x.1 f₂ f₂' t₁.T t₁.T' x.2.1,
      (fw x.1 x.2.1 x.2.2).choose_spec.1⟩
  have toθ_spec : ∀ x m₁ m₂, (toθ x).1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
      GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ x.1 φ φ' m₁ m₂ :=
    fun x => (fw x.1 x.2.1 x.2.2).choose_spec.2
  have hinj : Function.Injective toθ := by
    intro x y hxy
    apply Subtype.ext
    refine inj x.1 y.1 x.2.1 x.2.2 y.2.1 y.2.2 fun m₁ m₂ => ?_
    rw [← toθ_spec x, ← toθ_spec y, hxy]
  have hsurj : Function.Surjective toθ := by
    intro θ
    obtain ⟨Λ₂, hg, hth, hrel⟩ := bk θ.2.1 θ.2.2.1 θ.1 θ.2.2.2
    refine ⟨⟨Λ₂, hg, hth⟩, Subtype.ext (dd_ext H _ _ fun m₁ m₂ => ?_)⟩
    rw [toθ_spec, hrel]
  exact ⟨Equiv.ofBijective toθ ⟨hinj, hsurj⟩, toθ_spec⟩

end G3

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Psi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem MMfam_mem_sup (t : Term V M r) (i : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam t i ∈ H.Xp t.f ⊔ H.Xp t.f' := by
  have hf : ∀ a, t.f a ∈ H.Xp t.f ⊔ H.Xp t.f' := fun a =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  have hf' : ∀ a, t.f' a ∈ H.Xp t.f ⊔ H.Xp t.f' := fun a =>
    Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
  unfold HermSp.MMfam
  rcases M.split with _ | g
  · rcases i with a | a
    · exact hf a
    · exact hf' a
  · rcases i with a | a
    · exact hf a
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hf' a) (hf a))

theorem hermitian_W0_span_zero (t : Term V M r) {w m : V} (hw : w ∈ H.W0 t.f t.f')
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) : H.h w m = 0 := by
  have hle : Submodule.span E (Set.range (H.MMfam t)) ≤ H.Xp t.f ⊔ H.Xp t.f' :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact MMfam_mem_sup H t i)
  exact hw m (hle hm)


def psiSharp (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) :
    ↥(ThSharp H t₁ N₁) ≃ₗ[M.L.O] ↥(ThSharp H t₂ N₂) where
  toFun x := ⟨ψ ⟨x.1, x.2.1⟩, (ψ ⟨x.1, x.2.1⟩).2, fun n hn => by
    have hnW : n ∈ H.W0 t₂.f t₂.f' := hN₂ hn
    have e : ψ (ψ.symm ⟨n, hnW⟩) = ⟨n, hnW⟩ := ψ.apply_symm_apply _
    have h1 : ((ψ.symm ⟨n, hnW⟩ : ↥(H.W0 t₁.f t₁.f')) : V) ∈ N₁ := by
      rw [hN, e]; exact hn
    have h2 := x.2.2 _ h1
    have h3 := hψ ⟨x.1, x.2.1⟩ (ψ.symm ⟨n, hnW⟩)
    rw [e] at h3
    rw [h3]
    exact h2⟩
  invFun y := ⟨ψ.symm ⟨y.1, y.2.1⟩, (ψ.symm ⟨y.1, y.2.1⟩).2, fun n hn => by
    have hnW : n ∈ H.W0 t₁.f t₁.f' := hN₁ hn
    have h1 : ((ψ ⟨n, hnW⟩ : ↥(H.W0 t₂.f t₂.f')) : V) ∈ N₂ := (hN ⟨n, hnW⟩).1 hn
    have h2 := y.2.2 _ h1
    have h3 := hψ (ψ.symm ⟨y.1, y.2.1⟩) ⟨n, hnW⟩
    rw [ψ.apply_symm_apply] at h3
    rw [← h3]
    exact h2⟩
  map_add' x y := by
    apply Subtype.ext
    have e : (⟨((x + y : ↥(ThSharp H t₁ N₁)) : V), (x + y).2.1⟩ : ↥(H.W0 t₁.f t₁.f')) =
        ⟨x.1, x.2.1⟩ + ⟨y.1, y.2.1⟩ := Subtype.ext rfl
    change ((ψ ⟨((x + y : ↥(ThSharp H t₁ N₁)) : V), (x + y).2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V) =
      ((ψ ⟨x.1, x.2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V) + ((ψ ⟨y.1, y.2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V)
    rw [e, map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    have e : (⟨((c • x : ↥(ThSharp H t₁ N₁)) : V), (c • x).2.1⟩ : ↥(H.W0 t₁.f t₁.f')) =
        (c : E) • ⟨x.1, x.2.1⟩ := Subtype.ext rfl
    change ((ψ ⟨((c • x : ↥(ThSharp H t₁ N₁)) : V), (c • x).2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V) =
      (c : E) • ((ψ ⟨x.1, x.2.1⟩ : ↥(H.W0 t₂.f t₂.f')) : V)
    rw [e, map_smul]
    rfl
  left_inv x := by
    apply Subtype.ext
    show ((ψ.symm ⟨(ψ ⟨x.1, x.2.1⟩ : V), _⟩ : ↥(H.W0 t₁.f t₁.f')) : V) = x.1
    rw [Subtype.coe_eta, ψ.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    show ((ψ ⟨(ψ.symm ⟨y.1, y.2.1⟩ : V), _⟩ : ↥(H.W0 t₂.f t₂.f')) : V) = y.1
    rw [Subtype.coe_eta, ψ.apply_symm_apply]

theorem psiSharp_val (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) (x : ↥(ThSharp H t₁ N₁)) :
    ((psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN x : ↥(ThSharp H t₂ N₂)) : V) = (ψ ⟨x.1, x.2.1⟩ : V) := rfl

def psiTilde (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hψ : ∀ x y, H.h (ψ x) (ψ y) = H.h x y) (N₁ N₂ : Submodule M.L.O V)
    (hN₁ : N₁ ≤ (H.W0 t₁.f t₁.f').restrictScalars M.L.O) (hN₂ : N₂ ≤ (H.W0 t₂.f t₂.f').restrictScalars M.L.O)
    (hN : ∀ x : ↥(H.W0 t₁.f t₁.f'), (x : V) ∈ N₁ ↔ (ψ x : V) ∈ N₂) :
    DDW H t₁ N₁ ≃ₗ[M.L.O] DDW H t₂ N₂ :=
  Submodule.Quotient.equiv _ _ (psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show ((psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN x : ↥(ThSharp H t₂ N₂)) : V) ∈ N₂
      rw [psiSharp_val]
      exact (hN _).1 hx
    · intro hy
      refine ⟨(psiSharp H t₁ t₂ ψ hψ N₁ N₂ hN₁ hN₂ hN).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
      change ((ψ.symm ⟨y.1, y.2.1⟩ : ↥(H.W0 t₁.f t₁.f')) : V) ∈ N₁
      rw [hN (ψ.symm ⟨y.1, y.2.1⟩), ψ.apply_symm_apply]
      exact hy)


end Psi

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Fwd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

set_option maxHeartbeats 800000 in
theorem glueFwd_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) (hE : GlueEta M r) :
    GlueFwd M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT Λ₂ hG₂ hTh
  set t₂ : Term V M r := { abelian₂ := Λ₂, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } with ht₂
  have memS : ∀ (t : Term V M r) (N : Submodule M.L.O V) (w : V),
      w ∈ ThSharp H t N ↔ (w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O) :=
    fun _ _ _ => Iff.rfl
  have memL : ∀ (t : Term V M r) (w : V), w ∈ ThL H t ↔ (w ∈ t.abelian₂ ∧ w ∈ H.W0 t.f t.f') :=
    fun _ _ => Iff.rfl
  have hDl : IsUnit (H.Dl f₂ f₂' (r + 1)) := by
    obtain ⟨⟨_, _, _, hD, _⟩, _⟩ := hG₂
    exact hD
  have hG₁ : H.IsGeneric t₁ := by
    obtain ⟨h, -⟩ := id hT
    exact h
  obtain ⟨ψ, hψh, hψC⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hDl
  have key : ∀ (x : V) (hx : x ∈ H.W0 t₁.f t₁.f'), x ∈ t₁.abelian₂ ↔ (ψ ⟨x, hx⟩ : V) ∈ Λ₂ :=
    fun x hx => hTh x _ ((hψC x _).2 ⟨hx, rfl⟩)
  obtain ⟨η₁, hη₁a, hη₁b⟩ := hE hM V H t₁ hG₁
  obtain ⟨η₂, hη₂a, hη₂b⟩ := hE hM V H t₂ hG₂
  have fwd : ∀ (w : V) (hw : w ∈ ThSharp H t₁ (ThL H t₁)),
      (ψ ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₂ (ThL H t₂) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h1 : (ψ (ψ.symm ⟨n, hnW⟩) : V) = n := by simp
    rw [← h1, hψh]
    refine ((memS _ _ _).1 hw).2 _ ((memL _ _).2 ⟨?_, (ψ.symm ⟨n, hnW⟩).2⟩)
    exact (key _ (ψ.symm ⟨n, hnW⟩).2).2 (by simpa [ht₂] using hnΛ)
  have bwd : ∀ (w : V) (hw : w ∈ ThSharp H t₂ (ThL H t₂)),
      (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₁ (ThL H t₁) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ.symm _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h2 := hψh (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩) ⟨n, hnW⟩
    simp only [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact ((memS _ _ _).1 hw).2 _ ((memL _ _).2 ⟨(key n hnW).1 hnΛ, (ψ ⟨n, hnW⟩).2⟩)
  let e : ThSharp H t₁ (ThL H t₁) ≃ₗ[M.L.O] ThSharp H t₂ (ThL H t₂) :=
    { toFun := fun w => ⟨_, fwd w.1 w.2⟩
      invFun := fun w => ⟨_, bwd w.1 w.2⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memS _ _ _).1 a.2).1⟩ ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
        exact h
      map_smul' := by
        intro c a
        apply Subtype.ext
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memS _ _ _).1 a.2).1⟩)
        exact h
      left_inv := by
        intro a
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp }
  have hPQ : Submodule.map (e : ThSharp H t₁ (ThL H t₁) →ₗ[M.L.O] ThSharp H t₂ (ThL H t₂))
      (Submodule.comap (ThSharp H t₁ (ThL H t₁)).subtype (ThL H t₁)) =
      Submodule.comap (ThSharp H t₂ (ThL H t₂)).subtype (ThL H t₂) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h1, -⟩ := (memL _ _).1 hy
      exact (memL _ _).2 ⟨(key _ _).1 h1, (ψ _).2⟩
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      obtain ⟨h1, -⟩ := (memL _ _).1 hx
      refine (memL _ _).2 ⟨?_, (ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩).2⟩
      exact (key _ (ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩).2).2 (by simpa [ht₂] using h1)
  let κ : DDW H t₁ (ThL H t₁) ≃ₗ[M.L.O] DDW H t₂ (ThL H t₂) := Submodule.Quotient.equiv _ _ e hPQ
  have hκ : ∀ w, κ (dwMk H t₁ (ThL H t₁) w) = dwMk H t₂ (ThL H t₂) (e w) := fun w => rfl
  have surj : ∀ m : MMsharp H t₁, ∃ w, η₁ (ddMk H t₁ m) = dwMk H t₁ (ThL H t₁) w := by
    intro m
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (η₁ (ddMk H t₁ m))
    exact ⟨w, hw.symm⟩
  have hh : ∀ a b : ThSharp H t₁ (ThL H t₁), H.h (e a : V) (e b : V) = H.h a b :=
    fun a b => hψh ⟨a, ((memS _ _ _).1 a.2).1⟩ ⟨b, ((memS _ _ _).1 b.2).1⟩
  refine ⟨(η₁.trans κ).trans η₂.symm, ?_, ?_⟩
  · intro x y x₂ y₂ hx hy
    obtain ⟨w, hw⟩ := surj x
    obtain ⟨w', hw'⟩ := surj y
    change η₂.symm (κ (η₁ (ddMk H t₁ x))) = _ at hx
    change η₂.symm (κ (η₁ (ddMk H t₁ y))) = _ at hy
    have hx' := (LinearEquiv.symm_apply_eq η₂).1 hx
    have hy' := (LinearEquiv.symm_apply_eq η₂).1 hy
    rw [hw, hκ] at hx'
    rw [hw', hκ] at hy'
    have a1 := hη₁b x y w w' hw hw'
    have a2 := hη₂b x₂ y₂ (e w) (e w') hx'.symm hy'.symm
    rw [hh] at a2
    have a3 := sub_mem a2 a1
    convert a3 using 1
    ring
  · intro m₁ m₂
    obtain ⟨w, hw⟩ := surj m₁
    have hmw : (m₁ : V) + w ∈ t₁.abelian₂ := (hη₁a m₁ w).1 hw
    change η₂.symm (κ (η₁ (ddMk H t₁ m₁))) = _ ↔ _
    rw [hw, hκ]
    constructor
    · intro h
      have h' := (LinearEquiv.symm_apply_eq η₂).1 h
      exact ⟨w, e w, (hψC _ _).2 ⟨((memS _ _ _).1 w.2).1, rfl⟩, hmw, (hη₂a m₂ (e w)).1 h'.symm⟩
    · rintro ⟨n₁, n₂, hc, h1, h2⟩
      obtain ⟨hn₁, hψn⟩ := (hψC n₁ n₂).1 hc
      have hd : n₁ - w ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁ ((memS _ _ _).1 w.2).1
      have hdL : n₁ - w ∈ t₁.abelian₂ := by
        have h4 := t₁.abelian₂.sub_mem h1 hmw
        simpa using h4
      have hψd : (ψ ⟨n₁ - w, hd⟩ : V) = n₂ - (e w : V) := by
        rw [← hψn]
        exact congrArg Subtype.val (map_sub ψ ⟨n₁, hn₁⟩ ⟨(w : V), ((memS _ _ _).1 w.2).1⟩)
      have h3 := (key _ hd).1 hdL
      rw [hψd] at h3
      have h5 := Λ₂.sub_mem h2 h3
      have h6 : (m₂ : V) + (e w : V) ∈ t₂.abelian₂ := by
        convert h5 using 1
        abel
      apply (LinearEquiv.symm_apply_eq η₂).2
      exact ((hη₂a m₂ (e w)).2 h6).symm

end Fwd

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Back

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def GramMM (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) → IsUnit (H.gram (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r))).det

def ThFG (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t → (ThL H t).FG

def ThSpan (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t →
    Submodule.span E (ThL H t : Set V) = H.W0 t.f t.f'

set_option maxHeartbeats 800000 in
theorem glueBack_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) : GlueBack M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT hDl hMM θ hθ
  let t₀ : Term V M r := { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' }
  have memS : ∀ (t : Term V M r) (N : Submodule M.L.O V) (w : V),
      w ∈ ThSharp H t N ↔ (w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O) :=
    fun _ _ _ => Iff.rfl
  have memL : ∀ (t : Term V M r) (w : V), w ∈ ThL H t ↔ (w ∈ t.abelian₂ ∧ w ∈ H.W0 t.f t.f') :=
    fun _ _ => Iff.rfl
  have hG₁ : H.IsGeneric t₁ := by
    obtain ⟨h, -⟩ := id hT
    exact h
  have hsd : ∀ x : V, x ∈ t₁.abelian₂ ↔ ∀ y ∈ t₁.abelian₂, H.h x y ∈ M.L.O := by
    obtain ⟨⟨⟨-, -, h⟩, -⟩, -⟩ := id hG₁
    exact h
  obtain ⟨ψ, hψh, hψC⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hDl
  obtain ⟨η₁, hη₁a, hη₁b⟩ := hE hM V H t₁ hG₁
  let g : ThL H t₁ →ₗ[M.L.O] V :=
    { toFun := fun x => (ψ ⟨x, ((memL _ _).1 x.2).2⟩ : V)
      map_add' := fun a b => by
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memL _ _).1 a.2).2⟩ ⟨(b : V), ((memL _ _).1 b.2).2⟩)
        exact h
      map_smul' := fun c a => by
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memL _ _).1 a.2).2⟩)
        exact h }
  have hg : ∀ y : ThL H t₁, g y = (ψ ⟨y, ((memL _ _).1 y.2).2⟩ : V) := fun _ => rfl
  obtain ⟨N₂, hN₂⟩ : ∃ N : Submodule M.L.O V, N = Submodule.map g ⊤ := ⟨_, rfl⟩
  have memN : ∀ v : V, v ∈ N₂ ↔ ∃ y, g y = v := by
    intro v
    rw [hN₂]
    simp only [Submodule.mem_map, Submodule.mem_top, true_and]
  have keyN : ∀ (x : V) (hx : x ∈ H.W0 t₁.f t₁.f'), x ∈ t₁.abelian₂ ↔ (ψ ⟨x, hx⟩ : V) ∈ N₂ := by
    intro x hx
    constructor
    · intro h
      exact (memN _).2 ⟨⟨x, (memL _ _).2 ⟨h, hx⟩⟩, rfl⟩
    · intro h
      obtain ⟨y, hy⟩ := (memN _).1 h
      rw [hg] at hy
      have h2 : (y : V) = x := congrArg Subtype.val (ψ.injective (Subtype.ext hy))
      rw [← h2]
      exact ((memL _ _).1 y.2).1
  have fwd : ∀ (w : V) (hw : w ∈ ThSharp H t₁ (ThL H t₁)),
      (ψ ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₀ N₂ := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ _).2, ?_⟩
    intro n hn'
    obtain ⟨y, rfl⟩ := (memN _).1 hn'
    rw [hg, hψh]
    exact ((memS _ _ _).1 hw).2 _ y.2
  have bwd : ∀ (w : V) (hw : w ∈ ThSharp H t₀ N₂),
      (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₁ (ThL H t₁) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ.symm _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h2 := hψh (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩) ⟨n, hnW⟩
    simp only [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact ((memS _ _ _).1 hw).2 _ ((memN _).2 ⟨⟨n, hn'⟩, rfl⟩)
  let e : ThSharp H t₁ (ThL H t₁) ≃ₗ[M.L.O] ThSharp H t₀ N₂ :=
    { toFun := fun w => ⟨_, fwd w.1 w.2⟩
      invFun := fun w => ⟨_, bwd w.1 w.2⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memS _ _ _).1 a.2).1⟩ ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
        exact h
      map_smul' := by
        intro c a
        apply Subtype.ext
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memS _ _ _).1 a.2).1⟩)
        exact h
      left_inv := by
        intro a
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp }
  have hPQ : Submodule.map (e : ThSharp H t₁ (ThL H t₁) →ₗ[M.L.O] ThSharp H t₀ N₂)
      (Submodule.comap (ThSharp H t₁ (ThL H t₁)).subtype (ThL H t₁)) =
      Submodule.comap (ThSharp H t₀ N₂).subtype N₂ := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (memN _).2 ⟨⟨y, hy⟩, rfl⟩
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      obtain ⟨y, hy⟩ := (memN _).1 hx
      rw [hg] at hy
      have h4 : ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩ = ⟨(y : V), ((memL _ _).1 y.2).2⟩ :=
        (LinearEquiv.symm_apply_eq ψ).2 (Subtype.ext hy).symm
      have h3 : (e.symm x : V) = y := congrArg Subtype.val h4
      rw [h3]
      exact y.2
  let κ : DDW H t₁ (ThL H t₁) ≃ₗ[M.L.O] DDW H t₀ N₂ := Submodule.Quotient.equiv _ _ e hPQ
  have hκ : ∀ w, κ (dwMk H t₁ (ThL H t₁) w) = dwMk H t₀ N₂ (e w) := fun w => rfl
  have surj : ∀ m : MMsharp H t₁, ∃ w, η₁ (ddMk H t₁ m) = dwMk H t₁ (ThL H t₁) w := by
    intro m
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (η₁ (ddMk H t₁ m))
    exact ⟨w, hw.symm⟩
  have hh : ∀ a b : ThSharp H t₀ N₂, H.h (e.symm a : V) (e.symm b : V) = H.h a b := by
    intro a b
    have h := hψh (ψ.symm ⟨(a : V), ((memS _ _ _).1 a.2).1⟩) (ψ.symm ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  let η : DDt H t₀ ≃ₗ[M.L.O] DDW H t₀ N₂ := (θ.symm.trans η₁).trans κ
  have hle : N₂ ≤ Submodule.restrictScalars M.L.O (H.W0 t₀.f t₀.f') := by
    intro v hv
    obtain ⟨y, rfl⟩ := (memN v).1 hv
    exact (ψ _).2
  have hfg : N₂.FG := by
    rw [hN₂]
    haveI : Module.Finite M.L.O (ThL H t₁) := Module.Finite.iff_fg.2 (hFG V H t₁ hG₁)
    exact (Module.Finite.fg_top).map g
  have hS1 := hS V H t₁ hG₁
  have hspan : Submodule.span E (N₂ : Set V) = H.W0 t₀.f t₀.f' := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      exact hle hv
    · intro v hv
      have hu : ((ψ.symm ⟨v, hv⟩ : H.W0 t₁.f t₁.f') : V) ∈ Submodule.span E (ThL H t₁ : Set V) := by
        rw [hS1]
        exact (ψ.symm _).2
      have main : ∀ (x : V) (hx : x ∈ Submodule.span E (ThL H t₁ : Set V)),
          ∀ h : x ∈ H.W0 t₁.f t₁.f', (ψ ⟨x, h⟩ : V) ∈ Submodule.span E (N₂ : Set V) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          intro h
          exact Submodule.subset_span ((keyN x h).1 ((memL _ _).1 hx).1)
        | zero =>
          intro h
          have h0 : (⟨0, h⟩ : H.W0 t₁.f t₁.f') = 0 := rfl
          rw [h0, map_zero]
          exact Submodule.zero_mem _
        | add x y hx hy ihx ihy =>
          intro h
          have hx' : x ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hx
          have hy' : y ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hy
          have h0 : (⟨x + y, h⟩ : H.W0 t₁.f t₁.f') = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
          rw [h0, map_add, Submodule.coe_add]
          exact Submodule.add_mem _ (ihx hx') (ihy hy')
        | smul a x hx ihx =>
          intro h
          have hx' : x ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hx
          have h0 : (⟨a • x, h⟩ : H.W0 t₁.f t₁.f') = a • ⟨x, hx'⟩ := rfl
          rw [h0, map_smul, Submodule.coe_smul]
          exact Submodule.smul_mem _ a (ihx hx')
      have h4 := main _ hu (ψ.symm ⟨v, hv⟩).2
      simpa using h4
  have hint : ∀ x ∈ N₂, ∀ y ∈ N₂, H.h x y ∈ M.L.O := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (memN x).1 hx
    obtain ⟨b, rfl⟩ := (memN y).1 hy
    rw [hg, hg, hψh]
    exact (hsd _).1 ((memL _ _).1 a.2).1 _ ((memL _ _).1 b.2).1
  have hpair : ∀ (m m' : MMsharp H t₀) (w w' : ThSharp H t₀ N₂),
      η (ddMk H t₀ m) = dwMk H t₀ N₂ w → η (ddMk H t₀ m') = dwMk H t₀ N₂ w' →
      H.h m m' + H.h w w' ∈ M.L.O := by
    intro m m' w w' hw hw'
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₀ m))
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₀ m'))
    have hθx : θ (ddMk H t₁ x) = ddMk H t₀ m := by
      rw [show ddMk H t₁ x = θ.symm (ddMk H t₀ m) from hx, LinearEquiv.apply_symm_apply]
    have hθx' : θ (ddMk H t₁ x') = ddMk H t₀ m' := by
      rw [show ddMk H t₁ x' = θ.symm (ddMk H t₀ m') from hx', LinearEquiv.apply_symm_apply]
    have h1 : η₁ (ddMk H t₁ x) = dwMk H t₁ (ThL H t₁) (e.symm w) := by
      apply κ.injective
      rw [hκ, LinearEquiv.apply_symm_apply, ← hw]
      show κ (η₁ (ddMk H t₁ x)) = κ (η₁ (θ.symm (ddMk H t₀ m)))
      rw [← hx]
      rfl
    have h1' : η₁ (ddMk H t₁ x') = dwMk H t₁ (ThL H t₁) (e.symm w') := by
      apply κ.injective
      rw [hκ, LinearEquiv.apply_symm_apply, ← hw']
      show κ (η₁ (ddMk H t₁ x')) = κ (η₁ (θ.symm (ddMk H t₀ m')))
      rw [← hx']
      rfl
    have a1 := hη₁b x x' (e.symm w) (e.symm w') h1 h1'
    rw [hh] at a1
    have a2 := hθ x x' m m' hθx hθx'
    have a3 := add_mem a2 a1
    convert a3 using 1
    ring
  have hGr := hG V H hn t₁ f₂ f₂' φ φ' hT hDl
  obtain ⟨Λ, ⟨hsd2, hprim, hcap, hη⟩, -⟩ :=
    hV hM V H t₀ hGr hMM N₂ hle hfg hspan hint η hpair
  have hgen := hP hM V H hn t₁ f₂ f₂' φ φ' hT hDl Λ hsd2 hprim
  have hthc : ThCond H t₁ t₀ Λ φ φ' := by
    intro n₁ n₂ hc
    obtain ⟨hn₁, rfl⟩ := (hψC n₁ n₂).1 hc
    rw [keyN n₁ hn₁, ← hcap]
    constructor
    · intro h
      exact (Submodule.mem_inf.1 h).1
    · intro h
      exact Submodule.mem_inf.2 ⟨h, (ψ _).2⟩
  refine ⟨Λ, hgen, hthc, ?_⟩
  intro m₁ m₂
  obtain ⟨w, hw⟩ := surj m₁
  have hmw : (m₁ : V) + w ∈ t₁.abelian₂ := (hη₁a m₁ w).1 hw
  have step : θ (ddMk H t₁ m₁) = ddMk H t₀ m₂ ↔ η (ddMk H t₀ m₂) = dwMk H t₀ N₂ (e w) := by
    constructor
    · intro h
      show κ (η₁ (θ.symm (ddMk H t₀ m₂))) = _
      rw [← h, LinearEquiv.symm_apply_apply, hw, hκ]
    · intro h
      have h2 : κ (η₁ (θ.symm (ddMk H t₀ m₂))) = κ (η₁ (ddMk H t₁ m₁)) := by
        rw [hw, hκ]
        exact h
      have h3 := η₁.injective (κ.injective h2)
      rw [← h3, LinearEquiv.apply_symm_apply]
  refine step.trans ((hη m₂ (e w)).trans ?_)
  constructor
  · intro h
    exact ⟨w, e w, (hψC _ _).2 ⟨((memS _ _ _).1 w.2).1, rfl⟩, hmw, h⟩
  · rintro ⟨n₁, n₂, hc, h1, h2⟩
    obtain ⟨hn₁, rfl⟩ := (hψC n₁ n₂).1 hc
    have hd : n₁ - w ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁ ((memS _ _ _).1 w.2).1
    have hdL : n₁ - w ∈ t₁.abelian₂ := by
      have h4 := t₁.abelian₂.sub_mem h1 hmw
      simpa using h4
    have h3 : (ψ ⟨n₁ - w, hd⟩ : V) ∈ Λ := by
      have h5 := (keyN _ hd).1 hdL
      rw [← hcap] at h5
      exact (Submodule.mem_inf.1 h5).1
    have hψd : (ψ ⟨n₁ - w, hd⟩ : V) = (ψ ⟨n₁, hn₁⟩ : V) - (e w : V) := by
      have h6 := congrArg Subtype.val (map_sub ψ ⟨n₁, hn₁⟩ ⟨(w : V), ((memS _ _ _).1 w.2).1⟩)
      exact h6
    rw [hψd] at h3
    have h5 := Λ.sub_mem h2 h3
    convert h5 using 1
    abel

end Back

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Inj

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem hermSp_W0_eq_perp_span_range_MMfam {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.W0 f f' = H.perp (Submodule.span E (Set.range (Sum.elim f f'))) := by
  rw [Set.Sum.elim_range, Submodule.span_union]
  rfl

theorem span_frames_le_MM {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) :
    Submodule.span E (Set.range (Sum.elim t.f t.f')) ≤ Submodule.span E (Set.range (H.MMfam t)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  unfold HermSp.MMfam
  split
  · exact Submodule.subset_span ⟨i, rfl⟩
  · rename_i g _
    have hq : ((g.q : F)) ≠ 0 := by
      intro h0
      exact g.q_irr.ne_zero (Subtype.ext h0)
    set c : E := algebraMap F E ((g.q : F))⁻¹ with hc
    have hcu : IsUnit c := by
      rw [hc]
      exact (IsUnit.mk0 _ (inv_ne_zero hq)).map (algebraMap F E)
    rcases i with a | a
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · have h1 : t.f a ∈ Submodule.span E (Set.range (Sum.elim t.f fun b => c • (t.f' b - t.f b))) :=
        Submodule.subset_span ⟨Sum.inl a, rfl⟩
      have h2 : c • (t.f' a - t.f a) ∈ Submodule.span E (Set.range (Sum.elim t.f fun b => c • (t.f' b - t.f b))) :=
        Submodule.subset_span ⟨Sum.inr a, rfl⟩
      have h3 : t.f' a = t.f a + (((hcu.unit)⁻¹ : Eˣ) : E) • (c • (t.f' a - t.f a)) := by
        rw [smul_smul, IsUnit.val_inv_mul, one_smul]
        abel
      show t.f' a ∈ _
      rw [h3]
      exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)

private theorem span_MMfam_eq_span_f_f' {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) :
    Submodule.span E (Set.range (H.MMfam t)) = Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  refine le_antisymm ?_ (span_frames_le_MM H t)
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h := MMfam_mem_sup H t i
  refine (sup_le ?_ ?_ : H.Xp t.f ⊔ H.Xp t.f' ≤ _) h
  · exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩)
  · exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩)

private theorem isCompl_span_perp_of_isGeneric {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) (ht : H.IsGeneric t) :
    IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f')))
      (H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f')))) := by
  have h := isCompl_span_frames_W0 H t.f t.f' t.T t.T' ⟨ht.1.2.1.2.1, ht.1.2.1.2.2.1⟩
    ⟨ht.1.2.2.1.2.1, ht.1.2.2.1.2.2.1⟩ ht.1.2.2.2.1 (isUnit_Gdet H _ _ _ _ ht.1.2.2.2.2.1)
  rwa [hermSp_W0_eq_perp_span_range_MMfam] at h

private theorem mem_MMsharp_of_integral_pairing {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) (abelian₂ : Submodule (↥M.L.O) V) (hmem : ∀ a, H.MMfam t a ∈ abelian₂) (u : V)
    (hu : u ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')))
    (hint : ∀ y ∈ abelian₂, y ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) → H.h u y ∈ M.L.O) :
    u ∈ MMsharp H t := by
  refine ⟨by rw [span_MMfam_eq_span_f_f']; exact hu, ?_⟩
  intro m hm
  apply hint m
  · exact (Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hmem a)) hm
  · rw [← span_MMfam_eq_span_f_f' H t]
    exact Submodule.span_le_restrictScalars (↥M.L.O) E _ hm

theorem glueInj_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) : GlueInj M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT Λ₂ Λ₂' hG hTh hG' hTh' hrel
  obtain ⟨ψ, hψh, hψ⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hG.1.2.2.2.1
  have hW₁ := hermSp_W0_eq_perp_span_range_MMfam H t₁.f t₁.f'
  have hW₂ := hermSp_W0_eq_perp_span_range_MMfam H f₂ f₂'
  have hU₁ := isCompl_span_perp_of_isGeneric H t₁ hT.1
  have key : ∀ A B : Submodule (↥M.L.O) V,
      H.IsGeneric { abelian₂ := A, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } →
      ThCond H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ' →
      ThCond H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } B φ φ' →
      (∀ (m₁ : ↥(MMsharp H t₁))
          (m₂ : ↥(MMsharp H { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' })),
          GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ' m₁ m₂ →
          GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } B φ φ' m₁ m₂) →
      A ≤ B := by
    intro A B hGA hThA hThB hAB x hx
    let U₂ : Submodule E V := Submodule.span E (Set.range (Sum.elim f₂ f₂'))
    let U₁ : Submodule E V := Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))
    have hU₂ : IsCompl U₂ (H.perp U₂) := isCompl_span_perp_of_isGeneric H _ hGA
    have gA := local_hermitian_glue F E M hM V H A hGA.1.1 U₂ hU₂
    have g₁ := local_hermitian_glue F E M hM V H t₁.abelian₂ hT.1.1.1 U₁ hU₁
    obtain ⟨p, hp, hpint, q, hq, hqint, hxpq⟩ : ∃ p ∈ U₂, (∀ y ∈ A, y ∈ U₂ → H.h p y ∈ M.L.O) ∧
        ∃ q ∈ H.perp U₂, (∀ y ∈ A, y ∈ H.perp U₂ → H.h q y ∈ M.L.O) ∧ p + q = x :=
      ⟨_, Submodule.coe_mem _, (gA.1 _ (Submodule.coe_mem _)).mp ⟨x, hx, rfl⟩,
       _, Submodule.coe_mem _, (gA.2 _ (Submodule.coe_mem _)).mp ⟨x, hx, rfl⟩,
       Submodule.projection_add_projection_eq_self hU₂ x⟩
    have hpS : p ∈ MMsharp H { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } :=
      mem_MMsharp_of_integral_pairing H _ A hGA.2.1 p hp hpint
    have hqW : q ∈ H.W0 f₂ f₂' := hW₂.ge hq
    obtain ⟨n₁, hψn₁⟩ : ∃ n₁ : ↥(H.W0 t₁.f t₁.f'), (ψ n₁ : V) = q := ⟨ψ.symm ⟨q, hqW⟩, by simp⟩
    have hcorr₁ : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' (n₁ : V) q :=
      (hψ _ _).mpr ⟨n₁.2, hψn₁⟩
    have hn₁int : ∀ y ∈ t₁.abelian₂, y ∈ H.perp U₁ → H.h (n₁ : V) y ∈ M.L.O := by
      intro y hy hyp
      have hyW : y ∈ H.W0 t₁.f t₁.f' := hW₁.ge hyp
      have hc : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' y
          (ψ ⟨y, hyW⟩ : V) := (hψ _ _).mpr ⟨hyW, rfl⟩
      have hyA : (ψ ⟨y, hyW⟩ : V) ∈ A := (hThA _ _ hc).mp hy
      have hyp2 : (ψ ⟨y, hyW⟩ : V) ∈ H.perp U₂ := hW₂.le (ψ ⟨y, hyW⟩).2
      have e : H.h (n₁ : V) y = H.h q (ψ ⟨y, hyW⟩ : V) := by
        rw [← hψn₁]
        exact (hψh n₁ ⟨y, hyW⟩).symm
      rw [e]
      exact hqint _ hyA hyp2
    have hn₁p : (n₁ : V) ∈ H.perp U₁ := hW₁.le n₁.2
    obtain ⟨z, hz, hzn⟩ := (g₁.2 _ hn₁p).mpr hn₁int
    have hmS : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) ∈ MMsharp H t₁ :=
      mem_MMsharp_of_integral_pairing H t₁ t₁.abelian₂ hT.1.2.1 _ (Submodule.coe_mem _)
        ((g₁.1 _ (Submodule.coe_mem _)).mp ⟨z, hz, rfl⟩)
    have hzsum : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + (n₁ : V) = z := by
      rw [← hzn]
      exact Submodule.projection_add_projection_eq_self hU₁ z
    have hz' : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + (n₁ : V) ∈ t₁.abelian₂ := by
      rw [hzsum]; exact hz
    have hglA : GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ'
        ⟨_, hmS⟩ ⟨p, hpS⟩ :=
      ⟨n₁, q, hcorr₁, hz', by show p + q ∈ A; rw [hxpq]; exact hx⟩
    obtain ⟨n₁', n₂', hc', h1', h2'⟩ := hAB _ _ hglA
    obtain ⟨hn₁'W, hψ'⟩ := (hψ _ _).mp hc'
    have h1'' : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + n₁' ∈ t₁.abelian₂ := h1'
    have hd : n₁' - (n₁ : V) ∈ t₁.abelian₂ := by
      have h0 := t₁.abelian₂.sub_mem h1'' hz'
      rwa [add_sub_add_left_eq_sub] at h0
    have hdW : n₁' - (n₁ : V) ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁'W n₁.2
    have hψd : (ψ ⟨n₁' - n₁, hdW⟩ : V) = n₂' - q := by
      have e : (⟨n₁' - n₁, hdW⟩ : ↥(H.W0 t₁.f t₁.f')) = ⟨n₁', hn₁'W⟩ - n₁ := rfl
      rw [e, map_sub, Submodule.coe_sub, hψ', hψn₁]
    have hcd : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ'
        (n₁' - n₁) (n₂' - q) := (hψ _ _).mpr ⟨hdW, hψd⟩
    have hB : n₂' - q ∈ B := (hThB _ _ hcd).mp hd
    have h2'' : p + n₂' ∈ B := h2'
    have h0 := B.sub_mem h2'' hB
    have e : p + n₂' - (n₂' - q) = x := by rw [← hxpq]; abel
    rwa [e] at h0
  exact le_antisymm (key Λ₂ Λ₂' hG hTh hTh' (fun m₁ m₂ => (hrel m₁ m₂).mp))
    (key Λ₂' Λ₂ hG' hTh' hTh (fun m₁ m₂ => (hrel m₁ m₂).mpr))

end Inj

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CorrLemmas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

private theorem h_finset_sum_smul_left {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simpa using H.h_smul_left 0 0 y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

private theorem h_add_right_rank_point_counts (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

private theorem h_smul_right_eq_cj_mul (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

private theorem h_zero_right_rank_point_counts (x : V) : H.h x 0 = 0 := by
  simpa using h_add_right_rank_point_counts H x 0 0

theorem mem_perpX_of {f : Fin (r + 1) → V} {v : V} (h : ∀ j : Fin r, H.h v (f j.castSucc) = 0) :
    v ∈ H.perp (H.X f) := by
  show ∀ x ∈ H.X f, H.h v x = 0
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact h j
  | zero => exact h_zero_right_rank_point_counts H v
  | add y z _ _ hy hz => rw [h_add_right_rank_point_counts, hy, hz, add_zero]
  | smul a y _ hy => rw [h_smul_right_eq_cj_mul, hy, mul_zero]

theorem z_mem_perpX {f : Fin (r + 1) → V} {T : F} (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) :
    f (Fin.last r) ∈ H.perp (H.X f) :=
  mem_perpX_of H fun j => hF.1 _ _ (Or.inr (Fin.castSucc_lt_last j).ne)

theorem om'_mem_perpX (f f' : Fin (r + 1) → V) : H.om' f f' ∈ H.perp (H.X f) := by
  refine mem_perpX_of H fun j => ?_
  unfold HermSp.om'
  rw [h_sum_smul_left]
  have e := congrFun (congrFun (mul_adjugate (H.Zhat f f')) j.castSucc) (Fin.last r)
  rw [Matrix.smul_apply, one_apply_ne (Fin.castSucc_lt_last j).ne, smul_zero, mul_apply] at e
  rw [← e]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [HermSp.Zhat, Matrix.of_apply]
  ring

theorem om'_mem_U (f f' : Fin (r + 1) → V) :
    H.om' f f' ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
  unfold HermSp.om'
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)

theorem decomp_U_perpX {f f' : Fin (r + 1) → V} {T : F} (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hZ : IsUnit (H.Zhat f f').det) {u : V} (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f')))
    (hp : u ∈ H.perp (H.X f)) :
    ∃ x ∈ H.X f, ∃ β γ : E, u = x + β • f (Fin.last r) + γ • H.om' f f' := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hu
  obtain ⟨a, p, rfl⟩ : ∃ a p, c = Sum.elim a p := ⟨c ∘ Sum.inl, c ∘ Sum.inr, by ext (i | i) <;> rfl⟩
  have hp' : ∀ x ∈ H.X f, H.h (∑ i, Sum.elim a p i • Sum.elim f f' i) x = 0 := hp
  rw [Fintype.sum_sum_type] at hp' ⊢
  simp only [Sum.elim_inl, Sum.elim_inr] at hp' ⊢
  obtain ⟨d, hd⟩ := hZ
  have hperp : ∀ j : Fin r, (H.Zhat f f' *ᵥ p) j.castSucc = 0 := by
    intro j
    have h0 := hp' (f j.castSucc) (Submodule.subset_span ⟨j, rfl⟩)
    rw [H.h_add_left, h_finset_sum_smul_left, h_finset_sum_smul_left,
      Finset.sum_eq_zero (fun i _ => by rw [hF.1 _ _ (Or.inr (Fin.castSucc_lt_last j).ne), mul_zero]),
      zero_add] at h0
    refine Eq.trans ?_ h0
    simp only [Matrix.mulVec, dotProduct, HermSp.Zhat, Matrix.of_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hZp : H.Zhat f f' *ᵥ p = Pi.single (Fin.last r) ((H.Zhat f f' *ᵥ p) (Fin.last r)) := by
    funext k
    by_cases hk : k = Fin.last r
    · subst hk
      simp
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hk
      rw [hperp j, Pi.single_eq_of_ne hk]
  have hp2 : ∀ b, p b = (↑d⁻¹ * (H.Zhat f f' *ᵥ p) (Fin.last r)) * (H.Zhat f f').adjugate b (Fin.last r) := by
    intro b
    have h1 : (H.Zhat f f').adjugate *ᵥ (H.Zhat f f' *ᵥ p) = (H.Zhat f f').det • p := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 := congrFun h1 b
    rw [hZp] at h2
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul] at h2
    rw [← hd] at h2
    calc p b = ↑d⁻¹ * (↑d * p b) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by
        rw [← h2]
        simp only [Matrix.mulVec, dotProduct]
        ring
  refine ⟨∑ j : Fin r, a j.castSucc • f j.castSucc, ?_, a (Fin.last r),
    ↑d⁻¹ * (H.Zhat f f' *ᵥ p) (Fin.last r), ?_⟩
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Fin.sum_univ_castSucc (fun i => a i • f i)]
    congr 1
    unfold HermSp.om'
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul, ← hp2 b]

theorem Gdet_rel (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (h : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.Gdet f₂ f₂' T T' * H.normE (H.Dl f₁ f₁' (r + 1)) =
      H.normE (H.Dl f₂ f₂' (r + 1)) * H.Gdet f₁ f₁' T T' := by
  unfold HermSp.Gdet HermSp.normE
  have h' : M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1)) =
      M.L.cj (H.Dl f₂ f₂' r) * M.L.cj (H.Dl f₁ f₁' (r + 1)) := by
    rw [← map_mul, ← map_mul, h]
  linear_combination (algebraMap F E (T * T')) * (M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1))) * h +
    (algebraMap F E (T * T')) * (H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) * h'

end CorrLemmas

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CorrProof

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem Dl_succ {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dif_pos le_rfl]
  congr 1

theorem mkW_eq_of_sub_mem {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))} (h : (x : V) - y ∈ H.X f) : H.mkW f x = H.mkW f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using h

theorem corrIso_holds (M : Model F E) (r n : ℕ) : CorrIso M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂
  obtain ⟨hg₁, hF₂, hF₂', hI, hz, hz'⟩ := hyp
  have hT1 := hg₁.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT1.2.1.2.1, hT1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT1.2.2.1.2.1, hT1.2.2.1.2.2.1⟩
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  obtain ⟨hIs, -, hW0c, hom', -, hκ⟩ := hI
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hκ
    have hN₁ : IsUnit (H.normE (H.Dl t₁.f t₁.f' (r + 1))) := hD₁.mul (hD₁.map M.L.cj)
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  have hU₁ := isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ hG₁
  have hU₂ := isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂ hG₂
  have hXU : ∀ g g' : Fin (r + 1) → V, H.X g ≤ Submodule.span E (Set.range (Sum.elim g g')) :=
    fun g g' => Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Sum.inl j.castSucc, rfl⟩)
  have huniq : ∀ (a b : V) (ha : a ∈ H.W0 f₂ f₂') (hb : b ∈ H.W0 f₂ f₂'),
      H.mkW f₂ ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H ha⟩ = H.mkW f₂ ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩ → a = b := by
    intro a b ha hb hab
    have h1 := sub_mem_X_of_mkW_eq H hab
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hU₂.disjoint) _ (hXU f₂ f₂' h1) (Submodule.sub_mem _ ha hb))
  have hex : ∀ w : ↥(H.W0 t₁.f t₁.f'), ∃ w₂ : ↥(H.W0 f₂ f₂'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ ∧
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW f₂' ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H w₂.2⟩ := by
    intro w
    obtain ⟨w₂, hw₂, s1, s2⟩ := hW0c w w.2
    refine ⟨⟨w₂, hw₂⟩, ?_, ?_⟩
    · have := s1 ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H hw₂⟩ rfl rfl
      simpa using this
    · have := s2 ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H hw₂⟩ rfl rfl
      simpa using this
  choose ψf hψf using hex
  have hψadd : ∀ a b, ψf (a + b) = ψf a + ψf b := by
    intro a b
    apply Subtype.ext
    apply huniq _ _ (ψf (a + b)).2 (ψf a + ψf b).2
    rw [← (hψf (a + b)).1]
    have e : (⟨((a + b : ↥(H.W0 t₁.f t₁.f')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (a + b).2⟩ : ↥(H.perp (H.X t₁.f))) =
        ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ + ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ := Subtype.ext rfl
    have e2 : (⟨((ψf a + ψf b : ↥(H.W0 f₂ f₂')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (ψf a + ψf b).2⟩ : ↥(H.perp (H.X f₂))) =
        ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩ + ⟨ψf b, mem_perp_isotropicSpan_of_mem_framePerp H (ψf b).2⟩ := Subtype.ext rfl
    rw [e, e2, map_add, map_add, map_add, (hψf a).1, (hψf b).1]
  have hψsmul : ∀ (c : E) a, ψf (c • a) = c • ψf a := by
    intro c a
    apply Subtype.ext
    apply huniq _ _ (ψf (c • a)).2 (c • ψf a).2
    rw [← (hψf (c • a)).1]
    have e : (⟨((c • a : ↥(H.W0 t₁.f t₁.f')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (c • a).2⟩ : ↥(H.perp (H.X t₁.f))) =
        c • ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ := Subtype.ext rfl
    have e2 : (⟨((c • ψf a : ↥(H.W0 f₂ f₂')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (c • ψf a).2⟩ : ↥(H.perp (H.X f₂))) =
        c • ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩ := Subtype.ext rfl
    rw [e, e2, map_smul, map_smul, map_smul, (hψf a).1]
  let ψL : ↥(H.W0 t₁.f t₁.f') →ₗ[E] ↥(H.W0 f₂ f₂') :=
    { toFun := ψf, map_add' := hψadd, map_smul' := hψsmul }
  have hinj : Function.Injective ψL := by
    intro a b hab
    have hab' : ψf a = ψf b := hab
    have e : H.mkW t₁.f ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ = H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ :=
      φ.injective (by rw [(hψf a).1, (hψf b).1, hab'])
    have h1 := sub_mem_X_of_mkW_eq H e
    exact Subtype.ext (sub_eq_zero.1 ((Submodule.disjoint_def.1 hU₁.disjoint) _ (hXU t₁.f t₁.f' h1)
      (Submodule.sub_mem _ a.2 b.2)))
  have hsurj : Function.Surjective ψL := by
    intro w₂
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ.symm (H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩))
    have hy' : φ (H.mkW t₁.f y) = H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ := by
      have : H.mkW t₁.f y = φ.symm (H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩) := hy
      rw [this, LinearEquiv.apply_symm_apply]
    have hyU : (y : V) ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')) ⊔ H.W0 t₁.f t₁.f' := by
      rw [hU₁.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hyU
    have hup : u ∈ H.perp (H.X t₁.f) := by
      have : u = (y : V) - w := by rw [← huw]; abel
      rw [this]
      exact Submodule.sub_mem _ y.2 (mem_perp_isotropicSpan_of_mem_framePerp H hw)
    have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
    obtain ⟨x, hx, β, γ, hxe⟩ := decomp_U_perpX H hF₁ hZ₁ hu hup
    refine ⟨⟨w, hw⟩, ?_⟩
    set D₂ := H.Dl f₂ f₂' (r + 1)
    set D₁ := H.Dl t₁.f t₁.f' (r + 1)
    let zP₁ : ↥(H.perp (H.X t₁.f)) := ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩
    let oP₁ : ↥(H.perp (H.X t₁.f)) := ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩
    let zP₂ : ↥(H.perp (H.X f₂)) := ⟨f₂ (Fin.last r), z_mem_perpX H hF₂⟩
    let oP₂ : ↥(H.perp (H.X f₂)) := ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩
    let wP : ↥(H.perp (H.X t₁.f)) := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩
    let vP : ↥(H.perp (H.X f₂)) := ⟨ψf ⟨w, hw⟩, mem_perp_isotropicSpan_of_mem_framePerp H (ψf ⟨w, hw⟩).2⟩
    have hq₁ : H.mkW t₁.f y = H.mkW t₁.f (β • zP₁ + γ • oP₁ + wP) := by
      apply mkW_eq_of_sub_mem
      show (y : V) - (β • t₁.f (Fin.last r) + γ • H.om' t₁.f t₁.f' + w) ∈ H.X t₁.f
      rw [← huw, hxe]
      convert hx using 1
      abel
    have hz1 : φ (H.mkW t₁.f zP₁) = H.mkW f₂ zP₂ := by
      have := hz zP₁ zP₂ rfl rfl
      simpa using this
    have ho0 : D₂ • φ (H.mkW t₁.f oP₁) = D₁ • H.mkW f₂ oP₂ := by
      have := hom' oP₁ oP₂ rfl rfl
      simpa using this
    have ho1 : φ (H.mkW t₁.f oP₁) = (Ring.inverse D₂ * D₁) • H.mkW f₂ oP₂ := by
      rw [mul_smul, ← ho0, smul_smul, Ring.inverse_mul_cancel _ hD₂, one_smul]
    have hw1 : φ (H.mkW t₁.f wP) = H.mkW f₂ vP := (hψf ⟨w, hw⟩).1
    have hq₂ : H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ =
        H.mkW f₂ (β • zP₂ + (γ * (Ring.inverse D₂ * D₁)) • oP₂ + vP) := by
      rw [← hy', hq₁]
      simp only [map_add, map_smul, hz1, ho1, hw1, smul_smul]
    have hd := sub_mem_X_of_mkW_eq H hq₂
    have hU2mem : (w₂ : V) - (ψf ⟨w, hw⟩ : V) ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')) := by
      have e : (w₂ : V) - (ψf ⟨w, hw⟩ : V) =
          ((w₂ : V) - ((β • zP₂ + (γ * (Ring.inverse D₂ * D₁)) • oP₂ + vP : ↥(H.perp (H.X f₂))) : V)) +
            (β • f₂ (Fin.last r) + (γ * (Ring.inverse D₂ * D₁)) • H.om' f₂ f₂') := by
        simp only [Submodule.coe_add, Submodule.coe_smul, zP₂, oP₂, vP]
        abel
      rw [e]
      exact Submodule.add_mem _ (hXU f₂ f₂' hd) (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
        (Submodule.smul_mem _ _ (om'_mem_U H f₂ f₂')))
    have h0 := (Submodule.disjoint_def.1 hU₂.disjoint) _ hU2mem (Submodule.sub_mem _ w₂.2 (ψf ⟨w, hw⟩).2)
    exact Subtype.ext (sub_eq_zero.1 h0).symm
  refine ⟨LinearEquiv.ofBijective ψL ⟨hinj, hsurj⟩, fun a b => ?_, fun n₁ n₂ => ?_⟩
  · show H.h ((ψf a : ↥(H.W0 f₂ f₂')) : V) ((ψf b : ↥(H.W0 f₂ f₂')) : V) = H.h a b
    exact hIs ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩
      ⟨ψf b, mem_perp_isotropicSpan_of_mem_framePerp H (ψf b).2⟩ (hψf a).1 (hψf b).1
  · constructor
    · rintro ⟨h₁, h₂, c1, -⟩
      refine ⟨h₁, ?_⟩
      show ((ψf ⟨n₁, h₁⟩ : ↥(H.W0 f₂ f₂')) : V) = n₂
      exact huniq _ _ (ψf ⟨n₁, h₁⟩).2 h₂ ((hψf ⟨n₁, h₁⟩).1.symm.trans c1)
    · rintro ⟨h₁, rfl⟩
      exact ⟨h₁, (ψf ⟨n₁, h₁⟩).2, (hψf ⟨n₁, h₁⟩).1, (hψf ⟨n₁, h₁⟩).2⟩

end CorrProof

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem glue_at (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) : Glue M r n :=
  glue_of M r n (glueFwd_of M r n hM (corrIso_holds M r n) hE)
    (glueBack_of M r n hM (corrIso_holds M r n) hE hV hP hG hFG hS) (glueInj_of M r n hM (corrIso_holds M r n))

theorem latSide_at (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) (hR : ClaimR M r n) :
    LatSide M r n :=
  latSide_of M r n (glue_at M r n hM hE hV hP hG hFG hS) hR

end Top

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Tools

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

private theorem hermSp_h_sum_smul_left {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {ι : Type} [Fintype ι] (c : ι → E) (x : ι → V) (y : V) : H.h (∑ i, c i • x i) y = ∑ i, c i * H.h (x i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)
  have h1 := map_sum φ (fun i => c i • x i) Finset.univ
  simp only [φ, AddMonoidHom.mk'_apply, H.h_smul_left] at h1
  exact h1

private theorem hermSp_h_sum_smul_right {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {ι : Type} [Fintype ι] (y : V) (c : ι → E) (x : ι → V) :
    H.h y (∑ i, c i • x i) = ∑ i, M.L.cj (c i) * H.h y (x i) := by
  rw [H.h_herm (∑ i, c i • x i) y, hermSp_h_sum_smul_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm]

theorem gram_recomb {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type}
    [Fintype ι] (v : ι → V) (A : Matrix ι ι E) :
    H.gram (fun j => ∑ i, A i j • v i) = (A.map M.L.cj)ᵀ * H.gram v * A := by
  ext a b
  simp only [HermSp.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hermSp_h_sum_smul_left]
  simp only [hermSp_h_sum_smul_right, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem thSpan_at (M : Model F E) (r : ℕ) (hM : M.OK) : ThSpan M r := by
  intro V _ _ H t hg
  apply le_antisymm
  · exact (Submodule.span_le (R := E)).2 fun v hv => hv.2
  · intro w hw
    have hwΛ : w ∈ Submodule.span E (t.abelian₂ : Set V) := by
      rw [hg.1.1.2.1]
      exact Submodule.mem_top
    obtain ⟨c, hc0, hc⟩ := PI.LocHerm.Glue.existsIntegralMultiple M hM V t.abelian₂ w hwΛ
    have hcW : algebraMap F E (c : F) • w ∈ ThL H t := ⟨hc, Submodule.smul_mem _ _ hw⟩
    have hunit : IsUnit (algebraMap F E (c : F)) := (Units.mk0 (c : F) hc0).isUnit.map _
    have e : w = (hunit.unit⁻¹ : Eˣ) • (algebraMap F E (c : F) • w) := by
      rw [Units.smul_def, smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [e, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hcW)

theorem gramMM_holds (M : Model F E) (r n : ℕ) : GramMM M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂
  obtain ⟨hg₁, hF₂, hF₂', hI, -, -⟩ := hyp
  have hT1 := hg₁.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hI.2.2.2.2.2
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  obtain ⟨s, hs, hdet⟩ := gram_det H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂
  have hgu : IsUnit (H.gram (Sum.elim f₂ f₂')).det := by
    have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
    have : (H.gram (Sum.elim f₂ f₂')).det = H.Gdet f₂ f₂' t₁.T t₁.T' * s := by
      rw [← hdet, mul_assoc, hs, mul_one]
    rw [this]
    exact hG₂.mul hsu
  rcases hsplit : M.split with _ | g
  · have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ f₂' := by
      unfold HermSp.MMfam
      rw [hsplit]
    rw [hMM]
    exact hgu
  · set qi : E := algebraMap F E ((g.q : F)⁻¹)
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
    have hqi : IsUnit qi := ((Units.mk0 (g.q : F) hq0)⁻¹.isUnit).map (algebraMap F E)
    have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =
        Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) := by
      unfold HermSp.MMfam
      rw [hsplit]
    let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      fromBlocks 1 (-(qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) 0 (qi • 1)
    have hw : Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) = fun j => ∑ i, A i j • Sum.elim f₂ f₂' i := by
      funext j
      rcases j with a | a
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply, smul_sub, sub_eq_add_neg, add_comm]
    rw [hMM, hw, gram_recomb, det_mul, det_mul, det_transpose]
    have hA : A.det = qi ^ (r + 1) := by
      simp [A, det_fromBlocks_zero₂₁, det_smul]
    have hAm : (A.map M.L.cj).det = M.L.cj A.det := by
      rw [show A.map M.L.cj = (M.L.cj.toRingEquiv.toRingHom).mapMatrix A from rfl, ← RingHom.map_det]
      rfl
    rw [hAm, hA]
    exact ((hqi.pow _).map M.L.cj).mul hgu |>.mul (hqi.pow _)

end Tools

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section FG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

private theorem isNoetherianRing_locE_O' (L : LocE F E) [IsNonarchimedeanLocalField F] [CharZero F] :
    IsNoetherianRing L.O := by
  classical
  haveI : IsReduced E := L.reduced
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ L.rank
  have hA : ∀ a : 𝒪[F], algebraMap 𝒪[F] E a = algebraMap F E (a : F) := fun a =>
    IsScalarTower.algebraMap_apply 𝒪[F] F E a
  have hcjA : ∀ (a : F) (w : E), L.cj (algebraMap F E a * w) = algebraMap F E a * L.cj w := by
    intro a w
    rw [map_mul, L.cj.commutes]
  have hcjO : ∀ x ∈ L.O, L.cj x ∈ L.O := by
    intro x hx
    rw [L.O_def] at hx ⊢
    exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
  have htr : ∀ z ∈ L.O, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = z + L.cj z := by
    intro z hz
    have hmem : z + L.cj z ∈ L.O := L.O.add_mem hz (hcjO z hz)
    obtain ⟨a, ha⟩ := (L.cj_fix (z + L.cj z)).1 (by rw [map_add, L.cj_cj, add_comm])
    have hint : IsIntegral 𝒪[F] (algebraMap F E a) := ha ▸ (L.O_def _).1 hmem
    have hint' : IsIntegral 𝒪[F] a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] F E) (algebraMap F E).injective).1 hint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
    exact ⟨y, by rw [hA, ← ha, ← hy]; rfl⟩
  have hnd : ∀ x : E, (∀ y : E, x * y + L.cj (x * y) = 0) → x = 0 := by
    intro x hx
    have h1 : L.cj x = -x := by
      have h := hx 1
      rw [mul_one] at h
      exact eq_neg_of_add_eq_zero_right h
    have h2 := hx x
    rw [map_mul, h1, neg_mul_neg, ← two_mul] at h2
    have hu : IsUnit (2 : E) := by
      have h3 : (2 : E) = algebraMap F E 2 := (map_ofNat (algebraMap F E) 2).symm
      rw [h3]
      exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
    have hxx : x * x = 0 := hu.mul_right_eq_zero.1 h2
    exact IsReduced.eq_zero x ⟨2, by rw [pow_two, hxx]⟩
  let b := Module.finBasisOfFinrankEq F E L.rank
  have hsc : ∀ i, ∃ c : F, c ≠ 0 ∧ algebraMap F E c * b i ∈ L.O := by
    intro i
    haveI : Algebra.IsAlgebraic 𝒪[F] F := IsLocalization.isAlgebraic F (nonZeroDivisors 𝒪[F])
    haveI : Algebra.IsAlgebraic 𝒪[F] E := Algebra.IsAlgebraic.trans 𝒪[F] F E
    obtain ⟨c, hc, hci⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := 𝒪[F]) (b i)).exists_integral_multiple
    refine ⟨(c : F), by exact_mod_cast hc, (L.O_def _).2 ?_⟩
    rwa [Algebra.smul_def, hA] at hci
  choose c hc0 hcO using hsc
  let φ : 𝒪[F] →+* L.O :=
    (algebraMap 𝒪[F] E).codRestrict L.O (fun a => (L.O_def _).2 isIntegral_algebraMap)
  letI : Algebra 𝒪[F] L.O := φ.toAlgebra
  have hsm : ∀ (a : 𝒪[F]) (x : L.O), ((a • x : L.O) : E) = algebraMap F E (a : F) * x := by
    intro a x
    rw [Algebra.smul_def, Subring.coe_mul, ← hA]
    rfl
  let B : Fin 2 → E := fun i => algebraMap F E (c i) * b i
  let g : L.O →ₗ[𝒪[F]] (Fin 2 → E) :=
    { toFun := fun x i => (x : E) * B i + L.cj ((x : E) * B i)
      map_add' := by
        intro x y
        funext i
        simp only [Subring.coe_add, add_mul, map_add, Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [hsm, Algebra.smul_def, hA]
        simp only [mul_assoc, hcjA, mul_add] }
  let N : Submodule 𝒪[F] (Fin 2 → E) :=
    Submodule.span 𝒪[F] (Set.range fun i : Fin 2 => Pi.single i (1 : E))
  haveI : IsNoetherian 𝒪[F] N := isNoetherian_span_of_finite 𝒪[F] (Set.finite_range _)
  have hgN : ∀ x, g x ∈ N := by
    intro x
    have hx : ∀ i, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = (x : E) * B i + L.cj ((x : E) * B i) :=
      fun i => htr _ (L.O.mul_mem x.2 (hcO i))
    choose a ha using hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    show _ = fun j => (x : E) * B j + L.cj ((x : E) * B j)
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
  have hinj : Function.Injective (g.codRestrict N hgN) := by
    intro x y hxy
    have h0 : g x = g y := congrArg Subtype.val hxy
    have hd : ∀ i, ((x : E) - y) * B i + L.cj (((x : E) - y) * B i) = 0 := by
      intro i
      have h := congrFun h0 i
      simp only [g, LinearMap.coe_mk, AddHom.coe_mk] at h
      rw [sub_mul, map_sub]
      linear_combination h
    have hb : ∀ i, ((x : E) - y) * b i + L.cj (((x : E) - y) * b i) = 0 := by
      intro i
      have h := hd i
      simp only [B] at h
      rw [mul_left_comm, hcjA, ← mul_add] at h
      exact ((IsUnit.mk0 _ (hc0 i)).map (algebraMap F E)).mul_right_eq_zero.1 h
    have hall : ∀ w, ((x : E) - y) * w + L.cj (((x : E) - y) * w) = 0 := by
      intro w
      let τ : E →ₗ[F] E := LinearMap.mulLeft F ((x : E) - y) +
        (L.cj.toLinearMap).comp (LinearMap.mulLeft F ((x : E) - y))
      have hτ : τ = 0 := b.ext (fun i => by simpa [τ] using hb i)
      simpa [τ] using LinearMap.congr_fun hτ w
    exact Subtype.ext (sub_eq_zero.1 (hnd _ hall))
  haveI : IsNoetherian 𝒪[F] L.O := isNoetherian_of_injective (g.codRestrict N hgN) hinj
  exact isNoetherianRing_iff.2 (isNoetherian_of_tower 𝒪[F] this)

theorem thFG_at (M : Model F E) (r : ℕ) (hM : M.OK) : ThFG M r := by
  intro V _ _ H t ht
  haveI := hM.loc
  haveI := hM.char0
  haveI : IsNoetherianRing M.L.O := isNoetherianRing_locE_O' M.L
  have hfg : t.abelian₂.FG := ht.1.1.1
  haveI : IsNoetherian M.L.O t.abelian₂ := isNoetherian_of_fg_of_noetherian _ hfg
  have hle : ThL H t ≤ t.abelian₂ := inf_le_left
  haveI := isNoetherian_of_le hle
  exact Module.Finite.iff_fg.1 inferInstance

end FG

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Top2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem latSide_at' (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hR : ClaimR M r n) : LatSide M r n :=
  latSide_at M r n hM hE hV hP (gramMM_holds M r n) (thFG_at M r hM) (thSpan_at M r hM) hR

theorem localCount_of_glue (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hR : ClaimR M r n) (h0 : ModSide0 M r n M.split.isSome)
    (hU : ModSideU M r n M.split.isSome) : Formalism.MainNotions.ThinScalesBound.FamilyLocalModel M r n := by
  intro V _ _ H hn t₁ hg f₂ f₂' φ φ' hF hF' hI hs hs'
  have hT : LocalCountHypotheses H t₁ f₂ f₂' φ φ' := ⟨hg, hF, hF', hI, hs, hs'⟩
  have hL := latSide_at' M r n hM hE hV hP hR V H hn t₁ f₂ f₂' φ φ' hT
  dsimp only
  refine ⟨fun hz Z₁ Z₂ h₁ h₂ => ?_, fun hu Y₁ Y₂ be₁ be₂ al₁ al₂ hY hb => ?_⟩
  · rw [hL]
    exact h0 rfl V H hn t₁ f₂ f₂' φ φ' hT hz Z₁ Z₂ h₁ h₂
  · rw [hL]
    exact hU rfl V H hn t₁ f₂ f₂' φ φ' hT hu Y₁ Y₂ be₁ be₂ al₁ al₂ hY hb

end Top2

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section GP

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem prim_comp {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {Λ : Submodule M.L.O V} {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] {v : ι → V} (hv : H.Prim Λ v)
    (e : κ → ι) (he : Function.Injective e) : H.Prim Λ (v ∘ e) := by
  refine ⟨fun a => hv.1 (e a), hv.2.1.comp e he, fun x hx hxs => ?_⟩
  have hxv : x ∈ Submodule.span E (Set.range v) := Submodule.span_mono (Set.range_comp_subset_range e v) hxs
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hv.2.2 x hx hxv)
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
  have ha' : ∑ i, ((a i : M.L.O) : E) • v i = x := ha
  let d' : ι → E := fun i => ∑ j, if e j = i then d j else 0
  have hd' : ∑ i, d' i • v i = ∑ j, d j • v (e j) := by
    simp only [d', Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_ite_eq]
    simp
  have hcoef : ∀ i, ((a i : M.L.O) : E) = d' i := by
    have h0 : ∑ i, (((a i : M.L.O) : E) - d' i) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [hd', ha']
      simpa using hd.symm ▸ sub_self x
    intro i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv.2.1 _ h0 i)
  have hzero : ∀ i, i ∉ Set.range e → a i = 0 := by
    intro i hi
    apply Subtype.ext
    rw [hcoef i]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (fun h => hi ⟨j, h⟩)]
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => a (e j), ?_⟩
  rw [← ha]
  exact (Fintype.sum_of_injective e he (fun j => a (e j) • (v ∘ e) j) (fun i => a i • v i)
    (fun i hi => by rw [hzero i hi, zero_smul]) (fun j => rfl))

theorem genOfPrim_holds (M : Model F E) (r n : ℕ) : GenOfPrim M r n := by
  intro _ V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂ Λ₂ hsd hprim
  obtain ⟨hg₁, hF₂, hF₂', hI, -, -⟩ := hyp
  have hT1 := hg₁.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hI.2.2.2.2.2
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  have hnt : Nontrivial E := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    have h0 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    rw [M.L.rank] at h0
    exact absurd h0 (by norm_num)
  have hfam_inl : (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r)) ∘ Sum.inl = f₂ := by
    funext a
    unfold HermSp.MMfam
    rcases M.split with _ | g <;> rfl
  have hPf : H.Prim Λ₂ f₂ := by
    have := prim_comp H hprim Sum.inl Sum.inl_injective
    rwa [hfam_inl] at this
  have hPf' : H.Prim Λ₂ f₂' := by
    rcases hs : M.split with _ | g
    · have hfam_inr : (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r)) ∘ Sum.inr = f₂' := by
        funext a
        unfold HermSp.MMfam
        rw [hs]
        rfl
      have := prim_comp H hprim Sum.inr Sum.inr_injective
      rwa [hfam_inr] at this
    · set Q : E := algebraMap F E (g.q : F)
      set qi : E := algebraMap F E ((g.q : F)⁻¹)
      have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
      have hQqi : Q * qi = 1 := by
        simp only [Q, qi]
        rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
      have hQO : Q ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L g.q
      have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) := by
        unfold HermSp.MMfam
        rw [hs]
      rw [hMM] at hprim
      obtain ⟨hmem, hli, hsat⟩ := hprim
      set y : Fin (r + 1) → V := fun a => qi • (f₂' a - f₂ a)
      have hf' : ∀ a, f₂' a = f₂ a + Q • y a := by
        intro a
        simp only [y]
        rw [smul_smul, hQqi, one_smul]
        abel
      refine ⟨fun a => ?_, ?_, fun x hx hxs => ?_⟩
      · rw [hf' a]
        refine Submodule.add_mem _ (hmem (Sum.inl a)) ?_
        have := Λ₂.smul_mem (⟨Q, hQO⟩ : M.L.O) (hmem (Sum.inr a))
        rwa [Subring.smul_def] at this
      · rw [Fintype.linearIndependent_iff]
        intro d hd a
        have h0 : ∑ i, (Sum.elim d (fun b => d b * Q) i) • Sum.elim f₂ y i = 0 := by
          rw [Fintype.sum_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr]
          rw [← hd, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hf' b, smul_add, mul_smul]
        exact (Fintype.linearIndependent_iff.1 hli) _ h0 (Sum.inl a)
      · obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
        have hx2 : ∑ a, d a • f₂' a ∈ Submodule.span E (Set.range (Sum.elim f₂ y)) := by
          refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
          rw [hf' a]
          exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr a, rfl⟩))
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hsat _ hx hx2)
        have hcoef := (Fintype.linearIndependent_iff.1 hli)
          (fun i => (c i : E) - Sum.elim d (fun b => d b * Q) i) (by
            simp only [sub_smul, Finset.sum_sub_distrib]
            have e1 : ∑ i, (c i : E) • Sum.elim f₂ y i = ∑ a, d a • f₂' a := by
              rw [← hc]
              exact Finset.sum_congr rfl fun i _ => (Subring.smul_def _ _).symm
            rw [e1, Fintype.sum_sum_type]
            simp only [Sum.elim_inl, Sum.elim_inr]
            rw [← Finset.sum_add_distrib, sub_eq_zero]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [hf' b, smul_add, mul_smul])
        have hdO : ∀ a, d a ∈ M.L.O := by
          intro a
          have := hcoef (Sum.inl a)
          simp only [Sum.elim_inl] at this
          rw [← sub_eq_zero.1 this]
          exact (c _).2
        refine Submodule.sum_mem _ fun a _ => ?_
        have := Submodule.smul_mem (Submodule.span M.L.O (Set.range f₂')) (⟨d a, hdO a⟩ : M.L.O)
          (Submodule.subset_span ⟨a, rfl⟩)
        rwa [Subring.smul_def] at this
  refine ⟨⟨hsd, ⟨hPf, hF₂.1, hF₂.2, hT1.2.1.2.2.2⟩, ⟨hPf', hF₂'.1, hF₂'.2, hT1.2.2.1.2.2.2⟩, hD₂, hG₂.ne_zero,
    fun g hs => ⟨(hT1.2.2.2.2.2 g hs).1, (hT1.2.2.2.2.2 g hs).2.1, fun b => ?_⟩⟩, hprim⟩
  have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
  have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =
      Sum.elim f₂ (fun a => algebraMap F E ((g.q : F)⁻¹) • (f₂' a - f₂ a)) := by
    unfold HermSp.MMfam
    rw [hs]
  have hy : algebraMap F E ((g.q : F)⁻¹) • (f₂' b - f₂ b) ∈ Λ₂ := by
    have := hprim.1 (Sum.inr b)
    rw [hMM] at this
    exact this
  have e : f₂' b - f₂ b = algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (f₂' b - f₂ b)) := by
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_smul]
  show f₂' b - f₂ b ∈ H.smulLat (algebraMap F E (g.q : F)) Λ₂
  rw [e]
  exact Submodule.subset_span ⟨_, hy, rfl⟩

end GP

end Formalism.L2.SG.LsDatumA
end
end
