import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.ThinScalesBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section G

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem exists_of_mem_smulLat {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {c : E} {abelian₂ : Submodule M.L.O V} {x : V} (hx : x ∈ H.smulLat c abelian₂) : ∃ l ∈ abelian₂, x = c • l := by
  unfold Formalism.MainNotions.S.Loc.HermSp.smulLat at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨l, hl, rfl⟩
  | zero => exact ⟨0, abelian₂.zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨m, hm, rfl⟩ := hz
    exact ⟨l + m, abelian₂.add_mem hl hm, by simp [smul_add]⟩
  | smul a y _ hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨a • l, abelian₂.smul_mem a hl, smul_comm a c l⟩

def Lemma0G (M : Model F E) (r : ℕ) : Prop :=
  ∀ g : SplitG M.L, M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    H.IsGeneric t → ∀ (w : V) (hw : w ∈ H.W0 t.f t.f'),
      (w ∈ t.abelian₂ ↔ (H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩ ∈ H.Lset t.abelian₂ t.f ∧
        H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩ ∈ H.Lset t.abelian₂ t.f' ∧
        (H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩) ∈ H.iotaGraph g t))

theorem lemma0G_holds (M : Model F E) (r : ℕ) : Lemma0G M r := by
  intro g hg V _ _ H t hgen w hw
  constructor
  · intro hwL
    refine ⟨⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, rfl⟩, ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, hwL, rfl⟩, ?_⟩
    refine ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, hwL, ?_, rfl⟩
    simp only [sub_self]
    exact Submodule.zero_mem _
  · rintro ⟨-, -, x', x, hx'L, hxL, hxx, hp⟩
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [HermSp.mkW, Submodule.mkQ_apply] at hp1 hp2

    have ha' : w - (x' : V) ∈ H.X t.f' := by
      simpa [Submodule.mem_comap] using (Submodule.Quotient.eq _).1 hp1
    have ha : w - (x : V) ∈ H.X t.f := by
      simpa [Submodule.mem_comap] using (Submodule.Quotient.eq _).1 hp2
    obtain ⟨α', hα'⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ha'
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ha
    obtain ⟨l, hl, hxl⟩ := exists_of_mem_smulLat H hxx
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (by exact_mod_cast h0)
    have hqqi : algebraMap F E (g.q : F) * algebraMap F E ((g.q : F)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
    have hqiq : algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F) = 1 := by
      rw [mul_comm, hqqi]
    have hMM : H.MMfam t =
        Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
      simp only [HermSp.MMfam, hg]
    obtain ⟨-, hli, hprim⟩ := hgen.2
    rw [hMM] at hli hprim

    let γ : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim
      (Fin.snoc (fun i => algebraMap F E ((g.q : F)⁻¹) * (α' i - α i)) 0) (Fin.snoc α' 0)
    have hsum : ∑ j, γ j • Sum.elim t.f
        (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j = l := by
      have key : algebraMap F E (g.q : F) • ∑ j, γ j • Sum.elim t.f
          (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j =
          algebraMap F E (g.q : F) • l := by
        rw [← hxl, Fintype.sum_sum_type]
        simp only [γ, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, zero_smul, add_zero, smul_add, Finset.smul_sum]
        have e1 : (x : V) - x' = (w - x') - (w - x) := by abel
        rw [e1, ← hα', ← hα, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← mul_assoc, hqqi, one_mul, smul_comm (algebraMap F E (g.q : F)) (α' i),
          smul_smul (algebraMap F E (g.q : F)), hqqi, one_smul, sub_smul, smul_sub]
        abel
      calc _ = (algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F)) • ∑ j, γ j • Sum.elim t.f
              (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j := by
            rw [hqiq, one_smul]
        _ = l := by rw [mul_smul, key, ← mul_smul, hqiq, one_smul]
    have hlO := hprim l hl ((Submodule.mem_span_range_iff_exists_fun E).2 ⟨γ, hsum⟩)
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 hlO
    have hβ' : ∑ j, (β j : E) • Sum.elim t.f
        (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j = l := by
      simpa only [Subring.smul_def] using hβ
    have hzero := Fintype.linearIndependent_iff.1 hli (fun j => (β j : E) - γ j) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hβ', hsum, sub_self])

    have hmem : ∀ i : Fin r, α' i ∈ M.L.O := by
      intro i
      have := hzero (Sum.inr i.castSucc)
      simp only [γ, Sum.elim_inr, Fin.snoc_castSucc, sub_eq_zero] at this
      rw [← this]
      exact (β _).2
    have hf'L := hgen.1.2.2.1.1.1
    have hw' : w = (x' : V) + ∑ i, α' i • t.f' i.castSucc := by rw [hα']; abel
    rw [hw']
    refine t.abelian₂.add_mem hx'L (Submodule.sum_mem _ fun i _ => ?_)
    have := t.abelian₂.smul_mem (⟨α' i, hmem i⟩ : M.L.O) (hf'L i.castSucc)
    simpa only [Subring.smul_def] using this

end G

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section T

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ThCorr (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t₁ t₂ : Term V M r)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'),
    H.IsGeneric t₁ → H.IsGeneric t₂ → H.Respects t₁ t₂ φ φ' →
    ∀ (w₁ : V) (hw₁ : w₁ ∈ H.W0 t₁.f t₁.f') (w₂ : V) (hw₂ : w₂ ∈ H.W0 t₂.f t₂.f'),
      φ (H.mkW t₁.f ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp H hw₁⟩) = H.mkW t₂.f ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H hw₂⟩ →
      φ' (H.mkW t₁.f' ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp' H hw₁⟩) = H.mkW t₂.f' ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H hw₂⟩ →
      (w₁ ∈ t₁.abelian₂ ↔ w₂ ∈ t₂.abelian₂)

theorem mem_iff_of_image_eq {A B : Type} [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B]
    (φ : A ≃ₗ[E] B) {S : Set A} {T : Set B} (h : φ '' S = T) {a : A} {b : B} (hab : φ a = b) :
    a ∈ S ↔ b ∈ T := by
  subst hab
  subst h
  exact φ.injective.mem_set_image.symm

theorem thCorr_holds (M : Model F E) (r : ℕ) : ThCorr M r := by
  intro V _ _ H t₁ t₂ φ φ' hg₁ hg₂ hR w₁ hw₁ w₂ hw₂ he he'
  obtain ⟨hL, -, hL', -, hι⟩ := hR
  have e1 := mem_iff_of_image_eq φ hL he
  have e2 := mem_iff_of_image_eq φ' hL' he'
  cases hs : M.split with
  | none =>
    exact (lemma0L_holds M r hs V H t₁ hg₁ w₁ hw₁).trans
      ((and_congr e1 e2).trans (lemma0L_holds M r hs V H t₂ hg₂ w₂ hw₂).symm)
  | some g =>
    have hinj : Function.Injective (Prod.map φ' φ) := φ'.injective.prodMap φ.injective
    have e3 := hinj.mem_set_image (s := H.iotaGraph g t₁)
      (a := (H.mkW t₁.f' ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp' H hw₁⟩, H.mkW t₁.f ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp H hw₁⟩))
    rw [hι g hs, Prod.map_apply, he, he'] at e3
    exact (lemma0G_holds M r g hs V H t₁ hg₁ w₁ hw₁).trans
      ((and_congr e1 (and_congr e2 e3.symm)).trans (lemma0G_holds M r g hs V H t₂ hg₂ w₂ hw₂).symm)

end T

end Formalism.L2.SG.LsDatumA
end
end

section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Cut

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def MMo (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V :=
  Submodule.span M.L.O (Set.range (H.MMfam t))

def MMsharp (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V where
  carrier := {u | u ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h u m ∈ M.L.O}
  add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun m hm => by
    rw [H.h_add_left]; exact M.L.O.add_mem (ha.2 m hm) (hb.2 m hm)⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun m _ => by rw [H.h_zero_left]; exact M.L.O.zero_mem⟩
  smul_mem' := fun c u hu => ⟨by rw [Subring.smul_def]; exact Submodule.smul_mem _ _ hu.1, fun m hm => by
    rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem c.2 (hu.2 m hm)⟩

abbrev DDt (H : HermSp M V) {r : ℕ} (t : Term V M r) : Type :=
  ↥(MMsharp H t) ⧸ (MMo H t).comap (MMsharp H t).subtype

def ddMk (H : HermSp M V) {r : ℕ} (t : Term V M r) (u : ↥(MMsharp H t)) : DDt H t :=
  Submodule.Quotient.mk u

def IsomD (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) : Prop :=
  ∀ (x y : ↥(MMsharp H t₁)) (x₂ y₂ : ↥(MMsharp H t₂)), θ (ddMk H t₁ x) = ddMk H t₂ x₂ →
    θ (ddMk H t₁ y) = ddMk H t₂ y₂ → H.h x₂ y₂ - H.h x y ∈ M.L.O

def Gam (H : HermSp M V) {r : ℕ} (t : Term V M r) : Set (DDt H t × H.Wb t.f) :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f)), p = (ddMk H t u, H.mkW t.f ⟨u, hu⟩)}

def Gam' (H : HermSp M V) {r : ℕ} (t : Term V M r) : Set (DDt H t × H.Wb t.f') :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f')), p = (ddMk H t u, H.mkW t.f' ⟨u, hu⟩)}

def GamR (H : HermSp M V) {r : ℕ} (t : Term V M r) (c : E) :
    Set (DDt H t × DDt H t × H.Wb t.f × H.Wb t.f') :=
  {p | ∃ (u u' u'' : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f)) (hu' : (u' : V) ∈ H.perp (H.X t.f')),
    (u : V) - u' = c • (u'' : V) ∧
      p = (ddMk H t u, ddMk H t u'', H.mkW t.f ⟨u, hu⟩, H.mkW t.f' ⟨u', hu'⟩)}

def MMInt (H : HermSp M V) {r : ℕ} (t : Term V M r) : Prop :=
  ∀ m ∈ MMo H t, ∀ m' ∈ MMo H t, H.h m m' ∈ M.L.O

def Theta (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Set (DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :=
  {θ | IsUnit (H.Dl t₂.f t₂.f' (r + 1)) ∧ MMInt H t₂ ∧ IsomD H t₁ t₂ θ ∧
    (M.split = none →
      (fun p => (θ p.1, φ p.2)) '' Gam H t₁ = Gam H t₂ ∧ (fun p => (θ p.1, φ' p.2)) '' Gam' H t₁ = Gam' H t₂) ∧
    (∀ g : SplitG M.L, M.split = some g →
      (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
        GamR H t₂ (algebraMap F E (g.q : F)))}

def LocalCountHypotheses (H : HermSp M V) {r : ℕ} (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂') : Prop :=
  H.IsGeneric t₁ ∧ Formalism.MainNotions.ThinScalesBound.FrameK H f₂ t₁.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H f₂' t₁.T' ∧
    H.Ident t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ∧
    H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (f₂ (Fin.last r)) ∧
    H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r))

end Cut

section Props

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def LatSide (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    Nat.card {Λ₂ : Submodule M.L.O V | H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
        H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ'} =
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ')

def ModSide0 (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    H.Dl t₁.f t₁.f' r = 0 →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = H.ZZplus t₁ →
      Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = M.nIso Z₁ Z₂

def ModSideU (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
      (∀ a b : Fin r, (Y₁.Z a b : E) = H.ZZplus t₁ a.castSucc b.castSucc ∧
        (Y₂.Z a b : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a.castSucc b.castSucc) →
      (∀ a : Fin r, (be₁ a : E) = H.ZZplus t₁ a.castSucc (Fin.last r) ∧
        (be₂ a : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a.castSucc (Fin.last r) ∧
        (al₁ a : E) = H.ZZplus t₁ (Fin.last r) a.castSucc ∧
        (al₂ a : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' (Fin.last r) a.castSucc) →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂


end Props

end Formalism.L2.SG.LsDatumA
end
end
