import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

variable (F) in

def vi (x : n → E) : n → 𝒜 := fun i => ιA (x i)

theorem vi_mem_hat {Λ : Submodule (𝓞 E) (n → E)} {x : n → E} (hx : x ∈ Λ) : vi F x ∈ hat F Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem vi_add_smul (x w : n → E) (M : ℕ) : vi F (x + (M : E) • w) = vi F x + (M : 𝒜) • vi F w := by
  funext i
  simp [vi, map_add, map_mul, map_natCast]

theorem vi_smul_int (r : 𝓞 E) (x : n → E) : vi F (r • x) = ιA (algebraMap (𝓞 E) E r) • vi F x := by
  funext i
  simp [vi, Algebra.smul_def, map_mul]


theorem incl_int_mem (r : 𝓞 E) : ιA (algebraMap (𝓞 E) E r) ∈ 𝒮 := by
  have := levelaf_tmul_mem (F := F) (E := E) r (one_mem (intAd F))
  exact this

theorem gmv (G : Matrix n n E) (x : n → E) : (G.map ιA) *ᵥ vi F x = vi F (G *ᵥ x) := by
  funext i
  simp [vi, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem natCast_ne (M : ℕ) (hM : M ≠ 0) : ((M : ℕ) : 𝓞 F) ≠ 0 := by
  intro h
  apply hM
  have := congrArg (algebraMap (𝓞 F) F) h
  simpa using this

theorem levelafC_nat (M : ℕ) : levelafC (F := F) E ((M : ℕ) : 𝓞 F) = (M : 𝒜) := by
  induction M with
  | zero => simp [levelafC]
  | succ k ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← ih]
    simp [levelafC, TensorProduct.tmul_add, Algebra.TensorProduct.one_def]

theorem approx_hat (M : ℕ) (hM : M ≠ 0) (Λ : Submodule (𝓞 E) (n → E)) (u : n → 𝒜)
    (hu : u ∈ hat F Λ) : ∃ x ∈ Λ, ∃ z ∈ hat F Λ, u = vi F x + (M : 𝒜) • z := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨x, hx, 0, zero_mem _, by rw [smul_zero, add_zero]; rfl⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by funext i; simp [vi]⟩
  | add u w _ _ hu hw =>
    obtain ⟨x, hx, z, hz, rfl⟩ := hu
    obtain ⟨x', hx', z', hz', rfl⟩ := hw
    refine ⟨x + x', add_mem hx hx', z + z', add_mem hz hz', ?_⟩
    funext i
    simp only [vi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add]
    ring
  | smul s u _ hu =>
    obtain ⟨x, hx, z, hz, rfl⟩ := hu
    obtain ⟨b, t, ht, hs⟩ := csGlob_approx (F := F) (E := E) csGlob_intAdApprox ((M : ℕ) : 𝓞 F)
      (natCast_ne M hM) (s : 𝒜) s.2
    refine ⟨b • x, Submodule.smul_mem _ b hx,
      (⟨t, ht⟩ : 𝒮) • vi F x + s • z, add_mem (Submodule.smul_mem _ _ (vi_mem_hat hx)) (Submodule.smul_mem _ _ hz), ?_⟩
    rw [levelafC_nat] at hs
    funext i
    have e1 : vi F (b • x) i = ιA (algebraMap (𝓞 E) E b) * ιA (x i) := by simp [vi, Algebra.smul_def, map_mul]
    rw [Pi.add_apply, e1]
    show (s : 𝒜) * (vi F x i + (M : 𝒜) * z i) = _ + (M : 𝒜) * (t * vi F x i + (s : 𝒜) * z i)
    rw [hs]
    simp only [vi]
    ring

theorem hat_fwd (G : Matrix n n E) {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x ∈ Λ, G *ᵥ x ∈ Λ')
    (u : n → 𝒜) (hu : u ∈ hat F Λ) : (G.map ιA) *ᵥ u ∈ hat F Λ' := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    show G.map ιA *ᵥ vi F x ∈ _
    rw [gmv]
    exact vi_mem_hat (h x hx)
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [mulVec_add]; exact add_mem hu hw
  | smul s u _ hu =>
    rw [Subring.smul_def, mulVec_smul]
    exact Submodule.smul_mem _ s hu

theorem hat_iff (G : GL n E) {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x, x ∈ Λ ↔ (G : Matrix n n E) *ᵥ x ∈ Λ')
    (u : n → 𝒜) : u ∈ hat F Λ ↔ ((G : Matrix n n E).map ιA) *ᵥ u ∈ hat F Λ' := by
  constructor
  · exact hat_fwd _ (fun x hx => (h x).1 hx) u
  · intro hu
    have h1 : ∀ x ∈ Λ', ((G⁻¹ : GL n E) : Matrix n n E) *ᵥ x ∈ Λ := by
      intro x hx
      refine (h _).2 ?_
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      exact hx
    have h2 := hat_fwd _ h1 _ hu
    rwa [mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec] at h2

theorem dl_anti (σ : E →ₐ[F] E) (J : Matrix n n E) {A B : Submodule (𝓞 E) (n → E)} (h : A ≤ B) :
    dl σ J B ≤ dl σ J A := fun y hy =>
  (mem_dl σ J A y).2 fun x hx => (mem_dl σ J B y).1 hy x (h hx)

theorem dl_map (σ : E →ₐ[F] E) (J : Matrix n n E) (G : GL n E) (hG : G ∈ UJ (σ : E →+* E) J)
    {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x, x ∈ Λ ↔ (G : Matrix n n E) *ᵥ x ∈ Λ') :
    ∀ x ∈ dl σ J Λ, (G : Matrix n n E) *ᵥ x ∈ dl σ J Λ' := by
  intro x hx
  rw [mem_dl] at hx ⊢
  intro x' hx'
  have hG' : cT (σ : E →+* E) (G : Matrix n n E) * J * (G : Matrix n n E) = J := hG
  have h1 : ((G⁻¹ : GL n E) : Matrix n n E) *ᵥ x' ∈ Λ := by
    refine (h _).2 ?_
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    exact hx'
  have h2 := hx _ h1
  have h3 : x' = (G : Matrix n n E) *ᵥ (((G⁻¹ : GL n E) : Matrix n n E) *ᵥ x') := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [h3, hform_mulVec, hG']
  exact h2

theorem bc_mem_UPts (σ : E →ₐ[F] E) (J : Matrix n n E) (G : GL n E) (hG : G ∈ UJ (σ : E →+* E) J) :
    bc ιA G ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  have hc : (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)).comp (σ : E →+* E) =
      (sigR σ (FiniteAdeleRing (𝓞 F) F)).comp (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) :=
    RingHom.ext fun a => (csDual_sig_incl σ a).symm
  exact base_change_mem_holds _ _ n _ _ ιA hc J G hG

theorem frames_core (σ : E →ₐ[F] E) (J : Matrix n n E) (Lb : Submodule (𝓞 E) (n → E))
    (hLbd : IsLat (dl σ J Lb)) {cls : Type} (Λ : cls → Submodule (𝓞 E) (n → E))
    (hΔ : ∀ c, IsLat (dl σ J (Λ c))) (y : cls → GL n 𝒜)
    (hy : ∀ c, y c ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ c (u : n → 𝒜), u ∈ hat F (Λ c) ↔ (((y c)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Lb)
    (M : ℕ) (hM : M ≠ 0) {m : Type} [Fintype m] (b : m → n → E) (hb : ∀ a, b a ∈ dl σ J Lb)
    (hgen : ∀ x ∈ dl σ J Lb, ∃ r : m → 𝓞 E, ∃ z ∈ dl σ J Lb, x = ∑ a, r a • b a + (M : E) • z) :
    ∃ e : cls → m → n → E, (∀ c a, e c a ∈ dl σ J (Λ c)) ∧
      ∀ c c' (G : GL n E), G ∈ UJ (σ : E →+* E) J →
        (∀ x, x ∈ Λ c ↔ (G : Matrix n n E) *ᵥ x ∈ Λ c') →
        (∀ a, ∃ w ∈ dl σ J (Λ c'), (G : Matrix n n E) *ᵥ e c a - e c' a = (M : E) • w) →
        ∃ k : GL n 𝒜, k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
          (∀ u : n → 𝒜, u ∈ hat F Lb ↔ (k : Matrix n n 𝒜) *ᵥ u ∈ hat F Lb) ∧
          (∀ u ∈ hat F (dl σ J Lb), ∃ z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ u - u = (M : 𝒜) • z) ∧
          y c' = bc ιA G * y c * k⁻¹ := by

  have hya : ∀ c (w : n → 𝒜), w ∈ hat F (dl σ J Lb) → ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w ∈ hat F (dl σ J (Λ c)) := by
    intro c w hw
    have h1 : Λ c ≤ globLat (y c) Lb := fun x hx => (hyl c _).1 (vi_mem_hat hx)
    have h2 : globLat (y c) (dl σ J Lb) ≤ dl σ J (Λ c) :=
      (glob_dl_le σ J Lb (y c) (hy c)).trans (dl_anti σ J h1)
    have h3 : ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w ∈ hat F (globLat (y c) (dl σ J Lb)) := by
      rw [mem_hat_glob hLbd]
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      exact hw
    exact hat_mono h2 h3

  have hyb : ∀ c (u : n → 𝒜), u ∈ hat F (dl σ J (Λ c)) →
      (((y c)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F (dl σ J Lb) := by
    intro c u hu
    have h1 : Lb ≤ globLat (y c)⁻¹ (Λ c) := by
      intro x hx
      show ((((y c)⁻¹)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F x ∈ hat F (Λ c)
      rw [inv_inv, hyl, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      exact vi_mem_hat hx
    have h2 : globLat (y c)⁻¹ (dl σ J (Λ c)) ≤ dl σ J Lb :=
      (glob_dl_le σ J (Λ c) _ (inv_mem (hy c))).trans (dl_anti σ J h1)
    have h3 : (((y c)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F (globLat (y c)⁻¹ (dl σ J (Λ c))) := by
      rw [mem_hat_glob (hΔ c), inv_inv, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      exact hu
    exact hat_mono h2 h3

  have hfr : ∀ c a, ∃ x ∈ dl σ J (Λ c), ∃ z ∈ hat F (dl σ J (Λ c)),
      ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a) = vi F x + (M : 𝒜) • z :=
    fun c a => approx_hat M hM _ _ (hya c _ (vi_mem_hat (hb a)))
  choose e he z hz hez using hfr
  refine ⟨e, he, ?_⟩
  intro c c' G hG hGΛ hGe
  set k : GL n 𝒜 := (y c')⁻¹ * bc ιA G * y c with hk
  have hkm : (k : Matrix n n 𝒜) = (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * (G : Matrix n n E).map ιA *
      ((y c : GL n 𝒜) : Matrix n n 𝒜) := by
    rw [hk, Units.val_mul, Units.val_mul]; rfl
  have hGd := dl_map σ J G hG hGΛ

  have hkd : ∀ u ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ u ∈ hat F (dl σ J Lb) := by
    intro u hu
    rw [hkm, ← mulVec_mulVec, ← mulVec_mulVec]
    exact hyb c' _ (hat_fwd _ hGd _ (hya c _ hu))

  have hkb : ∀ a, ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (b a) - vi F (b a) = (M : 𝒜) • Z := by
    intro a
    obtain ⟨w, hw, hwe⟩ := hGe a
    have hGe' : (G : Matrix n n E) *ᵥ e c a = e c' a + (M : E) • w := sub_eq_iff_eq_add'.1 hwe
    have key : (G : Matrix n n E).map ιA *ᵥ (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) -
        ((y c' : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a) =
        (M : 𝒜) • (vi F w + (G : Matrix n n E).map ιA *ᵥ z c a - z c' a) := by
      rw [hez c a, hez c' a, mulVec_add, mulVec_smul, gmv, hGe', vi_add_smul]
      simp only [smul_add, smul_sub]
      abel
    refine ⟨(((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (vi F w + (G : Matrix n n E).map ιA *ᵥ z c a - z c' a),
      hyb c' _ (sub_mem (add_mem (vi_mem_hat hw) (hat_fwd _ hGd _ (hz c a))) (hz c' a)), ?_⟩
    have h1 : vi F (b a) = (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ
        (((y c' : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) := by
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    have h2 : (k : Matrix n n 𝒜) *ᵥ vi F (b a) = (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ
        ((G : Matrix n n E).map ιA *ᵥ (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a))) := by
      rw [hkm, ← mulVec_mulVec, ← mulVec_mulVec]
    have h3 : (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ
        ((G : Matrix n n E).map ιA *ᵥ (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a))) - vi F (b a) =
        (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ ((G : Matrix n n E).map ιA *ᵥ
          (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) - ((y c' : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) := by
      rw [mulVec_sub, ← h1]
    rw [h2, h3, key, mulVec_smul]
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem (inv_mem (hy c')) (bc_mem_UPts σ J G hG)) (hy c)
  · intro u
    rw [hkm, ← mulVec_mulVec, ← mulVec_mulVec]
    have e1 : u ∈ hat F Lb ↔ ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F (Λ c) := by
      rw [hyl, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [e1, hat_iff G hGΛ, hyl]
  · intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x, hx, rfl⟩ := hu
      show ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x - vi F x = (M : 𝒜) • Z

      have hadd : ∀ x x' : n → E, (∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x - vi F x = (M : 𝒜) • Z) →
          (∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x' - vi F x' = (M : 𝒜) • Z) →
          ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (x + x') - vi F (x + x') = (M : 𝒜) • Z := by
        rintro x x' ⟨Z, hZ, hZe⟩ ⟨Z', hZ', hZe'⟩
        refine ⟨Z + Z', add_mem hZ hZ', ?_⟩
        have : vi F (x + x') = vi F x + vi F x' := by funext i; simp [vi]
        rw [this, mulVec_add, smul_add, ← hZe, ← hZe']
        abel
      have hzero : ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (0 : n → E) - vi F 0 = (M : 𝒜) • Z :=
        ⟨0, zero_mem _, by
          have : vi F (0 : n → E) = 0 := by funext i; simp [vi]
          rw [this, mulVec_zero, sub_zero, smul_zero]⟩
      have hsmul : ∀ (r : 𝓞 E) (x : n → E),
          (∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x - vi F x = (M : 𝒜) • Z) →
          ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (r • x) - vi F (r • x) = (M : 𝒜) • Z := by
        rintro r x ⟨Z, hZ, hZe⟩
        refine ⟨(⟨_, incl_int_mem r⟩ : 𝒮) • Z, Submodule.smul_mem _ _ hZ, ?_⟩
        rw [vi_smul_int, mulVec_smul, ← smul_sub, hZe, Subring.smul_def, smul_comm]
      classical
      obtain ⟨r, z0, hz0, rfl⟩ := hgen x hx
      refine hadd _ _ ?_ ?_
      · have : ∀ s : Finset m, ∃ Z ∈ hat F (dl σ J Lb),
            (k : Matrix n n 𝒜) *ᵥ vi F (∑ a ∈ s, r a • b a) - vi F (∑ a ∈ s, r a • b a) = (M : 𝒜) • Z := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa using hzero
          | insert a s ha ih =>
            rw [Finset.sum_insert ha]
            exact hadd _ _ (hsmul _ _ (hkb a)) ih
        exact this Finset.univ
      · refine ⟨(k : Matrix n n 𝒜) *ᵥ vi F z0 - vi F z0, sub_mem (hkd _ (vi_mem_hat hz0)) (vi_mem_hat hz0), ?_⟩
        have : vi F ((M : E) • z0) = (M : 𝒜) • vi F z0 := by
          have := vi_add_smul (F := F) (0 : n → E) z0 M
          rwa [zero_add, show vi F (0 : n → E) = 0 from by funext i; simp [vi], zero_add] at this
        rw [this, mulVec_smul, smul_sub]
    | zero => exact ⟨0, zero_mem _, by rw [mulVec_zero, sub_zero, smul_zero]⟩
    | add u w _ _ hu hw =>
      obtain ⟨Z, hZ, hZe⟩ := hu
      obtain ⟨Z', hZ', hZe'⟩ := hw
      refine ⟨Z + Z', add_mem hZ hZ', ?_⟩
      rw [mulVec_add, smul_add, ← hZe, ← hZe']
      abel
    | smul s u _ hu =>
      obtain ⟨Z, hZ, hZe⟩ := hu
      refine ⟨s • Z, Submodule.smul_mem _ s hZ, ?_⟩
      rw [Subring.smul_def, Subring.smul_def, mulVec_smul, ← smul_sub, hZe, smul_comm]
  · rw [hk]
    group

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

variable (v : HeightOneSpectrum (𝓞 F))

abbrev lv (Λ : Submodule (𝓞 E) (n → E)) : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

theorem prV_hat {Λ : Submodule (𝓞 E) (n → E)} (u : n → 𝒜) (hu : u ∈ hat F Λ) :
    (fun i => prV (E := E) v (u i)) ∈ lv v Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : (fun i => prV (E := E) v ((0 : n → 𝒜) i)) = 0 := by funext i; simp
    rw [this]; exact zero_mem _
  | add u w _ _ hu hw =>
    have : (fun i => prV (E := E) v ((u + w) i)) =
        (fun i => prV (E := E) v (u i)) + (fun i => prV (E := E) v (w i)) := by funext i; simp
    rw [this]; exact add_mem hu hw
  | smul s u _ hu =>
    have hs := afsplit_prV_int (E := E) v (s : 𝒜) s.2
    have : (fun i => prV (E := E) v ((s • u) i)) =
        (⟨_, hs⟩ : intV E v) • (fun i => prV (E := E) v (u i)) := by
      funext i
      simp [Subring.smul_def, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ hu

theorem bc_mulVec_vi (k : GL n 𝒜) (x : n → E) :
    ((bc (prV (E := E) v) k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (v.adicCompletion F) (x i)) =
      fun i => prV (E := E) v (((k : Matrix n n 𝒜) *ᵥ vi F x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem loc_fwd {Λ Λ' : Submodule (𝓞 E) (n → E)} (k : GL n 𝒜) (hk : ∀ u ∈ hat F Λ, (k : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ')
    (y : n → E ⊗[F] v.adicCompletion F) (hy : y ∈ lv v Λ) :
    ((bc (prV (E := E) v) k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n _) *ᵥ y ∈ lv v Λ' := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [bc_mulVec_vi]
    exact prV_hat v _ (hk _ (vi_mem_hat hx))
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [mulVec_add]; exact add_mem hy hw
  | smul t y _ hy =>
    rw [Subring.smul_def, mulVec_smul]
    exact Submodule.smul_mem _ t hy

theorem loc_cong {Λ Λ' : Submodule (𝓞 E) (n → E)} (k : GL n 𝒜) (M : ℕ)
    (hk : ∀ u ∈ hat F Λ, ∃ z ∈ hat F Λ', (k : Matrix n n 𝒜) *ᵥ u - u = (M : 𝒜) • z)
    (y : n → E ⊗[F] v.adicCompletion F) (hy : y ∈ lv v Λ) :
    ∃ z ∈ lv v Λ', ((bc (prV (E := E) v) k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n _) *ᵥ y - y =
      (M : E ⊗[F] v.adicCompletion F) • z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨z, hz, hze⟩ := hk _ (vi_mem_hat hx)
    refine ⟨fun i => prV (E := E) v (z i), prV_hat v z hz, ?_⟩
    rw [bc_mulVec_vi]
    funext i
    have := congrFun hze i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← afsplit_prV_inclE, ← map_sub, show (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) (x i) = vi F x i from rfl,
      this, map_mul, map_natCast]
  | zero => exact ⟨0, zero_mem _, by rw [mulVec_zero, sub_zero, smul_zero]⟩
  | add y w _ _ hy hw =>
    obtain ⟨z, hz, hze⟩ := hy
    obtain ⟨z', hz', hze'⟩ := hw
    refine ⟨z + z', add_mem hz hz', ?_⟩
    rw [mulVec_add, smul_add, ← hze, ← hze']
    abel
  | smul t y _ hy =>
    obtain ⟨z, hz, hze⟩ := hy
    refine ⟨t • z, Submodule.smul_mem _ t hz, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, mulVec_smul, ← smul_sub, hze, smul_comm]

theorem natCast_smul_mem {Λ : Submodule (𝓞 E) (n → E)} (N : ℕ) {z : n → E ⊗[F] v.adicCompletion F}
    (hz : z ∈ lv v Λ) : (N : E ⊗[F] v.adicCompletion F) • z ∈ lv v Λ := by
  have := Submodule.smul_mem (lv v Λ) (N : intV E v) hz
  rwa [Subring.smul_def, Subring.coe_natCast] at this

theorem smul_lv_of {Λ Λ' : Submodule (𝓞 E) (n → E)} (t : E) (ht : ∀ x ∈ Λ, t • x ∈ Λ')
    {z : n → E ⊗[F] v.adicCompletion F} (hz : z ∈ lv v Λ) :
    inclE (F := F) (v.adicCompletion F) t • z ∈ lv v Λ' := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨t • x, ht x hx, ?_⟩
    funext i
    simp [map_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z w _ _ hz hw => rw [smul_add]; exact add_mem hz hw
  | smul s z _ hz =>
    rw [Subring.smul_def, smul_comm]
    exact Submodule.smul_mem _ s hz

theorem loc_stab {Λ : Submodule (𝓞 E) (n → E)} (k : GL n 𝒜)
    (hk : ∀ u : n → 𝒜, u ∈ hat F Λ ↔ (k : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ) (x : n → E ⊗[F] v.adicCompletion F) :
    x ∈ lv v Λ ↔ ((bc (prV (E := E) v) k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n _) *ᵥ x ∈ lv v Λ := by
  constructor
  · exact loc_fwd v k (fun u hu => (hk u).1 hu) x
  · intro hx
    have hk' : ∀ u ∈ hat F Λ, ((k⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ := by
      intro u hu
      refine (hk _).2 ?_
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      exact hu
    have h := loc_fwd v k⁻¹ hk' _ hx
    rwa [map_inv, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h

end Loc

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

open Formalism.L2.Herm in

theorem stepLevel_mem {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ}
    (lev : StepLevel hc S gp T f) (k : GL (Fin S.rank) 𝒜) (hkU : k ∈ UAf hc S)
    (hst : ∀ u, u ∈ hat F lev.Lb ↔ (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u ∈ hat F lev.Lb)
    (hcg : ∀ u ∈ hat F (dualL hc S lev.Lb), ∃ z ∈ hat F (dualL hc S lev.Lb),
      (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u - u = ((T * gp 0 * gp 1 : ℕ) : 𝒜) • z) :
    k ∈ lev.U := by
  rw [lev.U_eq]
  refine ⟨hkU, fun v => ?_⟩
  have hlev : bc (prV (E := E) v) k ∈ levelVL hc.sig S.gram v lev.Lb :=
    Subgroup.mem_inf.2 ⟨afsplit_bc_mem hc.sig S.gram v k hkU, fun x => loc_stab v k hst x⟩
  have hTd : ∀ x ∈ dualL hc S lev.Lb, (T : E) • x ∈ lev.Lb := lev.Lb_dual
  have hTz : ∀ z ∈ lv v (dualL hc S lev.Lb), (T : E ⊗[F] v.adicCompletion F) • z ∈ lv v lev.Lb := by
    intro z hz
    have := smul_lv_of v (T : E) hTd hz
    rwa [map_natCast] at this
  have hmono : lv v lev.Lb ≤ lv v (dualL hc S lev.Lb) := Submodule.span_mono (Set.image_mono lev.Lb_int)
  by_cases hTv : (T : 𝓞 F) ∈ v.asIdeal
  · rw [lev.UlocAlt v hTv]
    refine ⟨hlev, fun y hy => ?_⟩
    obtain ⟨z, hz, hze⟩ := loc_cong v k _ hcg y hy
    rw [hze, show ((T * gp 0 * gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) = ((gp 0 * gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) *
      (T : E ⊗[F] v.adicCompletion F) by push_cast; ring, mul_smul]
    exact natCast_smul_mem v _ (hTz z hz)
  by_cases hg0 : (gp 0 : 𝓞 F) ∈ v.asIdeal
  · refine lev.Uloc_g 0 v hg0 _ ⟨hlev, fun y hy => ?_⟩
    obtain ⟨z, hz, hze⟩ := loc_cong v k _ hcg y (hmono hy)
    refine ⟨((gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) • ((T : E ⊗[F] v.adicCompletion F) • z),
      natCast_smul_mem v _ (hTz z hz), ?_⟩
    rw [hze, smul_smul, smul_smul]
    congr 1
    push_cast; ring
  by_cases hg1 : (gp 1 : 𝓞 F) ∈ v.asIdeal
  · refine lev.Uloc_g 1 v hg1 _ ⟨hlev, fun y hy => ?_⟩
    obtain ⟨z, hz, hze⟩ := loc_cong v k _ hcg y (hmono hy)
    refine ⟨((gp 0 : ℕ) : E ⊗[F] v.adicCompletion F) • ((T : E ⊗[F] v.adicCompletion F) • z),
      natCast_smul_mem v _ (hTz z hz), ?_⟩
    rw [hze, smul_smul, smul_smul]
    congr 1
    push_cast; ring
  rw [lev.Uloc_hyp v hg0 hg1 hTv]
  exact hlev

open Formalism.L2.Herm in

theorem stepLevel0_mem {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {Lb : Submodule (𝓞 E) (Fin S.rank → E)}
    (hsd : dualL hc S Lb = Lb) (lev : StepLevel0 hc S gp Lb) (T : ℕ) (k : GL (Fin S.rank) 𝒜) (hkU : k ∈ UAf hc S)
    (hst : ∀ u, u ∈ hat F Lb ↔ (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u ∈ hat F Lb)
    (hcg : ∀ u ∈ hat F (dualL hc S Lb), ∃ z ∈ hat F (dualL hc S Lb),
      (k : Matrix (Fin S.rank) (Fin S.rank) 𝒜) *ᵥ u - u = ((T * gp 0 * gp 1 : ℕ) : 𝒜) • z) :
    k ∈ lev.U := by
  rw [lev.U_eq]
  refine ⟨hkU, fun v => ?_⟩
  have hlev : bc (prV (E := E) v) k ∈ levelVL hc.sig S.gram v Lb :=
    Subgroup.mem_inf.2 ⟨afsplit_bc_mem hc.sig S.gram v k hkU, fun x => loc_stab v k hst x⟩
  rw [hsd] at hcg
  by_cases hg0 : (gp 0 : 𝓞 F) ∈ v.asIdeal
  · refine lev.Uloc_g 0 v hg0 _ ⟨hlev, fun y hy => ?_⟩
    obtain ⟨z, hz, hze⟩ := loc_cong v k _ hcg y hy
    refine ⟨((T * gp 1 : ℕ) : E ⊗[F] v.adicCompletion F) • z, natCast_smul_mem v _ hz, ?_⟩
    rw [hze, smul_smul]
    congr 1
    push_cast; ring
  by_cases hg1 : (gp 1 : 𝓞 F) ∈ v.asIdeal
  · refine lev.Uloc_g 1 v hg1 _ ⟨hlev, fun y hy => ?_⟩
    obtain ⟨z, hz, hze⟩ := loc_cong v k _ hcg y hy
    refine ⟨((T * gp 0 : ℕ) : E ⊗[F] v.adicCompletion F) • z, natCast_smul_mem v _ hz, ?_⟩
    rw [hze, smul_smul]
    congr 1
    push_cast; ring
  rw [lev.Uloc_hyp v hg0 hg1]
  exact hlev

end Lev

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
end
