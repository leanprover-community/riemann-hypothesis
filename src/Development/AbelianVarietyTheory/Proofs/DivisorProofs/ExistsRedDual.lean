import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualIsConnOfIsEtPDivGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigToLieBijectiveAndDualRigOfOmegaBijectiveOfIsE

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem wittDual_reduction : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (M V : Type) [AddCommGroup M] [Module (WittVector p k) M] [Module.Free (WittVector p k) M] [Module.Finite (WittVector p k) M] [AddCommGroup V] [Module k V] (r : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = p • n) → ∃ r' : Module.Dual (WittVector p k) M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] Module.Dual k V, (∀ l m, r' l (r m) = WittVector.constantCoeff (l m)) ∧ Function.Surjective r' ∧ ∀ l, r' l = 0 ↔ ∃ l', l = p • l' := by
  intro p _ k _ _ _ M V _ _ _ _ _ _ r hr hker
  have hσs : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) :=
    WittVector.constantCoeff_surjective p
  have hpk : ∀ y : k, (p • y) = 0 := fun y => by
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hσker : ∀ x : WittVector p k, WittVector.constantCoeff x = 0 → ∃ y, x = p • y := by
    intro x hx
    have hx' : x ∈ Ideal.span {(p : WittVector p k)} :=
      (WittVector.mem_span_p_iff_coeff_zero_eq_zero x).2 (by simpa [WittVector.constantCoeff_apply] using hx)
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx'
    exact ⟨y, by rw [nsmul_eq_mul, ← hy, mul_comm]⟩
  have hwd : ∀ (l : Module.Dual (WittVector p k) M) (m m' : M), r m = r m' →
      WittVector.constantCoeff (l m) = WittVector.constantCoeff (l m') := by
    intro l m m' h
    obtain ⟨n, hn⟩ := (hker (m - m')).1 (by rw [map_sub, h, sub_self])
    have h1 : l m - l m' = p • l n := by rw [← map_sub, hn, map_nsmul]
    rw [← sub_eq_zero, ← map_sub, h1, map_nsmul, hpk]
  have hg0 : ∀ (l : Module.Dual (WittVector p k) M) (m : M),
      WittVector.constantCoeff (l (Function.surjInv hr (r m))) = WittVector.constantCoeff (l m) :=
    fun l m => hwd l _ _ (Function.surjInv_eq hr _)
  let g : Module.Dual (WittVector p k) M → Module.Dual k V := fun l =>
    { toFun := fun v => WittVector.constantCoeff (l (Function.surjInv hr v))
      map_add' := fun v w => by
        obtain ⟨m, rfl⟩ := hr v
        obtain ⟨m', rfl⟩ := hr w
        rw [← map_add r, hg0, hg0, hg0, map_add, map_add]
      map_smul' := fun c v => by
        obtain ⟨a, rfl⟩ := hσs c
        obtain ⟨m, rfl⟩ := hr v
        rw [← LinearMap.map_smulₛₗ, hg0, hg0, map_smul, smul_eq_mul, map_mul, RingHom.id_apply,
          smul_eq_mul] }
  have hg : ∀ l m, g l (r m) = WittVector.constantCoeff (l m) := fun l m => hg0 l m
  let r' : Module.Dual (WittVector p k) M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
      Module.Dual k V :=
    { toFun := g
      map_add' := fun l l' => by
        ext v
        obtain ⟨m, rfl⟩ := hr v
        rw [LinearMap.add_apply, hg, hg, hg, LinearMap.add_apply, map_add]
      map_smul' := fun a l => by
        ext v
        obtain ⟨m, rfl⟩ := hr v
        rw [LinearMap.smul_apply, hg, hg, LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul] }
  have hr' : ∀ l m, r' l (r m) = WittVector.constantCoeff (l m) := hg
  let b := Module.Free.chooseBasis (WittVector p k) M
  refine ⟨r', hr', ?_, ?_⟩
  · intro f
    let a : Module.Free.ChooseBasisIndex (WittVector p k) M → WittVector p k :=
      fun i => Function.surjInv hσs (f (r (b i)))
    let l : Module.Dual (WittVector p k) M := b.constr (WittVector p k) a
    let F1 : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] k :=
      { toFun := fun m => WittVector.constantCoeff (l m)
        map_add' := fun m m' => by rw [map_add, map_add]
        map_smul' := fun c m => by rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul] }
    have hF : F1 = f.comp r := by
      refine b.ext fun i => ?_
      show WittVector.constantCoeff (l (b i)) = f (r (b i))
      rw [show l (b i) = a i from b.constr_basis _ _ _]
      exact Function.surjInv_eq hσs _
    refine ⟨l, ?_⟩
    ext v
    obtain ⟨m, rfl⟩ := hr v
    rw [hr']
    exact LinearMap.congr_fun hF m
  · intro l
    constructor
    · intro h0
      have hz : ∀ m, WittVector.constantCoeff (l m) = 0 := fun m => by
        rw [← hr', h0, LinearMap.zero_apply]
      choose w hw using fun i => hσker _ (hz (b i))
      refine ⟨b.constr (WittVector p k) w, b.ext fun i => ?_⟩
      rw [LinearMap.smul_apply, b.constr_basis, hw]
    · rintro ⟨l', rfl⟩
      rw [map_nsmul]
      ext v
      rw [LinearMap.smul_apply, hpk, LinearMap.zero_apply]

end GlobalTheory
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.EtFromConn

variable {p : ℕ} [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn))

theorem dual_conn {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G : PDivGroup p k}
    (hG : G.IsEt) : G.dual.IsConn :=
  PDivGroup.dual_isConn_of_isEt p k G hG

abbrev Mod {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k)
    (hG : G.IsEt) : Type :=
  Module.Dual (WittVector p k) (B.M G.dual (dual_conn hG))

def IsTr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] (σ : k →+* k') {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) (l' : Mod B G' hG') : Prop :=
  letI : Algebra k k' := σ.toAlgebra
  ∃ (hb : (G.dual.baseChange k').IsConn)
    (lb : Module.Dual (WittVector p k') (B.M (G.dual.baseChange k') hb)),
    (∀ x, lb (B.smap hb (dual_conn hG) (G.dual.toBase k') x) = WittVector.map σ (l x)) ∧
    ∀ y, l' y = lb (B.map hb (dual_conn hG')
      ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) y)

open Classical in

def tr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) : Mod B G' hG' :=
  if h : ∃ l', IsTr B σ hG' hG s l l' then Classical.choose h else 0

theorem tr_spec {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) (h : ∃ l', IsTr B σ hG' hG s l l') :
    IsTr B σ hG' hG s l (tr B hG' hG s l) := by
  rw [tr, dif_pos h]
  exact Classical.choose_spec h

section Red

variable {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (hG : G.IsEt)

theorem exists_redDual : ∃ r' : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
      Module.Dual k G.dual.RigExt,
    (∀ l m, r' l (B.red G.dual (dual_conn hG) m) = WittVector.constantCoeff (l m)) ∧
      Function.Surjective r' ∧ ∀ l, r' l = 0 ↔ ∃ l', l = p • l' := by
  haveI := B.free G.dual (dual_conn hG)
  haveI := B.finite G.dual (dual_conn hG)
  exact wittDual_reduction p k _ _ (B.red G.dual (dual_conn hG))
    (B.red_surjective G.dual (dual_conn hG)) (B.red_eq_zero G.dual (dual_conn hG))

def redDual : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
    Module.Dual k G.dual.RigExt :=
  Classical.choose (exists_redDual B G hG)

theorem redDual_spec :
    (∀ l m, redDual B G hG l (B.red G.dual (dual_conn hG) m) = WittVector.constantCoeff (l m)) ∧
      Function.Surjective (redDual B G hG) ∧ ∀ l, redDual B G hG l = 0 ↔ ∃ l', l = p • l' :=
  Classical.choose_spec (exists_redDual B G hG)

def rigLie : G.RigExt ≃ₗ[k] G.dual.Lie :=
  LinearEquiv.ofBijective (G.rigToLie (p_eq_zero p k))
    (PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k (p_eq_zero p k) G hG).1

def red : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt :=
  (rigLie G hG).symm.toLinearMap.comp (G.dual.rigOfOmega.dualMap.comp (redDual B G hG))

theorem rigToLie_red (l : Mod B G hG) :
    G.rigToLie (p_eq_zero p k) (red B G hG l) = G.dual.rigOfOmega.dualMap (redDual B G hG l) :=
  (rigLie G hG).apply_symm_apply _

end Red

end GlobalTheory.Dieu.EtFromConn
end
end
