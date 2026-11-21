import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMapEqOfKerEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFinrankDeRhamQuotientCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartLieDeRhamQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomHarrisTaylorOrderMoritaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPairingSkewHodgeLagrangianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCrystalActionAdjointStatement

section
section
open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model GlobalTheory.UPel.Sm.KSCount

noncomputable section

namespace GlobalTheory.UPel.Sm.KSCount

theorem ksDim_of_eigen_reduce : ∀ (k : Type) (H : Type 1) (O : Type) [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (ρ : O →+* Module.End k H) (st : O → O) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (w : O) (r r' : k) (d : ℕ), Function.Surjective st → (∀ b x y, φ (ρ b x) y = φ x (ρ (st b) y)) → (∀ x y, φ x y = -φ y x) → (∀ x, (∀ y, φ x y = 0) → x = 0) → (∀ x ∈ Fil, ∀ y ∈ Fil, φ x y = 0) → 2 * Module.finrank k Fil = Module.finrank k H → (∀ a, ∀ x ∈ Fil, ρ a x ∈ Fil) → (∀ a, ρ w * ρ a = ρ a * ρ w) → (ρ w - r • 1) * (ρ w - r' • 1) = 0 → r ≠ r' → (∀ x y, φ (ρ w x) y = φ x ((r + r') • y - ρ w y)) → Z ≤ LinearMap.range (ρ w - r' • 1) → KSDim ρ 0 (Fil ⊔ LinearMap.range (ρ w - r • 1)) Z d → KSDim ρ φ Fil Z d := by
  intro k H O _ _ _ _ _ ρ st φ Fil Z w r r' d hst hadj hskew hnd hiso hdim hstab hcomm hA hr hφw hZ hd
  set A := ρ w with hAdef
  have hA2 : ∀ x, A (A x) = (r + r') • A x - (r * r') • x := by
    intro x
    have h := LinearMap.congr_fun hA x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, LinearMap.zero_apply] at h
    linear_combination (norm := module) h
  have hrr : r - r' ≠ 0 := sub_ne_zero.2 hr
  set c := (r - r')⁻¹ with hc
  have hc1 : c * (r - r') = 1 := inv_mul_cancel₀ hrr
  let P : Module.End k H := c • (A - r' • 1)
  have hPx : ∀ x, P x = c • (A x - r' • x) := fun x => by simp [P]
  have hPA : ∀ x, A (P x) = r • P x := by
    intro x; rw [hPx, map_smul, map_sub, map_smul, hA2]
    linear_combination (norm := module) (0:k) • x
  have hPfix : ∀ x, A x = r • x → P x = x := by
    intro x hx; rw [hPx, hx]
    linear_combination (norm := module) hc1 • x
  have hPkill : ∀ x, A x = r' • x → P x = 0 := by
    intro x hx; rw [hPx, hx]; simp
  have hQA : ∀ x, A (x - P x) = r' • (x - P x) := by
    intro x; rw [map_sub, hPA]
    have : A x - r' • x = (r - r') • P x := by rw [hPx, smul_smul, mul_comm, hc1, one_smul]
    linear_combination (norm := module) this
  have hPP : ∀ x, P (P x) = P x := fun x => hPfix _ (hPA x)
  have hPQ : ∀ x, P (x - P x) = 0 := fun x => hPkill _ (hQA x)

  have hAρ : ∀ a x, A (ρ a x) = ρ a (A x) := fun a x => LinearMap.congr_fun (hcomm a) x
  have hPρ : ∀ a x, P (ρ a x) = ρ a (P x) := by
    intro a x; rw [hPx, hPx, hAρ, map_smul, map_sub, map_smul]
  have hPFil : ∀ x ∈ Fil, P x ∈ Fil := fun x hx => by
    rw [hPx]; exact Fil.smul_mem _ (Fil.sub_mem (hstab w x hx) (Fil.smul_mem _ hx))
  have hQFil : ∀ x ∈ Fil, x - P x ∈ Fil := fun x hx => Fil.sub_mem hx (hPFil x hx)
  have hφeig : ∀ (s t : k), s ≠ t → s + t = r + r' → ∀ u v, A u = s • u → A v = s • v → φ u v = 0 := by
    intro s t hst' hsum u v hu hv
    have h := hφw u v
    rw [hu, hv] at h
    simp only [map_smul, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, smul_eq_mul] at h
    have h2 : (s - t) * φ u v = 0 := by linear_combination h - (φ u v) * hsum
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hst')
  have hφPP : ∀ x y, φ (P x) (P y) = 0 := fun x y => hφeig r r' hr rfl _ _ (hPA x) (hPA y)
  have hφQQ : ∀ x y, φ (x - P x) (y - P y) = 0 := fun x y =>
    hφeig r' r (Ne.symm hr) (add_comm _ _) _ _ (hQA x) (hQA y)
  have hφdec : ∀ a b, φ a b = φ (P a) (b - P b) + φ (a - P a) (P b) := by
    intro a b
    have e : φ a b = φ (P a + (a - P a)) (P b + (b - P b)) := by simp
    rw [e]
    simp only [map_add, LinearMap.add_apply, hφPP, hφQQ]
    ring
  have hnd' : φ.Nondegenerate := ⟨hnd, fun y h => hnd y (fun x => by rw [hskew, h x, neg_zero])⟩
  have hperp : ∀ v, (∀ y ∈ Fil, φ v y = 0) → v ∈ Fil := by
    have hle : Fil ≤ φ.orthogonal Fil := by
      intro x hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      exact hiso y hy x hx
    have hdim2 := LinearMap.BilinForm.finrank_orthogonal hnd' Fil
    have heq : Fil = φ.orthogonal Fil := Submodule.eq_of_le_of_finrank_le hle (by omega)
    intro v hv
    rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    change φ y v = 0
    rw [hskew, hv y hy, neg_zero]

  have hAP : ∀ v, A v - r' • v = (r - r') • P v := fun v => by
    rw [hPx, smul_smul, mul_comm, hc1, one_smul]
  have hPAc : ∀ x, P (A x) = A (P x) := fun x => by rw [hPx, hPx, map_smul, map_sub, map_smul]
  set G := Fil ⊔ LinearMap.range (A - r • 1) with hG
  have hrangeP : ∀ y ∈ LinearMap.range (A - r • 1), P y = 0 := by
    rintro _ ⟨z, rfl⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hPAc, hPA, sub_self]
  have hFilG : Fil ≤ G := le_sup_left
  have hmemG : ∀ x ∈ G, P x ∈ Fil := by
    intro x hx
    obtain ⟨f, hf, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hrangeP y hy, add_zero]
    exact hPFil f hf
  have hQG : ∀ x, x - P x ∈ G := by
    intro x
    apply Submodule.mem_sup_right
    refine ⟨(-c) • x, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul]
    have h := hAP x
    linear_combination (norm := module) (-c) • h - hc1 • P x + hc1 • x
  have hZP : ∀ z ∈ Z, P z = z := by
    intro z hz
    obtain ⟨y, rfl⟩ := hZ hz
    apply hPfix
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hA2]
    module
  have hwQ : ∀ (F : Submodule k H) v, r • v - A v ∈ F → v - P v ∈ F := by
    intro F v hv
    have e : v - P v = c • (r • v - A v) := by
      have h := hAP v
      linear_combination (norm := module) c • h - hc1 • v + hc1 • P v
    rw [e]; exact F.smul_mem _ hv
  have hwP : ∀ (F : Submodule k H) v, r' • v - A v ∈ F → P v ∈ F := by
    intro F v hv
    have e : P v = (-c) • (r' • v - A v) := by
      have h := hAP v
      linear_combination (norm := module) (-c) • h - hc1 • P v
    rw [e]; exact F.smul_mem _ hv
  have L1 : ∀ v y, φ (P v) y = φ (P v) (y - P y) := fun v y => by
    rw [hφdec (P v) y]; simp [hPP]
  have L2 : ∀ v y, φ (v - P v) y = φ v (P y) := fun v y => by
    rw [hφdec (v - P v) y, hφdec v (P y)]; simp [hPP, hPQ]
  have L3 : ∀ x v, φ x (P v) = φ (x - P x) (P v) := fun x v => by
    rw [hφdec x (P v)]; simp [hPP]
  have L4 : ∀ x v, φ x (v - P v) = φ (P x) v := fun x v => by
    rw [hφdec x (v - P v), hφdec (P x) v]; simp [hPP, hPQ]
  have hQcrit : ∀ v, (∀ y ∈ Fil, φ v (P y) = 0) → v - P v ∈ Fil := by
    intro v hv
    apply hperp
    intro y hy
    rw [L2]; exact hv y hy

  let conj : (H →ₗ[k] H) →ₗ[k] (H →ₗ[k] H) :=
    { toFun := fun g => P ∘ₗ g ∘ₗ P
      map_add' := fun f g => by ext; simp
      map_smul' := fun a f => by ext; simp }
  have hconj : ∀ g x, conj g x = P (g (P x)) := fun _ _ => rfl
  have hi : ∀ g, IsKS ρ φ Fil Z g → IsKS ρ 0 G Z (conj g) := by
    intro g hg
    refine ⟨fun a x hx => ?_, fun x hx => ?_, fun x _ y _ => by simp⟩
    · rw [hconj, hconj, hPρ a x, ← hPρ a (g (P x)), ← map_sub]
      exact hFilG (hPFil _ (hg.1 a _ (hmemG x hx)))
    · rw [hconj, hZP x hx]; exact hFilG (hPFil _ (hg.2.1 x hx))
  have hker : ∀ g, IsKS ρ φ Fil Z g → ((∀ x ∈ Fil, g x ∈ Fil) ↔ (∀ x ∈ G, conj g x ∈ G)) := by
    intro g hg
    constructor
    · intro h x hx
      rw [hconj]; exact hFilG (hPFil _ (h _ (hmemG x hx)))
    · intro h
      have hPpart : ∀ u ∈ Fil, P (g (P u)) ∈ Fil := by
        intro u hu
        have := hmemG _ (h (P u) (hFilG (hPFil u hu)))
        rwa [hconj, hPP, hPP] at this
      have hgP : ∀ u ∈ Fil, g (P u) ∈ Fil := by
        intro u hu
        have hq : g (P u) - P (g (P u)) ∈ Fil := by
          apply hwQ
          have := hg.1 w (P u) (hPFil u hu)
          rwa [← hAdef, hPA, map_smul] at this
        have := Fil.add_mem hq (hPpart u hu)
        rwa [sub_add_cancel] at this
      intro x hx
      have hu : x - P x ∈ Fil := hQFil x hx
      have hp : P (g (x - P x)) ∈ Fil := by
        apply hwP
        have := hg.1 w (x - P x) hu
        rwa [← hAdef, hQA, map_smul] at this
      have hq : g (x - P x) - P (g (x - P x)) ∈ Fil := by
        apply hQcrit
        intro y hy
        have h1 := hg.2.2 (x - P x) hu (P y) (hPFil y hy)
        have h2 := hiso (x - P x) hu _ (hgP y hy)
        linear_combination h1 - h2
      have e : g x = g (P x) + (P (g (x - P x)) + (g (x - P x) - P (g (x - P x)))) := by
        rw [add_sub_cancel, ← map_add, add_sub_cancel]
      rw [e]
      exact Fil.add_mem (hgP x hx) (Fil.add_mem hp hq)

  have hiii : ∀ f', IsKS ρ 0 G Z f' → ∃ g, IsKS ρ φ Fil Z g ∧ ∀ x ∈ G, conj g x - f' x ∈ G := by
    intro f' hf'
    have hinj : Function.Injective φ.flip := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      apply hnd v
      intro u
      rw [hskew]
      have : φ u v = 0 := LinearMap.congr_fun hv u
      rw [this, neg_zero]
    have hsurj : Function.Surjective φ.flip :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq).symm).1 hinj
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective φ.flip (LinearMap.range_eq_top.2 hsurj)
    let L : H →ₗ[k] H := P ∘ₗ f' ∘ₗ P
    let T : H →ₗ[k] H := s ∘ₗ (-(L.dualMap ∘ₗ φ.flip))
    have hT : ∀ u v, φ u (T v) = -φ (P (f' (P u))) v := by
      intro u v
      have := LinearMap.congr_fun (LinearMap.congr_fun hs (-(L.dualMap ∘ₗ φ.flip) v)) u
      simpa [T, L] using this
    let g : H →ₗ[k] H := L + (1 - P) ∘ₗ T ∘ₗ (1 - P)
    have hg : ∀ x, g x = P (f' (P x)) + (T (x - P x) - P (T (x - P x))) := fun x => by
      simp [g, L]
    have hT0 : T 0 = 0 := map_zero T
    refine ⟨g, ⟨fun a x hx => ?_, fun z hz => ?_, fun x _ y _ => ?_⟩, fun x hx => ?_⟩
    · obtain ⟨q, hq⟩ : ∃ q, q = x - P x := ⟨_, rfl⟩
      obtain ⟨e, he⟩ : ∃ e, e = T (ρ a q) - ρ a (T q) := ⟨_, rfl⟩
      have hqF : q ∈ Fil := hq ▸ hQFil x hx
      have eq : g (ρ a x) - ρ a (g x) = P (f' (ρ a (P x)) - ρ a (f' (P x))) + (e - P e) := by
        have hq' : ρ a x - P (ρ a x) = ρ a q := by rw [hq, hPρ, ← map_sub]
        rw [hg, hg, hq', he, ← hq]
        simp only [hPρ, map_sub, map_add]
        abel
      rw [eq]
      refine Fil.add_mem (hmemG _ (hf'.1 a _ (hFilG (hPFil x hx)))) (hQcrit e fun y hy => ?_)
      set u := P y with hu
      set t := T q with ht
      have hm : P (f' (ρ (st a) u)) - ρ (st a) (P (f' u)) ∈ Fil := by
        rw [← hPρ (st a) (f' u), ← map_sub]; exact hmemG _ (hf'.1 (st a) u (hFilG (hPFil y hy)))
      have h4 := hiso _ hm q hqF
      rw [LinearMap.map_sub₂] at h4
      have F2 : φ u (T (ρ a q)) = -φ (P (f' u)) (ρ a q) := by rw [hT, hu, hPP]
      have F5 : φ (ρ (st a) u) t = -φ (P (f' (ρ (st a) u))) q := by rw [ht, hT, hu, hPρ, hPP]
      have F3 := hadj a t u
      have F7 := hadj a q (P (f' u))
      have S1 := hskew (T (ρ a q)) u
      have S2 := hskew t (ρ (st a) u)
      have S3 := hskew (P (f' u)) (ρ a q)
      have S4 := hskew q (ρ (st a) (P (f' u)))
      rw [he, LinearMap.map_sub₂]
      linear_combination S1 - F2 + S3 - F7 - S4 - F3 - S2 + F5 - h4
    · rw [hg, hZP z hz, sub_self, hT0, map_zero, sub_zero, add_zero]
      exact hmemG _ (hf'.2.1 z hz)
    · have ex : φ (g x) y = φ (P (f' (P x))) y + φ (T (x - P x) - P (T (x - P x))) y := by
        rw [hg, map_add, LinearMap.add_apply]
      have ey : φ x (g y) = φ x (P (f' (P y))) + φ x (T (y - P y) - P (T (y - P y))) := by
        rw [hg, map_add]
      have K1 := L1 (f' (P x)) y
      have K2 := L2 (T (x - P x)) y
      have K3 := L3 x (f' (P y))
      have K4 := L4 x (T (y - P y))
      have K5 := hT (P x) (y - P y)
      have K6 := hT (P y) (x - P x)
      rw [hPP] at K5 K6
      have K7 := hskew (T (x - P x)) (P y)
      have K8 := hskew (x - P x) (P (f' (P y)))
      linear_combination ex + ey + K1 + K2 + K3 + K4 + K5 + K7 - K6 + K8
    · rw [hconj, hg, hPP, sub_self, hT0, map_zero, sub_zero, add_zero, hPP]
      have hu : x - P x ∈ G := hQG x
      have hp : P (f' (x - P x)) ∈ G := hwP G _ (by
        have := hf'.1 w (x - P x) hu
        rwa [← hAdef, hQA, map_smul] at this)
      have hq1 := hQG (f' (x - P x))
      have hq2 := hQG (f' (P x))
      have e1 : f' x = f' (P x) + f' (x - P x) := by rw [← map_add, add_sub_cancel]
      have e : P (f' (P x)) - f' x = -(f' (P x) - P (f' (P x))) -
          (P (f' (x - P x)) + (f' (x - P x) - P (f' (x - P x)))) := by rw [e1]; abel
      rw [e]
      exact G.sub_mem (G.neg_mem hq2) (G.add_mem hp hq1)

  set p := ksSub ρ φ Fil Z with hp
  have hmap : p.map (cls G ∘ₗ conj) = (ksSub ρ 0 G Z).map (cls G) := by
    ext m
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨conj g, hi g hg, rfl⟩
    · rintro ⟨f', hf', rfl⟩
      obtain ⟨g, hg, hgf⟩ := hiii f' hf'
      exact ⟨g, hg, (cls_eq_iff (Fil := G) _ _).2 hgf⟩
  have hkerEq : LinearMap.ker (cls Fil ∘ₗ p.subtype) = LinearMap.ker ((cls G ∘ₗ conj) ∘ₗ p.subtype) := by
    ext ⟨g, hg⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]
    have e1 : cls Fil g = 0 ↔ ∀ x ∈ Fil, g x ∈ Fil := by
      rw [← (cls Fil).map_zero, cls_eq_iff]; simp
    have e2 : cls G (conj g) = 0 ↔ ∀ x ∈ G, conj g x ∈ G := by
      rw [← (cls G).map_zero, cls_eq_iff]; simp
    rw [e1, e2]
    exact hker g hg
  have h1 := finrank_map_add_ker p (cls Fil)
  have h2 := finrank_map_add_ker p (cls G ∘ₗ conj)
  rw [hkerEq] at h1
  rw [hmap] at h2
  have hfin : finrank k (p.map (cls Fil)) = finrank k ((ksSub ρ 0 G Z).map (cls G)) := by omega
  have hd' := KSDim.unique hd (ksDim_finrank ρ 0 G Z)
  have := ksDim_finrank ρ φ Fil Z
  rwa [← hp, hfin, ← hd'] at this

end GlobalTheory.UPel.Sm.KSCount
end
end

open GlobalTheory.UPel.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_skew_dim_semisimple_two_roots : ∀ (k : Type) (H : Type 1) (O : Type) [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (ρ : O →+* Module.End k H) (st : O → O) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (w : O) (r r' : k) (d : ℕ), Function.Surjective st → (∀ b x y, φ (ρ b x) y = φ x (ρ (st b) y)) → (∀ x y, φ x y = -φ y x) → (∀ x, (∀ y, φ x y = 0) → x = 0) → (∀ x ∈ Fil, ∀ y ∈ Fil, φ x y = 0) → 2 * Module.finrank k Fil = Module.finrank k H → (∀ a, ∀ x ∈ Fil, ρ a x ∈ Fil) → (∀ a, ρ w * ρ a = ρ a * ρ w) → (ρ w - r • 1) * (ρ w - r' • 1) = 0 → r ≠ r' → (∀ x y, φ (ρ w x) y = φ x ((r + r') • y - ρ w y)) → Z ≤ LinearMap.range (ρ w - r' • 1) → KSDim ρ 0 (Fil ⊔ LinearMap.range (ρ w - r • 1)) Z d → KSDim ρ φ Fil Z d := by
  atlas_forward_decl GlobalTheory.UPel.Sm.KSCount.ksDim_of_eigen_reduce
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_firstDeRhamHomology_hodgeFiltration_of_field : GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Hodge → ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FiniteDimensional k (HdR A) ∧ Module.finrank k (HdR A) = 2 * g ∧ Module.finrank k (Fil A) = g := by
  first | exact @GlobalTheory.finrank_HdR_Fil_of_field | exact GlobalTheory.finrank_HdR_Fil_of_field | (intros; apply GlobalTheory.finrank_HdR_Fil_of_field <;> assumption)
end

section
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

noncomputable section

namespace GlobalTheory.HTRho

theorem finrank_ksSub_map_cls_eq_homO {k O H : Type*} [Field k] [AddCommGroup H] [Module k H]
    [FiniteDimensional k H] [Ring O] (σ : O →+* Module.End k H) (G Z : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z) (hZG : Z ≤ G) :
    finrank k ((ksSub σ 0 G Z).map (cls G)) =
      finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx))
        (qAct σ G hG)) := by
  set Zc := Z.comap G.subtype
  set hom := homO (qAct (rAct σ G hG) Zc (fun a x hx => hZ a x hx)) (qAct σ G hG)
  let Ψ : hom →ₗ[k] (G →ₗ[k] H ⧸ G) := (LinearMap.lcomp k (H ⧸ G) Zc.mkQ) ∘ₗ hom.subtype
  have hΨ : ∀ S : hom, Ψ S = (S : (G ⧸ Zc) →ₗ[k] H ⧸ G) ∘ₗ Zc.mkQ := fun S => rfl
  have inj : Function.Injective Ψ := by
    intro S S' h
    rw [hΨ, hΨ] at h
    exact Subtype.ext (LinearMap.ext fun q => by
      obtain ⟨x, rfl⟩ := Zc.mkQ_surjective q
      exact LinearMap.congr_fun h x)
  have hr : LinearMap.range Ψ = (ksSub σ 0 G Z).map (cls G) := by
    apply le_antisymm
    · rintro _ ⟨S, rfl⟩
      obtain ⟨G', hG'⟩ := Submodule.exists_isCompl G
      obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective G.mkQ (Submodule.range_mkQ G)
      have hs' : ∀ q, G.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
      let T : G →ₗ[k] H ⧸ G := Ψ S
      let f : H →ₗ[k] H := s ∘ₗ T ∘ₗ Submodule.linearProjOfIsCompl G G' hG'
      have hf : ∀ x (hx : x ∈ G), G.mkQ (f x) = (S : (G ⧸ Zc) →ₗ[k] H ⧸ G) (Zc.mkQ ⟨x, hx⟩) := by
        intro x hx
        have hp : Submodule.linearProjOfIsCompl G G' hG' x = ⟨x, hx⟩ :=
          Submodule.linearProjOfIsCompl_apply_left hG' ⟨x, hx⟩
        simp only [f, LinearMap.comp_apply, hp, hs']
        rfl
      refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro a x hx
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
        change G.mkQ (f (σ a x)) = G.mkQ (σ a (f x))
        rw [hf _ (hG a x hx), ← qAct_mk σ G hG, hf x hx]
        rw [← (mem_homO _ _ _).1 S.2 a]
        rfl
      · intro x hx
        rw [← Submodule.Quotient.mk_eq_zero]
        change G.mkQ (f x) = 0
        rw [hf x (hZG hx)]
        have : Zc.mkQ ⟨x, hZG hx⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hx
        rw [this, map_zero]
      · intro x _ y _
        simp
      · apply LinearMap.ext
        rintro ⟨x, hx⟩
        exact hf x hx
    · rintro _ ⟨f, hf, rfl⟩
      have hker : Zc ≤ LinearMap.ker (cls G f) := by
        intro x hx
        rw [LinearMap.mem_ker]
        exact (Submodule.Quotient.mk_eq_zero _).2 (hf.2.1 x hx)
      let S0 := Zc.liftQ (cls G f) hker
      have hS0 : S0 ∈ hom := by
        rw [mem_homO]
        intro a q
        obtain ⟨x, rfl⟩ := Zc.mkQ_surjective q
        change S0 (Zc.mkQ (rAct σ G hG a x)) = qAct σ G hG a (S0 (Zc.mkQ x))
        simp only [S0, Submodule.liftQ_mkQ]
        change G.mkQ (f (σ a x)) = G.mkQ (σ a (f x))
        rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hf.1 a x x.2
      refine ⟨⟨S0, hS0⟩, ?_⟩
      rw [hΨ]
      exact Submodule.liftQ_mkQ _ _ _
  rw [← hr, LinearMap.finrank_range_of_inj inj]

end GlobalTheory.HTRho
end
end

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_ksSub_map_cls_eq_finrank_homO : ∀ {k O H : Type*} [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (σ : O →+* Module.End k H) (G Z : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z), Z ≤ G → finrank k ((ksSub σ 0 G Z).map (cls G)) = finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (qAct σ G hG)) := by
  atlas_forward_decl GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO
end

section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

noncomputable section

namespace GlobalTheory.HTRho.CRTSplit

variable {k O C V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [AddCommGroup V] [Module k V]

abbrev actC (τ : O →+* Module.End k V) : MonoidAlgebra k C →ₐ[k] Module.End k V :=
  MonoidAlgebra.lift k (Module.End k V) C (τ.comp (algebraMap C O)).toMonoidHom

abbrev chiC (χ : C →+* k) : MonoidAlgebra k C →ₐ[k] k :=
  MonoidAlgebra.lift k k C χ.toMonoidHom

theorem actC_apply (τ : O →+* Module.End k V) (f : MonoidAlgebra k C) (v : V) :
    actC τ f v = ∑ c ∈ f.coeff.support, f.coeff c • τ (algebraMap C O c) v := by
  rw [actC, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply]
  rfl

theorem chiC_apply (χ : C →+* k) (f : MonoidAlgebra k C) :
    chiC χ f = ∑ c ∈ f.coeff.support, f.coeff c * χ c := by
  rw [chiC, MonoidAlgebra.lift_apply, Finsupp.sum]
  rfl

theorem actC_of (τ : O →+* Module.End k V) (c : C) :
    actC τ (MonoidAlgebra.of k C c) = τ (algebraMap C O c) := by
  rw [actC, MonoidAlgebra.lift_of]; rfl

theorem chiC_of (χ : C →+* k) (c : C) : chiC χ (MonoidAlgebra.of k C c) = χ c := by
  rw [chiC, MonoidAlgebra.lift_of]; rfl

theorem actC_eq_zero {Idx : Type*} (τ : O →+* Module.End k V) (χ : Idx → C →+* k)
    (hJ : jSub τ χ ⊤ = ⊥) (f : MonoidAlgebra k C) (hf : ∀ i, chiC (χ i) f = 0) (v : V) :
    actC τ f v = 0 := by
  have hmem : actC τ f v ∈ jSub τ χ ⊤ := by
    apply Submodule.subset_span
    refine ⟨f.coeff.support.card, fun l => f.coeff (f.coeff.support.equivFin.symm l),
      fun l => (f.coeff.support.equivFin.symm l : C), v, trivial, fun i => ?_, ?_⟩
    · have h1 := Equiv.sum_comp f.coeff.support.equivFin.symm
        (fun x : f.coeff.support => f.coeff x * χ i x)
      beta_reduce at h1
      rw [h1, Finset.sum_coe_sort f.coeff.support (fun x => f.coeff x * χ i x), ← chiC_apply, hf i]
    · have h1 := Equiv.sum_comp f.coeff.support.equivFin.symm
        (fun x : f.coeff.support => f.coeff x • τ (algebraMap C O x) v)
      beta_reduce at h1
      rw [h1, Finset.sum_coe_sort f.coeff.support (fun x => f.coeff x • τ (algebraMap C O x) v),
        actC_apply]
  rw [hJ] at hmem
  simpa using hmem

theorem actC_mem_mSub (τ : O →+* Module.End k V) (χ : C →+* k) (f : MonoidAlgebra k C)
    (hf : chiC χ f = 0) (x : V) : actC τ f x ∈ mSub τ χ ⊤ := by
  have h : actC τ f x = ∑ c ∈ f.coeff.support, f.coeff c • (τ (algebraMap C O c) x - χ c • x) := by
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
    rw [actC_apply, ← Finset.sum_smul, ← chiC_apply, hf, zero_smul, sub_zero]
  rw [h]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, x, trivial, rfl⟩)

theorem actC_mSub_eq_zero {Idx : Type*} (τ : O →+* Module.End k V) (χ : Idx → C →+* k)
    (hJ : jSub τ χ ⊤ = ⊥) (i : Idx) (e : MonoidAlgebra k C) (he : ∀ l, l ≠ i → chiC (χ l) e = 0)
    (y : V) (hy : y ∈ mSub τ (χ i) ⊤) : actC τ e y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, x, -, rfl⟩ := hz
    have h2 : τ (algebraMap C O c) x - χ i c • x =
        actC τ (MonoidAlgebra.of k C c - algebraMap k _ (χ i c)) x := by
      rw [map_sub, AlgHom.commutes, actC_of, LinearMap.sub_apply, Module.algebraMap_end_apply]
    rw [h2, ← Module.End.mul_apply, ← map_mul]
    refine actC_eq_zero τ χ hJ _ (fun l => ?_) x
    rw [map_mul]
    by_cases hl : l = i
    · subst hl
      rw [map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply, sub_self,
        mul_zero]
    · rw [he l hl, zero_mul]
  | zero => simp
  | add _ _ _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
  | smul a _ _ h => rw [map_smul, h, smul_zero]

end GlobalTheory.HTRho.CRTSplit

open GlobalTheory.HTRho.CRTSplit in

theorem GlobalTheory.HTRho.finrank_homO_eq_sum_quot : ∀ {k O C Idx W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O]
    [Fintype Idx] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : Idx → C →+* k),
    Function.Injective χ → jSub τ χ ⊤ = ⊥ →
    finrank k (homO σW τ) = ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤)
      (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := by
  intro k O C Idx W V _ _ _ _ _ _ _ _ _ _ _ σW τ χ hχ hJ
  classical
  have hb : ∀ i j, ∃ b : MonoidAlgebra k C, i ≠ j → chiC (χ i) b = 1 ∧ chiC (χ j) b = 0 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    obtain ⟨c, hc⟩ := DFunLike.ne_iff.mp (hχ.ne hij)
    have hc' : χ i c - χ j c ≠ 0 := sub_ne_zero.mpr hc
    refine ⟨(χ i c - χ j c)⁻¹ • (MonoidAlgebra.of k C c - algebraMap k _ (χ j c)), fun _ => ⟨?_, ?_⟩⟩
    · rw [map_smul, map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply,
        smul_eq_mul, inv_mul_cancel₀ hc']
    · rw [map_smul, map_sub, AlgHom.commutes, chiC_of, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self, smul_zero]
  choose b hb using hb
  let e : Idx → MonoidAlgebra k C := fun i => ∏ j ∈ Finset.univ.erase i, b i j
  have he : ∀ i l, chiC (χ l) (e i) = if l = i then 1 else 0 := by
    intro i l
    simp only [e, map_prod]
    split_ifs with hl
    · subst hl; exact Finset.prod_eq_one fun j hj => (hb l j (Finset.ne_of_mem_erase hj).symm).1
    · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩) (hb i l (Ne.symm hl)).2
  have hsum : ∀ v : V, v = ∑ i, actC τ (e i) v := by
    intro v
    have h0 : actC τ (1 - ∑ i, e i) v = 0 :=
      actC_eq_zero τ χ hJ _ (fun l => by simp [map_sub, map_sum, he]) v
    rw [map_sub, map_one, map_sum, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
      sub_eq_zero] at h0
    exact h0
  let Φ : V →ₗ[k] ((i : Idx) → V ⧸ mSub τ (χ i) ⊤) := LinearMap.pi fun i => (mSub τ (χ i) ⊤).mkQ
  have hΦ : Function.Bijective Φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro v hv
      have hv' : ∀ i, v ∈ mSub τ (χ i) ⊤ := fun i => by
        have := congr_fun hv i
        simpa [Φ, Submodule.Quotient.mk_eq_zero] using this
      rw [hsum v]
      exact Finset.sum_eq_zero fun i _ =>
        actC_mSub_eq_zero τ χ hJ i (e i) (fun l hl => by rw [he, if_neg hl]) v (hv' i)
    · intro q
      choose w hw using fun i => Submodule.Quotient.mk_surjective (mSub τ (χ i) ⊤) (q i)
      refine ⟨∑ j, actC τ (e j) (w j), funext fun i => ?_⟩
      simp only [Φ, LinearMap.pi_apply, Submodule.mkQ_apply]
      rw [← hw i, Submodule.Quotient.eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_right_comm]
      refine add_mem ?_ (Submodule.sum_mem _ fun j hj => actC_mem_mSub τ (χ i) _
        (by rw [he, if_neg (Finset.ne_of_mem_erase hj).symm]) (w j))
      have h3 := actC_mem_mSub τ (χ i) (e i - 1) (by rw [map_sub, he, if_pos rfl, map_one, sub_self]) (w i)
      simpa [map_sub] using h3
  let Φe := LinearEquiv.ofBijective Φ hΦ
  let Ψ : homO σW τ →ₗ[k] ((i : Idx) → homO σW (qAct τ (mSub τ (χ i) ⊤)
      (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) :=
    LinearMap.pi fun i =>
      { toFun := fun T => ⟨(mSub τ (χ i) ⊤).mkQ ∘ₗ T.1, (mem_homO _ _ _).mpr fun a x => by
            rw [LinearMap.comp_apply, LinearMap.comp_apply, (mem_homO _ _ _).mp T.2 a x, qAct_mk]⟩
        map_add' := fun S T => by ext; simp
        map_smul' := fun c T => by ext; simp }
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro S T h
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      apply hΦ.1
      funext i
      have := congrArg (fun F => ((F i).1 x)) h
      simpa [Ψ, Φ] using this
    · intro F
      let T : W →ₗ[k] V := Φe.symm.toLinearMap ∘ₗ LinearMap.pi (fun i => (F i).1)
      have hT : ∀ x i, (mSub τ (χ i) ⊤).mkQ (T x) = (F i).1 x := fun x i =>
        congr_fun (Φe.apply_symm_apply (fun i => (F i).1 x)) i
      have hTm : T ∈ homO σW τ := by
        rw [mem_homO]
        intro a x
        apply hΦ.1
        funext i
        change (mSub τ (χ i) ⊤).mkQ (T (σW a x)) = (mSub τ (χ i) ⊤).mkQ (τ a (T x))
        rw [hT, ← qAct_mk τ _ (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)), hT,
          (mem_homO _ _ _).mp (F i).2 a x]
      refine ⟨⟨T, hTm⟩, funext fun i => Subtype.ext (LinearMap.ext fun x => ?_)⟩
      exact hT x i
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective Ψ hΨ), Module.finrank_pi_fintype]
end
end

section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterAugmentationSubspace_quotientAction_top : ∀ {k O C Idx W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [Fintype Idx] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : Idx → C →+* k), Function.Injective χ → jSub τ χ ⊤ = ⊥ → finrank k (homO σW τ) = ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤) (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := by
  first | (exact @GlobalTheory.HTRho.finrank_homO_eq_sum_quot) | (exact GlobalTheory.HTRho.finrank_homO_eq_sum_quot) | (intros; apply GlobalTheory.HTRho.finrank_homO_eq_sum_quot  <;> assumption)
end

section
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

theorem finrank_homO_eq_quot_mSub : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k),
    (∀ c, τ (algebraMap C O c) = χ c • 1) →
    finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  intro k O C W V _ _ _ _ _ _ _ _ _ _ σW τ χ hτ
  have hker : ∀ T : W →ₗ[k] V, T ∈ homO σW τ → mSub σW χ ⊤ ≤ LinearMap.ker T := by
    intro T hT
    rw [mem_homO] at hT
    refine Submodule.span_le.mpr ?_
    rintro z ⟨c, x, -, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hT, hτ, LinearMap.smul_apply,
      Module.End.one_apply, sub_self]
  let qa := qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))
  let e : homO qa τ ≃ₗ[k] homO σW τ :=
    { toFun := fun f => ⟨f.1 ∘ₗ (mSub σW χ ⊤).mkQ, by
        rw [mem_homO]
        intro a x
        have h := (mem_homO _ _ _).mp f.2 a ((mSub σW χ ⊤).mkQ x)
        change f.1 ((mSub σW χ ⊤).mkQ (σW a x)) = τ a (f.1 ((mSub σW χ ⊤).mkQ x))
        rw [← qAct_mk]
        exact h⟩
      invFun := fun T => ⟨(mSub σW χ ⊤).liftQ T.1 (hker T.1 T.2), by
        rw [mem_homO]
        intro a y
        induction y using Submodule.Quotient.induction_on with
        | H x =>
          have h := (mem_homO _ _ _).mp T.2 a x
          change (mSub σW χ ⊤).liftQ T.1 _ (qa a ((mSub σW χ ⊤).mkQ x)) = τ a ((mSub σW χ ⊤).liftQ T.1 _ ((mSub σW χ ⊤).mkQ x))
          simp only [qa, qAct_mk, Submodule.liftQ_mkQ, Submodule.mkQ_apply, Submodule.liftQ_apply]
          exact h⟩
      map_add' := fun f g => by ext; rfl
      map_smul' := fun c f => by ext; rfl
      left_inv := fun f => by
        ext y
        rfl
      right_inv := fun T => by ext; rfl }
  exact e.finrank_eq.symm

end GlobalTheory.HTRho
end

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_homO_eq_augmentationQuotient_of_scalar_character : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k), (∀ c, τ (algebraMap C O c) = χ c • 1) → finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  atlas_forward_decl GlobalTheory.HTRho.finrank_homO_eq_quot_mSub
end

section
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

theorem mSub_qAct_top {k O C : Type*} {H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C]
    [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : C →+* k) : mSub (qAct σ G hG) χ ⊤ = (mSub σ χ ⊤).map G.mkQ := by
  unfold mSub
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨c, x, -, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective G x
    refine ⟨σ (algebraMap C O c) y - χ c • y, ⟨c, y, trivial, rfl⟩, ?_⟩
    rw [map_sub, map_smul]
    rfl
  · rintro ⟨w, ⟨c, y, -, rfl⟩, rfl⟩
    refine ⟨c, G.mkQ y, trivial, ?_⟩
    rw [map_sub, map_smul, qAct_mk]

theorem quotFacts {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C]
    [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : Idx → C →+* k) :
    (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧
      ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := by
  refine ⟨fun hJ => ?_, fun i => ?_⟩
  · unfold jSub
    rw [Submodule.span_eq_bot]
    rintro z ⟨r, lam, c, x, -, hc, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective G x
    have hmem : (∑ l, lam l • σ (algebraMap C O (c l)) y) ∈ G :=
      hJ (Submodule.subset_span ⟨r, lam, c, y, trivial, hc, rfl⟩)
    have : (∑ l, lam l • qAct σ G hG (algebraMap C O (c l)) (Submodule.Quotient.mk y)) =
        G.mkQ (∑ l, lam l • σ (algebraMap C O (c l)) y) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      rfl
    rw [this, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  · rw [mSub_qAct_top]
    exact LinearEquiv.finrank_eq (Submodule.quotientQuotientEquivQuotientSup G (mSub σ (χ i) ⊤))

end GlobalTheory.HTRho
end

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_equivariantHom_eq_augmentation_quotient : ∀ {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (χ : Idx → C →+* k), (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧ ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := by
  atlas_forward_decl GlobalTheory.HTRho.quotFacts
end

section
open Module GlobalTheory.HTRho

noncomputable section

namespace GlobalTheory.HTRho.FilDim

variable {k H O C : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

theorem mSub_gen (σ : O →+* Module.End k H) (χ : C →+* k) {X : Submodule k H} (c : C) {x : H}
    (hx : x ∈ X) : σ (algebraMap C O c) x - χ c • x ∈ mSub σ χ X :=
  Submodule.subset_span ⟨c, x, hx, rfl⟩

theorem mSub_le_of_stable (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : mSub σ χ X ≤ X := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, x, hx, rfl⟩
  exact X.sub_mem (hX _ x hx) (X.smul_mem _ hx)

theorem mSub_mono (σ : O →+* Module.End k H) (χ : C →+* k) {X Y : Submodule k H} (h : X ≤ Y) :
    mSub σ χ X ≤ mSub σ χ Y := by
  refine Submodule.span_mono ?_
  rintro _ ⟨c, x, hx, rfl⟩
  exact ⟨c, x, h hx, rfl⟩

theorem jSub_mono {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) {X Y : Submodule k H}
    (h : X ≤ Y) : jSub σ χ X ≤ jSub σ χ Y := by
  refine Submodule.span_mono ?_
  rintro _ ⟨r, lam, c, x, hx, hc, rfl⟩
  exact ⟨r, lam, c, x, h hx, hc, rfl⟩

theorem jSub_le_mSub {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H)
    (i : ι) : jSub σ χ X ≤ mSub σ (χ i) X := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨r, lam, c, x, hx, hc, rfl⟩
  have e : ∑ l, lam l • σ (algebraMap C O (c l)) x
      = ∑ l, lam l • (σ (algebraMap C O (c l)) x - χ i (c l) • x) + (∑ l, lam l * χ i (c l)) • x := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, smul_smul]
    abel
  rw [e, hc i, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (mSub_gen σ (χ i) (c l) hx)

theorem jSub_gen {ι β : Type*} [Fintype β] (σ : O →+* Module.End k H) (χ : ι → C →+* k)
    {X : Submodule k H} (lam : β → k) (c : β → C) {x : H} (hx : x ∈ X)
    (h : ∀ i, ∑ l, lam l * χ i (c l) = 0) :
    ∑ l, lam l • σ (algebraMap C O (c l)) x ∈ jSub σ χ X := by
  let e := Fintype.equivFin β
  refine Submodule.subset_span ⟨Fintype.card β, lam ∘ e.symm, c ∘ e.symm, x, hx, fun i => ?_, ?_⟩
  · rw [← h i]; exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  · exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm

theorem mSub_rAct (σ : O →+* Module.End k H) (χ : C →+* k) (G : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) :
    (mSub (rAct σ G hG) χ ⊤).map G.subtype = mSub σ χ G := by
  rw [mSub, Submodule.map_span, mSub]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨c, x, _, rfl⟩, rfl⟩
    exact ⟨c, x, x.2, by simp⟩
  · rintro ⟨c, x, hx, rfl⟩
    exact ⟨_, ⟨c, ⟨x, hx⟩, trivial, rfl⟩, by simp⟩

theorem mSub_qAct {V : Type*} [AddCommGroup V] [Module k V] (τ : O →+* Module.End k V) (χ : C →+* k)
    (X : Submodule k V) (h : ∀ a, ∀ x ∈ X, τ a x ∈ X) :
    mSub (qAct τ X h) χ ⊤ = (mSub τ χ ⊤).map X.mkQ := by
  simp only [mSub]
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨c, q, _, rfl⟩
    obtain ⟨x, rfl⟩ := X.mkQ_surjective q
    exact ⟨_, ⟨c, x, trivial, rfl⟩, by simp; rfl⟩
  · rintro ⟨w, ⟨c, x, _, rfl⟩, rfl⟩
    exact ⟨c, X.mkQ x, trivial, by simp; rfl⟩

theorem exists_delta {Idx : Type*} [Fintype Idx] [DecidableEq Idx] (χ : Idx → C →+* k)
    (hχ : Function.Injective χ) (i : Idx) :
    ∃ S : Finset C, ∃ lam : C → k, ∀ j, ∑ d ∈ S, lam d * χ j d = if j = i then 1 else 0 := by
  let v : C → (Idx → k) := fun d j => χ j d
  have hmem : (Pi.single i 1 : Idx → k) ∈ Submodule.span k (Set.range v) := by
    by_contra hx
    obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hli : LinearIndependent k (fun j => ((χ j : C →* k) : C → k)) := by
      have := linearIndependent_monoidHom C k
      refine this.comp (fun j => (χ j : C →* k)) ?_
      intro a b hab
      apply hχ
      ext c
      exact DFunLike.congr_fun hab c
    have hzero : ∑ j, f (Pi.single j 1) • ((χ j : C →* k) : C → k) = 0 := by
      funext d
      have h1 : f (v d) = 0 := by
        have : f (v d) ∈ (Submodule.span k (Set.range v)).map f :=
          Submodule.mem_map_of_mem (Submodule.subset_span ⟨d, rfl⟩)
        rw [hf'] at this
        exact this
      rw [LinearMap.pi_apply_eq_sum_univ f (v d)] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [v, smul_eq_mul, MonoidHom.coe_coe]
      rw [mul_comm]
      congr 2
      funext j'
      simp [Pi.single_apply, eq_comm]
    have ha := Fintype.linearIndependent_iff.1 hli _ hzero
    apply hf
    rw [LinearMap.pi_apply_eq_sum_univ f (Pi.single i 1)]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hs : (fun j' => if j = j' then (1 : k) else 0) = Pi.single j 1 := by
      funext j'; simp [Pi.single_apply, eq_comm]
    rw [hs, ha j, smul_zero]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨c.support, c, fun j => ?_⟩
  have := congrFun hc j
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at this
  rw [this, Pi.single_apply]

theorem mSub_map_le (σ : O →+* Module.End k H) (χ : C →+* k) (T : Module.End k H)
    (hT : ∀ c z, T (σ (algebraMap C O c) z) = σ (algebraMap C O c) (T z)) :
    (mSub σ χ ⊤).map T ≤ mSub σ χ (LinearMap.range T) := by
  rw [mSub, Submodule.map_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨c, z, _, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨c, T z, ⟨z, rfl⟩, ?_⟩
  simp [hT]

theorem inf_le_sup {Idx : Type*} [Fintype Idx] (σ : O →+* Module.End k H) (χ : Idx → C →+* k)
    (hχ : Function.Injective χ) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (ω : C) (r₀ r₁ : k)
    (hr : r₀ ≠ r₁)
    (hw : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0)
    (hχω : ∀ i, χ i ω = r₀) (hR : LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) ≤ G) (i : Idx) :
    G ⊓ mSub σ (χ i) ⊤ ≤
      jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) ⊔ mSub σ (χ i) G := by
  classical
  have hA : LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) ≤ mSub σ (χ i) G := by
    rintro y ⟨z, rfl⟩
    have h0 : ((σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1)) z = 0 := by
      rw [hw]; rfl
    have e1 : σ (algebraMap C O ω) ((σ (algebraMap C O ω) - r₀ • 1) z) - r₀ • (σ (algebraMap C O ω) - r₀ • 1) z
        = (r₁ - r₀) • (σ (algebraMap C O ω) - r₀ • 1) z := by
      have : σ (algebraMap C O ω) ((σ (algebraMap C O ω) - r₀ • 1) z) - r₀ • (σ (algebraMap C O ω) - r₀ • 1) z
          = ((σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1)) z
            + (r₁ - r₀) • (σ (algebraMap C O ω) - r₀ • 1) z := by
        simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          map_sub, map_smul]
        module
      rw [this, h0, zero_add]
    have hg := mSub_gen σ (χ i) ω (hR ⟨z, rfl⟩)
    rw [hχω i, e1] at hg
    have hne : r₁ - r₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hr)
    have := Submodule.smul_mem _ (r₁ - r₀)⁻¹ hg
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hcomm : ∀ c z, (σ (algebraMap C O ω) - r₁ • 1) (σ (algebraMap C O c) z)
      = σ (algebraMap C O c) ((σ (algebraMap C O ω) - r₁ • 1) z) := by
    intro c z
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
    congr 1
    have : algebraMap C O ω * algebraMap C O c = algebraMap C O c * algebraMap C O ω := by
      rw [← map_mul, mul_comm, map_mul]
    rw [← Module.End.mul_apply, ← map_mul σ, this, map_mul σ, Module.End.mul_apply]
  rintro x ⟨hxG, hxM⟩
  have hx : x = (r₀ - r₁)⁻¹ • (σ (algebraMap C O ω) - r₁ • 1) x
      - (r₀ - r₁)⁻¹ • (σ (algebraMap C O ω) - r₀ • 1) x := by
    have hne : r₀ - r₁ ≠ 0 := sub_ne_zero.2 hr
    have : (σ (algebraMap C O ω) - r₁ • 1) x - (σ (algebraMap C O ω) - r₀ • 1) x = (r₀ - r₁) • x := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      module
    rw [← smul_sub, this, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hq : (σ (algebraMap C O ω) - r₀ • 1) x ∈ mSub σ (χ i) G := hA ⟨x, rfl⟩
  set p := (σ (algebraMap C O ω) - r₁ • 1) x with hp_def
  have hpG : p ∈ G := by
    rw [hp_def]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact G.sub_mem (hG _ x hxG) (G.smul_mem _ hxG)
  have hpR : p ∈ mSub σ (χ i) (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) :=
    mSub_map_le σ (χ i) _ hcomm (Submodule.mem_map_of_mem hxM)
  obtain ⟨S, lam, hδ⟩ := exists_delta χ hχ i
  let E : Module.End k H := ∑ d ∈ S, lam d • σ (algebraMap C O d)
  have hEapp : ∀ v, E v = ∑ d ∈ S, lam d • σ (algebraMap C O d) v := by
    intro v; simp [E, LinearMap.sum_apply]
  have hE : ∀ v ∈ mSub σ (χ i) (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)),
      E v ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, hy, rfl⟩ := hz
      have key := jSub_gen σ χ (β := S ⊕ S)
        (Sum.elim (fun d => lam d) (fun d => -(lam d * χ i c)))
        (Sum.elim (fun d => (d : C) * c) (fun d => (d : C))) hy (by
          intro j
          rw [Fintype.sum_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr, map_mul]
          rw [Finset.sum_coe_sort S (fun d => lam d * (χ j d * χ j c)),
            Finset.sum_coe_sort S (fun d => -(lam d * χ i c) * χ j d)]
          have h1 : ∑ d ∈ S, lam d * (χ j d * χ j c) = (∑ d ∈ S, lam d * χ j d) * χ j c := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun d _ => by ring
          have h2 : ∑ d ∈ S, -(lam d * χ i c) * χ j d = -(χ i c) * ∑ d ∈ S, lam d * χ j d := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
          rw [h1, h2, hδ j]
          split_ifs with h
          · subst h; ring
          · ring)
      convert key using 1
      rw [hEapp, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, map_mul, Module.End.mul_apply, neg_smul, Finset.sum_neg_distrib]
      rw [Finset.sum_coe_sort S (fun d => lam d • σ (algebraMap C O d) (σ (algebraMap C O c) y)),
        Finset.sum_coe_sort S (fun d => (lam d * χ i c) • σ (algebraMap C O d) y)]
      simp only [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib, smul_smul]
      rw [sub_eq_add_neg]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  have hpE : p - E p ∈ mSub σ (χ i) G := by
    have : p - E p = -∑ d ∈ S, lam d • (σ (algebraMap C O d) p - χ i d • p) := by
      rw [hEapp]
      simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
      rw [← Finset.sum_smul, hδ i, if_pos rfl, one_smul]
      abel
    rw [this]
    exact neg_mem (Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (mSub_gen σ (χ i) d hpG))
  have hp : p ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) ⊔ mSub σ (χ i) G := by
    have : p = E p + (p - E p) := by abel
    rw [this]
    exact Submodule.add_mem_sup (hE p hpR) hpE
  rw [hx]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hp)
    (Submodule.smul_mem _ _ (Submodule.mem_sup_right hq))

end GlobalTheory.HTRho.FilDim

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

theorem GlobalTheory.HTRho.FilDim.finrank_fildim : ∀ {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O] [Fintype Idx] [FiniteDimensional k H] (σ : O →+* Module.End k H) (χ : Idx → C →+* k), Function.Injective χ → ∀ (Fil : Submodule k H), (∀ a, ∀ x ∈ Fil, σ a x ∈ Fil) → ∀ (ω : C) (r₀ r₁ : k), r₀ ≠ r₁ → (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0 → (∀ i, χ i ω = r₀) → ∀ (hG : ∀ a, ∀ x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1), σ a x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) (hZ : ∀ a, ∀ x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)), σ a x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))), jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) → ∀ (i : Idx), let G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1); let Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)); let σW := qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx); finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) + finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) = finrank k (H ⧸ mSub σ (χ i) ⊤) := by
  intro k O C Idx H _ _ _ _ _ _ _ _ σ χ hχ Fil hFil ω r₀ r₁ hr hw hχω hG hZ hJ i G Z σW
  classical
  have hZG : Z ≤ G := (GlobalTheory.HTRho.FilDim.jSub_mono σ χ le_top).trans hJ
  have hZM : Z ≤ mSub σ (χ i) ⊤ :=
    (GlobalTheory.HTRho.FilDim.jSub_le_mSub σ χ _ i).trans (GlobalTheory.HTRho.FilDim.mSub_mono σ (χ i) le_top)
  have hmG : mSub σ (χ i) G ≤ G ⊓ mSub σ (χ i) ⊤ :=
    le_inf (GlobalTheory.HTRho.FilDim.mSub_le_of_stable σ _ G hG) (GlobalTheory.HTRho.FilDim.mSub_mono _ _ le_top)
  have heq : Z ⊔ mSub σ (χ i) G = G ⊓ mSub σ (χ i) ⊤ :=
    le_antisymm (sup_le (le_inf hZG hZM) hmG)
      (GlobalTheory.HTRho.FilDim.inf_le_sup σ χ hχ G hG ω r₀ r₁ hr hw hχω le_sup_right i)
  let N : Submodule k G := mSub (rAct σ G hG) (χ i) ⊤ ⊔ Z.comap G.subtype
  have hσW : mSub σW (χ i) ⊤ = N.map (Z.comap G.subtype).mkQ := by
    refine (GlobalTheory.HTRho.FilDim.mSub_qAct (rAct σ G hG) (χ i) (Z.comap G.subtype) _).trans ?_
    simp only [N]
    rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  have e1 : finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) = finrank k (G ⧸ N) := by
    rw [hσW]
    exact (Submodule.quotientQuotientEquivQuotient (Z.comap G.subtype) N le_sup_right).finrank_eq
  have hNmap : N.map G.subtype = G ⊓ mSub σ (χ i) ⊤ := by
    simp only [N]
    rw [Submodule.map_sup, GlobalTheory.HTRho.FilDim.mSub_rAct, Submodule.map_comap_subtype,
      inf_eq_right.2 hZG, sup_comm, heq]
  have e2 : finrank k N = finrank k ↥(G ⊓ mSub σ (χ i) ⊤) := by
    have := (Submodule.equivMapOfInjective G.subtype G.injective_subtype N).finrank_eq
    rw [hNmap] at this
    exact this
  have a1 := Submodule.finrank_quotient_add_finrank N
  have a2 := Submodule.finrank_quotient_add_finrank (G ⊔ mSub σ (χ i) ⊤)
  have a3 := Submodule.finrank_quotient_add_finrank (mSub σ (χ i) ⊤)
  have a4 := Submodule.finrank_sup_add_finrank_inf_eq G (mSub σ (χ i) ⊤)
  rw [e1]
  omega
end
end

section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_ksSub_quotient_augmentation_of_two_roots : ∀ {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O] [Fintype Idx] [FiniteDimensional k H] (σ : O →+* Module.End k H) (χ : Idx → C →+* k), Function.Injective χ → ∀ (Fil : Submodule k H), (∀ a, ∀ x ∈ Fil, σ a x ∈ Fil) → ∀ (ω : C) (r₀ r₁ : k), r₀ ≠ r₁ → (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0 → (∀ i, χ i ω = r₀) → ∀ (hG : ∀ a, ∀ x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1), σ a x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) (hZ : ∀ a, ∀ x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)), σ a x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))), jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) → ∀ (i : Idx), let G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1); let Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)); let σW := qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx); finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) + finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) = finrank k (H ⧸ mSub σ (χ i) ⊤) := by
  first | (exact @GlobalTheory.HTRho.FilDim.finrank_fildim) | (exact GlobalTheory.HTRho.FilDim.finrank_fildim) | (intros; apply GlobalTheory.HTRho.FilDim.finrank_fildim  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_finrank_deRham_quotient_character : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ i, Module.finrank k (HdR o₀.A ⧸ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤) = D.m * D.n := by
  first | (exact @GlobalTheory.HTRank.finrank_quot) | (exact GlobalTheory.HTRank.finrank_quot) | (intros; apply GlobalTheory.HTRank.finrank_quot  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_rho_part_lie_deRham_quotient : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → GlobalTheory.HTRho.jSub (GlobalTheory.HTCount.crysAct o₀) (fun i => β.comp (b.t i)) ⊤ ≤ (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ∧ ∀ i, Module.finrank k (HdR o₀.A ⧸ ((Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) ⊔ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤)) = D.m := by
  first | (exact @GlobalTheory.HTLieRho.lie_rho_quot) | (exact GlobalTheory.HTLieRho.lie_rho_quot) | (intros; apply GlobalTheory.HTLieRho.lie_rho_quot  <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.HTRho
open Module

def trAct {k O X X' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X] [AddCommGroup X'] [Module k X']
    (e : X ≃ₗ[k] X') (σ : O →+* Module.End k X) : O →+* Module.End k X' where
  toFun a := e.toLinearMap ∘ₗ σ a ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem trAct_apply {k O X X' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X] [AddCommGroup X']
    [Module k X'] (e : X ≃ₗ[k] X') (σ : O →+* Module.End k X) (a : O) (x : X') :
    trAct e σ a x = e (σ a (e.symm x)) := rfl

theorem finrank_homO_trAct {k O X Y X' Y' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup X'] [Module k X'] [AddCommGroup Y'] [Module k Y']
    (eX : X ≃ₗ[k] X') (eY : Y ≃ₗ[k] Y') (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) :
    finrank k (homO σX σY) = finrank k (homO (trAct eX σX) (trAct eY σY)) := by
  have h : (homO σX σY).map (LinearEquiv.arrowCongr eX eY).toLinearMap = homO (trAct eX σX) (trAct eY σY) := by
    ext T'
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_homO, mem_homO]
    simp only [LinearEquiv.coe_coe, LinearEquiv.arrowCongr_symm_apply, LinearMap.comp_apply, trAct_apply]
    constructor
    · intro hT a x
      have := congrArg eY (hT a (eX.symm x))
      simpa using this
    · intro hT a x
      have := hT a (eX x)
      rw [LinearEquiv.symm_apply_apply] at this
      rw [this, LinearEquiv.symm_apply_apply]
  rw [← h, LinearEquiv.finrank_map_eq]

end GlobalTheory.HTRho

namespace GlobalTheory.HTRho
open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

universe v
variable {k O C : Type*} {H : Type v} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

theorem finrank_ks_map_cls [FiniteDimensional k H] (σ : O →+* Module.End k H) (G Z : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z) (hZG : Z ≤ G) :
    finrank k ((ksSub σ 0 G Z).map (cls G)) =
      finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (qAct σ G hG)) := GlobalTheory.T.finrank_ksSub_map_cls_eq_finrank_homO σ G Z hG hZ hZG

theorem finrank_homO_crt {ι W V : Type*} [Fintype ι] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (hJ : jSub τ χ ⊤ = ⊥) :
    finrank k (homO σW τ) =
      ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤) (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := GlobalTheory.T.characterAugmentationSubspace_quotientAction_top σW τ χ hχ hJ

theorem finrank_homO_quot {W V : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V)
    (χ : C →+* k) (hτ : ∀ c, τ (algebraMap C O c) = χ c • 1) :
    finrank k (homO σW τ) =
      finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := GlobalTheory.T.finrank_homO_eq_augmentationQuotient_of_scalar_character σW τ χ hτ

theorem quot_facts {ι : Type*} (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : ι → C →+* k) :
    (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧
    ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := GlobalTheory.T.finrank_equivariantHom_eq_augmentation_quotient σ G hG χ

theorem finrank_sub_quot {ι : Type*} [Fintype ι] [FiniteDimensional k H] (σ : O →+* Module.End k H)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (Fil : Submodule k H) (hFil : ∀ a, ∀ x ∈ Fil, σ a x ∈ Fil)
    (ω : C) (r₀ r₁ : k) (hr : r₀ ≠ r₁)
    (hω : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0) (hχω : ∀ i, χ i ω = r₀)
    (hG : ∀ a, ∀ x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1),
      σ a x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
    (hZ : ∀ a, ∀ x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)),
      σ a x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)))
    (hJ : jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) (i : ι) :
    let G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)
    let Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))
    let σW := qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)
    finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) + finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) =
      finrank k (H ⧸ mSub σ (χ i) ⊤) := GlobalTheory.T.finrank_ksSub_quotient_augmentation_of_two_roots σ χ hχ Fil hFil ω r₀ r₁ hr hω hχω hG hZ hJ i

theorem count {ι : Type*} [Fintype ι] [FiniteDimensional k H] (σ : O →+* Module.End k H)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (Fil : Submodule k H) (hFil : ∀ a, ∀ x ∈ Fil, σ a x ∈ Fil)
    (ω : C) (r₀ r₁ : k) (hr : r₀ ≠ r₁)
    (hω : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0) (hχω : ∀ i, χ i ω = r₀)
    (m n : ℕ) (hm : 0 < m)
    (hrank : ∀ i, finrank k (H ⧸ mSub σ (χ i) ⊤) = m * n)
    (hJ : jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
    (hlie : ∀ i, finrank k (H ⧸ ((Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) ⊔ mSub σ (χ i) ⊤)) = m)
    (hmor : ∀ i (X Y : Type v) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y]
      [FiniteDimensional k Y] (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y),
      (∀ c, σX (algebraMap C O c) = χ i c • 1) → (∀ c, σY (algebraMap C O c) = χ i c • 1) →
      m ^ 2 * finrank k (homO σX σY) = finrank k X * finrank k Y) :
    KSDim σ 0 (Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
      (jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))) (Fintype.card ι * (n - 1)) := by
  set G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) with hGdef
  set Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) with hZdef
  have hωc : ∀ a, σ a * σ (algebraMap C O ω) = σ (algebraMap C O ω) * σ a := fun a => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hRst : ∀ r : k, ∀ a, ∀ x ∈ LinearMap.range (σ (algebraMap C O ω) - r • 1),
      σ a x ∈ LinearMap.range (σ (algebraMap C O ω) - r • 1) := by
    rintro r a _ ⟨y, rfl⟩
    refine ⟨σ a y, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hωc]
  have hG : ∀ a, ∀ x ∈ G, σ a x ∈ G := by
    intro a x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (hFil a y hy)) (Submodule.mem_sup_right (hRst r₀ a z hz))
  have hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z := jSub_stable σ χ _ (hRst r₁)
  have hZG : Z ≤ G := le_trans (Submodule.span_mono (by
    rintro z ⟨r, lam, c, x, -, hc, rfl⟩; exact ⟨r, lam, c, x, trivial, hc, rfl⟩)) hJ
  have key := GlobalTheory.UPel.Sm.KSCount.ksDim_finrank σ 0 G Z
  rw [finrank_ks_map_cls σ G Z hG hZ hZG] at key
  convert key using 1
  obtain ⟨hF1, hF2⟩ := quot_facts σ G hG χ
  rw [finrank_homO_crt _ _ χ hχ (hF1 hJ)]
  rw [← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finrank_homO_quot _ _ (χ i) (qAct_mSub_algebraMap _ (χ i))]
  have hD := finrank_sub_quot σ χ hχ Fil hFil ω r₀ r₁ hr hω hχω hG hZ hJ i
  have hM := hmor i ((G ⧸ Z.comap G.subtype) ⧸ mSub (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (χ i) ⊤)
    ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) _ _ (qAct_mSub_algebraMap _ (χ i)) (qAct_mSub_algebraMap _ (χ i))
  rw [hF2 i, hlie i] at hM
  simp only at hD
  rw [hlie i, hrank i] at hD
  have h1 := Nat.eq_sub_of_add_eq hD
  rw [h1, ← Nat.mul_sub_one] at hM
  rw [show m * (n - 1) * m = m ^ 2 * (n - 1) by ring] at hM
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) hM).symm

end GlobalTheory.HTRho

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTRho

theorem rhoCount : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → KSDim (GlobalTheory.HTCount.crysAct o₀) 0 (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β hβ
  obtain ⟨hFree, hHodge, -, -, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hA := o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A hA
  obtain ⟨hfd, -, -⟩ := GlobalTheory.T.finrank_firstDeRhamHomology_hodgeFiltration_of_field hFree hHodge k o₀.A g hA hg
  have hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : k) := fun n hn => by
    simpa using (b.unit n hn).map β
  set σ := GlobalTheory.HTCount.crysAct o₀ with hσ
  set χ : Fin D.a → (𝓞 D.F →+* k) := fun i => β.comp (b.t i) with hχdef
  have hχ : Function.Injective χ := by
    intro i j hij
    by_contra hne
    have h1 := b.comax i j hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker β := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      have := congrArg (fun f : 𝓞 D.F →+* k => f x) hij
      simp only [χ, RingHom.comp_apply] at this
      simp [RingHom.mem_ker, this]
    have h1' : (1 : R) ∈ RingHom.ker β := hle (by rw [h1]; trivial)
    simp at h1'
  have hFil : ∀ a, ∀ x ∈ Fil o₀.A, σ a x ∈ Fil o₀.A := fun a x hx => by
    haveI := o₀.act.hom a
    rw [hσ, GlobalTheory.HTCount.crysAct_apply]
    exact push_mem_Fil _ hx
  have hχω : ∀ i, χ i D.ω = β b.ρ := fun i => by simp [χ, b.t_ω]
  have hchar : ∀ n : ℕ, n.Coprime p → (n : k) ≠ 0 := fun n hn => (hunit n hn).ne_zero
  have hρk : β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k) = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  have hr : β b.ρ ≠ (D.tr : k) - β b.ρ := by
    intro h
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (-(D.tr : k) + 2 * β b.ρ) * h - 4 * hρk
    have hp : (p : ℕ).Prime := Fact.out
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => D.disc_p ?_)
      exact Int.natCast_dvd.2 hdv
    apply hchar _ hcop
    have hm := congrArg (Int.cast : ℤ → k) (Int.natAbs_mul_self' (D.tr ^ 2 - 4 * D.nm))
    rw [Int.cast_mul, Int.cast_mul, hd, mul_zero, Int.cast_natCast] at hm
    exact mul_self_eq_zero.1 hm
  have hω : (σ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) * (σ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1) = 0 := by
    have e1 : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
      rw [← D.tr_eq, ← D.nm_eq]; ring
    have e2 : σ (algebraMap (𝓞 D.F) D.O (D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F))) = 0 := by
      rw [e1]; simp
    simp only [map_add, map_sub, map_mul, map_intCast] at e2
    refine LinearMap.ext fun x => ?_
    have e3 := congrArg (fun T => T x) e2
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at e3
    simp only [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul k] at e3
    simp only [LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.zero_apply, map_sub, map_smul]
    set w := σ (algebraMap (𝓞 D.F) D.O D.ω)
    have : β b.ρ * ((D.tr : k) - β b.ρ) = D.nm := by linear_combination -hρk
    linear_combination (norm := module) e3 - hρk • x
  have hS2 := GlobalTheory.T.harrisTaylor_rho_part_lie_deRham_quotient p D R b N ‹_› ‹_› k t o₀ β hβ
  have key := count σ χ hχ (Fil o₀.A) hFil D.ω (β b.ρ) ((D.tr : k) - β b.ρ) hr hω hχω D.m D.n D.m_pos
    (GlobalTheory.T.harrisTaylor_finrank_deRham_quotient_character p D R b N ‹_› ‹_› k t o₀ β hβ) hS2.1 hS2.2
    (fun i X Y _ _ _ _ _ _ σX σY hX hY => by
      let eX := (Module.finBasis k X).equivFun
      let eY := (Module.finBasis k Y).equivFun
      rw [finrank_homO_trAct eX eY σX σY]
      have := GlobalTheory.T.finrank_hom_harrisTaylorOrder_morita p D k hchar (χ i) _ _ (trAct eX σX) (trAct eY σY)
        (fun c => LinearMap.ext fun x => by rw [trAct_apply, hX]; simp) (fun c => LinearMap.ext fun x => by rw [trAct_apply, hY]; simp)
      rwa [← eX.finrank_eq, ← eY.finrank_eq] at this)
  rw [Fintype.card_fin] at key
  exact key

end GlobalTheory.HTRho
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_rho_part_deformation_dim : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → KSDim (GlobalTheory.HTCount.crysAct o₀) 0 (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  first | (exact @GlobalTheory.HTRho.rhoCount) | (exact GlobalTheory.HTRho.rhoCount) | (intros; apply GlobalTheory.HTRho.rhoCount  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem sub_smul_mul_sub_smul_eq_zero_of_quadratic {k E : Type*} [Field k] [Ring E] [Algebra k E] (X : E) (tr nm : ℤ) (r r' : k)
    (hX : X * X = (tr : E) * X - (nm : E)) (hs : r + r' = tr) (hp : r * r' = nm) :
    (X - r • (1 : E)) * (X - r' • (1 : E)) = 0 := by
  have htr : (tr : E) = algebraMap k E r + algebraMap k E r' := by rw [← map_add, hs, map_intCast]
  have hnm : (nm : E) = algebraMap k E r * algebraMap k E r' := by rw [← map_mul, hp, map_intCast]
  rw [Algebra.smul_def, Algebra.smul_def, _root_.mul_one, _root_.mul_one, sub_mul, mul_sub, mul_sub, hX, htr, hnm,
    ← Algebra.commutes r' X]
  noncomm_ring

end GlobalTheory.HTCount

namespace GlobalTheory.HTCount

theorem ksDim_at_point : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → KSDim (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht φ hφ
  obtain ⟨hfd, hdim, hskew, hiso⟩ := GlobalTheory.T.harrisTaylor_pairing_skew_hodge_lagrangian p D R b N hN hNp k t o₀ β ht φ hφ
  have hnd := GlobalTheory.T.harrisTaylor_polarisation_pairing_nondegenerate p D R b N hN hNp k t o₀ β ht φ hφ
  have hadj := GlobalTheory.T.harrisTaylor_crystal_action_adjoint p D R b N hN hNp k t o₀ β ht φ hφ
  have hcount := GlobalTheory.T.harrisTaylor_rho_part_deformation_dim p D R b N hN hNp k t o₀ β ht
  haveI := hfd
  have hstab : ∀ a, ∀ x ∈ Fil o₀.A, crysAct o₀ a x ∈ Fil o₀.A := fun a x hx => by
    haveI := o₀.act.hom a
    rw [crysAct_apply]; exact push_mem_Fil _ hx
  have hcomm : ∀ a, crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) * crysAct o₀ a = crysAct o₀ a * crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) := fun a => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hsurj : Function.Surjective (fun c : D.O => (D.star c).unop) := fun a => ⟨(D.star a).unop, D.star_star a⟩

  have hbar : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
  have hωsq : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hw2 : algebraMap (𝓞 D.F) D.O D.ω * algebraMap (𝓞 D.F) D.O D.ω =
      (D.tr : D.O) * algebraMap (𝓞 D.F) D.O D.ω - (D.nm : D.O) := by
    rw [← map_mul, hωsq, map_sub, map_mul, map_intCast, map_intCast]
  have hstw : (D.star (algebraMap (𝓞 D.F) D.O D.ω)).unop = (D.tr : D.O) - algebraMap (𝓞 D.F) D.O D.ω := by
    rw [D.star_F, MulOpposite.unop_op, hbar, map_sub, map_intCast]
  have hrr : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this
  have hsum : β b.ρ + ((D.tr : k) - β b.ρ) = (D.tr : k) := by ring
  have hdisc : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) ≠ 0 := by
    have hp : p.Prime := Fact.out
    have hnd : ¬ p ∣ (D.tr ^ 2 - 4 * D.nm).natAbs := fun h => D.disc_p (Int.ofNat_dvd_left.2 h)
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    have hu := (b.unit _ hcop).map β
    rw [map_natCast] at hu
    intro h0
    rcases Int.natAbs_eq (D.tr ^ 2 - 4 * D.nm) with e | e
    · rw [e, Int.cast_natCast] at h0; exact hu.ne_zero h0
    · rw [e, Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h0; exact hu.ne_zero h0
  have hne : β b.ρ ≠ (D.tr : k) - β b.ρ := by
    intro h
    apply hdisc
    push_cast
    linear_combination (2 * β b.ρ - (D.tr : k)) * h + 4 * hrr
  have hZ : lieZ o₀ β ≤ LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨n, lam, c, y, ⟨y₀, rfl⟩, -, rfl⟩
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ⟨crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y₀, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply]
    congr 1
    rw [sub_mul, mul_sub, hcomm, smul_mul_assoc, mul_smul_comm, _root_.one_mul, _root_.mul_one]
  generalize lieZ o₀ β = Z at hZ hcount ⊢
  generalize crysAct o₀ = ρ at hstab hcomm hadj hcount hZ ⊢
  generalize algebraMap (𝓞 D.F) D.O D.ω = w at hw2 hstw hcomm hcount hZ
  have hq := sub_smul_mul_sub_smul_eq_zero_of_quadratic (ρ w) D.tr D.nm (β b.ρ) ((D.tr : k) - β b.ρ)
    (by rw [← map_mul, hw2, map_sub, map_mul, map_intCast, map_intCast]) hsum hrr
  have hwadj : ∀ x y, φ (ρ w x) y = φ x ((β b.ρ + ((D.tr : k) - β b.ρ)) • y - ρ w y) := fun x y => by
    rw [hadj, hstw, map_sub, map_intCast, hsum, LinearMap.sub_apply, Module.End.intCast_apply,
      Int.cast_smul_eq_zsmul]
  exact GlobalTheory.T.kodairaSpencer_skew_dim_semisimple_two_roots k (HdR o₀.A) D.O ρ (fun c => (D.star c).unop) φ (Fil o₀.A) Z w (β b.ρ) ((D.tr : k) - β b.ρ) _ hsurj
    hadj hskew hnd hiso hdim hstab hcomm hq hne hwadj hZ hcount

end GlobalTheory.HTCount
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_kodairaSpencer_directions_dim : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → KSDim (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  first | (exact @GlobalTheory.HTCount.ksDim_at_point) | (exact GlobalTheory.HTCount.ksDim_at_point) | (intros; apply GlobalTheory.HTCount.ksDim_at_point  <;> assumption)
end
