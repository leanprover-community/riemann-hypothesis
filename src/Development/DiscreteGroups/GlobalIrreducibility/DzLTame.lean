import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
import Development.DiscreteGroups.GlobalIrreducibility.DzTame
import Development.DiscreteGroups.GlobalIrreducibility.DzNormV
import Development.DiscreteGroups.GlobalIrreducibility.ContinuousResI
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.DiscreteGroups.GlobalIrreducibility.DzApprox

section
open Module Polynomial

set_option linter.all false

namespace DiscreteGroups.sglob.DzCliff

variable {W V : Type*} [Group W] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem eig_unique {f : End ℂ V} {u : V} (hu : u ≠ 0) {a b : ℂ} (ha : f u = a • u) (hb : f u = b • u) : a = b :=
  smul_left_injective ℂ hu (ha.symm.trans hb)

theorem pow_apply_of_eig {f : End ℂ V} {v : V} {c : ℂ} (hv : f v = c • v) (m : ℕ) : (f ^ m) v = c ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem rho_inv_apply (ρ : Representation ℂ W V) (a : W) (v : V) : ρ a⁻¹ (ρ a v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rho_apply_inv (ρ : Representation ℂ W V) (a : W) (v : V) : ρ a (ρ a⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rho_ne_zero (ρ : Representation ℂ W V) (a : W) {v : V} (hv : v ≠ 0) : ρ a v ≠ 0 := by
  intro h
  apply hv
  rw [← rho_inv_apply ρ a v, h, map_zero]

theorem exists_common_eigenvector (S : Set (End ℂ V)) (hS : ∀ f ∈ S, ∀ g ∈ S, f * g = g * f)
    (U : Submodule ℂ V) (hU : U ≠ ⊥) (hUS : ∀ f ∈ S, ∀ v ∈ U, f v ∈ U) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ f ∈ S, ∃ c : ℂ, f u = c • u := by
  classical
  let P : Submodule ℂ V → Prop := fun X => X ≤ U ∧ X ≠ ⊥ ∧ ∀ f ∈ S, ∀ v ∈ X, f v ∈ X
  have hex : ∃ k, ∃ X, P X ∧ finrank ℂ X = k := ⟨_, U, ⟨le_rfl, hU, hUS⟩, rfl⟩
  obtain ⟨X, hX, hXk⟩ := Nat.find_spec hex
  have hmin : ∀ Y, P Y → finrank ℂ X ≤ finrank ℂ Y := fun Y hY => hXk ▸ Nat.find_min' hex ⟨Y, hY, rfl⟩
  obtain ⟨u, huX, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX.2.1
  refine ⟨u, hX.1 huX, hu0, fun f hf => ?_⟩
  haveI : Nontrivial X := Submodule.nontrivial_iff_ne_bot.mpr hX.2.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrict (fun v hv => hX.2.2 f hf v hv))
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx' : f (x : V) = c • (x : V) := by
    have := Module.End.mem_eigenspace_iff.mp hx.1
    simpa [LinearMap.restrict_apply] using congrArg Subtype.val this
  let Y : Submodule ℂ V := X ⊓ f.eigenspace c
  have hY : P Y := by
    refine ⟨le_trans inf_le_left hX.1, ?_, fun g hg v hv => ⟨hX.2.2 g hg v hv.1, Module.End.mem_eigenspace_iff.mpr
      (by rw [← Module.End.mul_apply, hS f hf g hg, Module.End.mul_apply, Module.End.mem_eigenspace_iff.mp hv.2,
        map_smul])⟩⟩
    intro hbot
    have hxY : (x : V) ∈ Y := ⟨x.2, Module.End.mem_eigenspace_iff.mpr hx'⟩
    rw [hbot, Submodule.mem_bot] at hxY
    exact hx.2 (Subtype.ext hxY)
  have hYX : Y = X := Submodule.eq_of_le_of_finrank_le inf_le_left (hmin Y hY)
  have huY : u ∈ Y := hYX ▸ huX
  exact ⟨c, Module.End.mem_eigenspace_iff.mp huY.2⟩

theorem eq_top_of_stable (ρ : Representation ℂ W V) (hρ : ρ.IsIrreducible) (S : Submodule ℂ V) (hS : S ≠ ⊥)
    (hst : ∀ σ : W, ∀ v ∈ S, ρ σ v ∈ S) : S = ⊤ := by
  let X : Subrepresentation ρ := ⟨S, fun σ v hv => hst σ v hv⟩
  rcases hρ.eq_bot_or_eq_top X with h | h
  · exact absurd (congrArg Subrepresentation.toSubmodule h) hS
  · exact congrArg Subrepresentation.toSubmodule h

end DiscreteGroups.sglob.DzCliff
end

section
open Module Polynomial

set_option linter.all false

namespace DiscreteGroups.sglob.DzCliff

variable {W V : Type*} [Group W] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem conj_pow (ρ : Representation ℂ W V) (I : Subgroup W) [hI : I.Normal] (φ : W) (q : ℕ)
    (hfrob : ∀ t ∈ I, ρ (φ * t * φ⁻¹) = ρ t ^ q) (j : ℕ) :
    ∀ t ∈ I, ρ (φ ^ j * t * (φ ^ j)⁻¹) = ρ t ^ q ^ j := by
  induction j with
  | zero => intro t _; simp
  | succ j ih =>
    intro t ht
    have hmem : φ ^ j * t * (φ ^ j)⁻¹ ∈ I := hI.conj_mem t ht (φ ^ j)
    have e : φ ^ (j + 1) * t * (φ ^ (j + 1))⁻¹ = φ * (φ ^ j * t * (φ ^ j)⁻¹) * φ⁻¹ := by group
    rw [e, hfrob _ hmem, ih t ht, ← pow_mul, pow_succ]

theorem eig_translate (ρ : Representation ℂ W V) (I : Subgroup W) [I.Normal] (φ : W) (q : ℕ)
    (hfrob : ∀ t ∈ I, ρ (φ * t * φ⁻¹) = ρ t ^ q) {η : W → ℂ} {v : V} (hv : ∀ t ∈ I, ρ t v = η t • v) (j : ℕ) :
    ∀ t ∈ I, ρ t (ρ (φ ^ j)⁻¹ v) = η t ^ q ^ j • ρ (φ ^ j)⁻¹ v := by
  intro t ht
  have e : t * (φ ^ j)⁻¹ = (φ ^ j)⁻¹ * (φ ^ j * t * (φ ^ j)⁻¹) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, conj_pow ρ I φ q hfrob j t ht,
    pow_apply_of_eig (hv t ht), map_smul]

theorem clifford (ρ : Representation ℂ W V) (hρ : ρ.IsIrreducible) (I : Subgroup W) [hI : I.Normal] (φ : W)
    (q n : ℕ) (hn : finrank ℂ V = n) (hpos : 0 < n)
    (hgen : ∀ σ : W, ∃ k : ℤ, ∃ t ∈ I, σ = φ ^ k * t)
    (hcomm : ∀ s ∈ I, ∀ t ∈ I, ρ s * ρ t = ρ t * ρ s)
    (hfrob : ∀ t ∈ I, ρ (φ * t * φ⁻¹) = ρ t ^ q) :
    ∃ (η : W → ℂ) (u : V) (c : ℂ), u ≠ 0 ∧ (∀ t ∈ I, ρ t u = η t • u) ∧ ρ (φ ^ n) u = c • u ∧
      (∀ t ∈ I, (ρ t).charpoly = ∏ j ∈ Finset.range n, (X - C (η t ^ q ^ j))) ∧
      (∀ t ∈ I, η t ^ q ^ n = η t) ∧
      (∀ k, 0 < k → k < n → ∃ t ∈ I, η t ^ q ^ k ≠ η t) := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (hn ▸ hpos)
  obtain ⟨u0, -, hu0, hu0e⟩ := exists_common_eigenvector (ρ '' (I : Set W))
    (by rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩; exact hcomm s hs t ht) ⊤ top_ne_bot (fun _ _ _ _ => trivial)
  have hex0 : ∀ t : W, t ∈ I → ∃ c : ℂ, ρ t u0 = c • u0 := fun t ht => hu0e _ ⟨t, ht, rfl⟩
  choose! η hη using hex0
  have hsurj : ∀ k : ℕ, ∀ t ∈ I, ∃ s ∈ I, η t = η s ^ q ^ k := by
    intro k t ht
    have hs : (φ ^ k)⁻¹ * t * φ ^ k ∈ I := by
      simpa using hI.conj_mem t ht (φ ^ k)⁻¹
    refine ⟨_, hs, ?_⟩
    have e : φ ^ k * ((φ ^ k)⁻¹ * t * φ ^ k) * (φ ^ k)⁻¹ = t := by group
    have h1 := conj_pow ρ I φ q hfrob k _ hs
    rw [e] at h1
    exact eig_unique hu0 (hη t ht) (by rw [h1, pow_apply_of_eig (hη _ hs)])
  have hper_ex : ∃ d, (0 < d ∧ ∀ t ∈ I, η t ^ q ^ d = η t) ∧ d ≤ n := by
    by_contra hcon
    push Not at hcon
    let χ : Fin (n + 1) → (I → ℂ) := fun j t => η t ^ q ^ (j : ℕ)
    have hinj : Function.Injective χ := by
      intro i j hij
      by_contra hne
      wlog hlt : (i : ℕ) < j generalizing i j
      · exact this hij.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (fun h => hne (Fin.ext h.symm)))
      have key : 0 < (j : ℕ) - i ∧ ∀ t ∈ I, η t ^ q ^ ((j : ℕ) - i) = η t := by
        refine ⟨Nat.sub_pos_of_lt hlt, fun t ht => ?_⟩
        obtain ⟨s, hs, hts⟩ := hsurj i t ht
        have hij' := congrFun hij ⟨s, hs⟩
        simp only [χ] at hij'
        rw [hts, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
        exact hij'.symm
      have h2 := hcon _ key
      have hj := j.2
      omega
    let f : I → End ℂ V := fun t => ρ t
    have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j φ' => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j j.2 i i.2) φ')
    let v : Fin (n + 1) → V := fun j => ρ (φ ^ (j : ℕ))⁻¹ u0
    have hli : LinearIndependent ℂ v := by
      refine (hind.comp hinj).linearIndependent _ (fun j => ?_) (fun j => rho_ne_zero ρ _ hu0)
      simp only [Function.comp, Submodule.mem_iInf]
      intro t
      exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr
        (eig_translate ρ I φ q hfrob hη j t t.2))
    have := hli.fintype_card_le_finrank
    simp [hn] at this
  set d := Nat.find hper_ex with hd
  obtain ⟨hdper, hdn⟩ := Nat.find_spec hper_ex
  have hdmin : ∀ k, 0 < k → k < d → ∃ t ∈ I, η t ^ q ^ k ≠ η t := by
    intro k hk hkd
    by_contra hcon
    push Not at hcon
    exact Nat.find_min hper_ex hkd ⟨⟨hk, hcon⟩, by omega⟩
  let Vη : Submodule ℂ V := ⨅ t : I, Module.End.eigenspace (ρ t) (η t)
  have memVη : ∀ v, v ∈ Vη ↔ ∀ t ∈ I, ρ t v = η t • v := by
    intro v
    simp only [Vη, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    exact ⟨fun h t ht => h ⟨t, ht⟩, fun h t => h t t.2⟩
  have hu0η : u0 ∈ Vη := (memVη u0).mpr hη
  have hstab : ∀ v ∈ Vη, ρ (φ ^ d)⁻¹ v ∈ Vη := by
    intro v hv
    rw [memVη] at hv ⊢
    intro t ht
    rw [eig_translate ρ I φ q hfrob hv d t ht, hdper.2 t ht]
  have hVη : Vη ≠ ⊥ := by
    intro h
    rw [h] at hu0η
    exact hu0 ((Submodule.mem_bot ℂ).mp hu0η)
  obtain ⟨u, huη, hu, hue⟩ := exists_common_eigenvector {ρ (φ ^ d)⁻¹}
    (fun f hf g hg => by rw [Set.mem_singleton_iff.mp hf, Set.mem_singleton_iff.mp hg]) Vη hVη
    (fun f hf v hv => by rw [Set.mem_singleton_iff.mp hf]; exact hstab v hv)
  obtain ⟨c, hc⟩ := hue _ (Set.mem_singleton _)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact rho_ne_zero ρ _ hu (by rw [hc, zero_smul])
  have hcinv : ρ (φ ^ d) u = c⁻¹ • u := by
    have h1 := rho_apply_inv ρ (φ ^ d) u
    rw [hc, map_smul] at h1
    calc ρ (φ ^ d) u = c⁻¹ • (c • ρ (φ ^ d) u) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • u := by rw [h1]
  have hz : ∀ m : ℤ, ρ ((φ ^ d)⁻¹ ^ m) u = c ^ m • u := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, zpow_add_one₀ hc0, mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, Module.End.mul_apply, inv_inv, hcinv, map_smul, ih, smul_smul,
        zpow_sub_one₀ hc0, mul_comm]
  have huI : ∀ t ∈ I, ρ t u = η t • u := (memVη u).mp huη
  have hbη : ∀ j : ℕ, ∀ t ∈ I, ρ t (ρ (φ ^ j)⁻¹ u) = η t ^ q ^ j • ρ (φ ^ j)⁻¹ u :=
    fun j => eig_translate ρ I φ q hfrob huI j
  let b : Fin d → V := fun j => ρ (φ ^ (j : ℕ))⁻¹ u
  let S : Submodule ℂ V := Submodule.span ℂ (Set.range b)
  have hbS : ∀ j : Fin d, ρ (φ ^ (j : ℕ))⁻¹ u ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hpowmem : ∀ e : ℤ, ρ (φ ^ e) u ∈ S := by
    intro e
    have hd0 : (0 : ℤ) < d := by exact_mod_cast hdper.1
    have hr0 : 0 ≤ (-e) % (d : ℤ) := Int.emod_nonneg _ hd0.ne'
    have hrd : (-e) % (d : ℤ) < d := Int.emod_lt_of_pos _ hd0
    have hdec := Int.mul_ediv_add_emod (-e) d
    have hdecomp : φ ^ e = (φ ^ ((-e) % (d : ℤ)).toNat)⁻¹ * (φ ^ d)⁻¹ ^ ((-e) / (d : ℤ)) := by
      have h1 : e = -(((-e) % (d : ℤ)).toNat : ℤ) + -((d : ℤ) * ((-e) / (d : ℤ))) := by
        rw [Int.toNat_of_nonneg hr0]; omega
      conv_lhs => rw [h1]
      rw [zpow_add, zpow_neg, zpow_natCast, zpow_neg, zpow_mul, zpow_natCast, inv_zpow]
    have htn : ((-e) % (d : ℤ)).toNat < d := by omega
    rw [hdecomp, map_mul, Module.End.mul_apply, hz, map_smul]
    exact S.smul_mem _ (hbS ⟨_, htn⟩)
  have hSst : ∀ σ : W, ∀ v ∈ S, ρ σ v ∈ S := by
    intro σ v hv
    obtain ⟨k, t, ht, rfl⟩ := hgen σ
    have hle : S ≤ S.comap (ρ (φ ^ k * t)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show ρ (φ ^ k * t) (ρ (φ ^ (j : ℕ))⁻¹ u) ∈ S
      rw [map_mul, Module.End.mul_apply, hbη j t ht, map_smul, ← Module.End.mul_apply, ← map_mul]
      refine S.smul_mem _ ?_
      have e2 : φ ^ k * (φ ^ (j : ℕ))⁻¹ = φ ^ (k - (j : ℕ)) := by group
      rw [e2]
      exact hpowmem _
    exact hle hv
  have hS0 : S ≠ ⊥ := by
    intro h
    have := hbS ⟨0, hdper.1⟩
    rw [h, Submodule.mem_bot] at this
    simp at this
    exact hu this
  have hStop : S = ⊤ := eq_top_of_stable ρ hρ S hS0 hSst
  have hnd : n ≤ d := by
    have h1 := finrank_range_le_card (R := ℂ) (b := b)
    rw [Set.finrank, show Submodule.span ℂ (Set.range b) = ⊤ from hStop, finrank_top, hn] at h1
    simpa using h1
  have hdn' : d = n := le_antisymm hdn hnd
  have hcard : Fintype.card (Fin d) = finrank ℂ V := by simp [hn, hdn']
  let B := basisOfTopLeSpanOfCardEqFinrank b hStop.ge hcard
  have hB : ∀ j, B j = b j := fun j => by simp [B]
  have hchar : ∀ t ∈ I, (ρ t).charpoly = ∏ j ∈ Finset.range d, (X - C (η t ^ q ^ j)) := by
    intro t ht
    rw [← LinearMap.charpoly_toMatrix (ρ t) B]
    have hM : LinearMap.toMatrix B B (ρ t) = Matrix.diagonal (fun j : Fin d => η t ^ q ^ (j : ℕ)) := by
      ext i j
      rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, hB j]
      show B.repr (ρ t (ρ (φ ^ (j : ℕ))⁻¹ u)) i = _
      rw [hbη j t ht, map_smul]
      have hBj : ρ (φ ^ (j : ℕ))⁻¹ u = B j := (hB j).symm
      rw [hBj, B.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [hM, Matrix.charpoly_diagonal, Fin.prod_univ_eq_prod_range (fun j => X - C (η t ^ q ^ j)) d]
  refine ⟨η, u, c⁻¹, hu, huI, by rw [← hdn']; exact hcinv, fun t ht => by rw [← hdn']; exact hchar t ht,
    fun t ht => by rw [← hdn']; exact hdper.2 t ht, fun k hk hkn => hdmin k hk (by omega)⟩

end DiscreteGroups.sglob.DzCliff
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_eigenChar {H W V : Type*} [Group H] [Group W] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ W V) (f : H →* W) {u : V} (hu : u ≠ 0) (hex : ∀ s, ∃ e : ℂ, ρ (f s) u = e • u) :
    ∃ χ : H →* ℂˣ, ∀ s, ρ (f s) u = ((χ s : ℂˣ) : ℂ) • u := by
  choose e he using hex
  have hne : ∀ s, e s ≠ 0 := fun s h0 => DzCliff.rho_ne_zero ρ (f s) hu (by rw [he s, h0, zero_smul])
  refine ⟨{ toFun := fun s => Units.mk0 (e s) (hne s), map_one' := ?_, map_mul' := ?_ }, fun s => he s⟩
  · ext
    simp only [Units.val_mk0, Units.val_one]
    exact DzCliff.eig_unique hu (he 1) (by rw [map_one, map_one, Module.End.one_apply, one_smul])
  · intro s t
    ext
    simp only [Units.val_mk0, Units.val_mul]
    exact DzCliff.eig_unique hu (he (s * t))
      (by rw [map_mul, map_mul, Module.End.mul_apply, he t, map_smul, he s, smul_smul, mul_comm])

theorem lTame : LTame := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' i hi n hn hg hN a' ha' K _ _ red hr hk y hirr htame hdim
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hq' : normV w' = normV w ^ n := by rw [hq, hN]
  obtain ⟨m, a, hya, hirr_a⟩ := hirr
  obtain ⟨m2, a2, hya2, htame2⟩ := htame
  have hiso : a2.Iso a := WD.mk_eq_mk.mp (hya2.trans hya.symm)
  have htame_a : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1 :=
    fun σ hσ => hiso.ρ_eq_one (htame2 σ hσ)
  have hdim_a : finrank ℂ (Fin m → ℂ) = n := by rw [← hdim, ← hya, WD.lpDim_mk]
  let I : Subgroup (Weil h) := (Ine (F := E) A).comap (Weil h).subtype
  haveI hInorm : I.Normal := ⟨fun t ht g0 => by
    show ((g0 * t * g0⁻¹ : Weil h) : G E Ω) ∈ Ine (F := E) A
    exact conj_mem_Ine (Weil_le_Dec h g0.2) ht⟩
  have hgen : ∀ σ : Weil h, ∃ k : ℤ, ∃ t ∈ I, σ = frob h ^ k * t := fun σ => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    exact ⟨deg σ, ineIncl h τ, τ.2, hτ⟩
  have hcomm : ∀ s ∈ I, ∀ t ∈ I, a.ρ s * a.ρ t = a.ρ t * a.ρ s := by
    intro s hs t ht
    let s' : Ine (F := E) A := ⟨s, hs⟩
    let t' : Ine (F := E) A := ⟨t, ht⟩
    have h1 : a.ρ (ineIncl h (s' * t' * s'⁻¹ * t'⁻¹)) = 1 := htame_a _ (isWild_commutator s' t')
    have h2 : ineIncl h (s' * t' * s'⁻¹ * t'⁻¹) = s * t * s⁻¹ * t⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  have hfrob : ∀ t ∈ I, a.ρ (frob h * t * (frob h)⁻¹) = a.ρ t ^ normV w := by
    intro t ht
    let t' : Ine (F := E) A := ⟨t, ht⟩
    let c' : Ine (F := E) A :=
      ⟨(frob h : G E Ω) * t' * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 t'.2⟩
    have h1 : a.ρ (ineIncl h (c' * (t' ^ normV w)⁻¹)) = 1 :=
      htame_a _ (isWild_frob (isFrob_frob (h := h)) t')
    have h2 : ineIncl h (c' * (t' ^ normV w)⁻¹) = frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : frob h * t * (frob h)⁻¹ = (frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹) * t ^ normV w := by group
    rw [e, map_mul, h1, one_mul, map_pow]
  obtain ⟨η, u, c, hu, huI, hφn, hchar, hper, hmin⟩ :=
    DzCliff.clifford a.ρ hirr_a I (frob h) (normV w) n hdim_a hn hgen hcomm hfrob
  have hc0 : c ≠ 0 := fun h0 => DzCliff.rho_ne_zero a.ρ (frob h ^ n) hu (by rw [hφn, h0, zero_smul])
  have hcinv : a.ρ (frob h ^ n)⁻¹ u = c⁻¹ • u := by
    have h1 := DzCliff.rho_inv_apply a.ρ (frob h ^ n) u
    rw [hφn, map_smul] at h1
    calc a.ρ (frob h ^ n)⁻¹ u = c⁻¹ • (c • a.ρ (frob h ^ n)⁻¹ u) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • u := by rw [h1]
  have hz : ∀ k : ℤ, a.ρ ((frob h ^ n) ^ k) u = c ^ k • u := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, Module.End.mul_apply, hφn, map_smul, ih, smul_smul, zpow_add_one₀ hc0, mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, Module.End.mul_apply, hcinv, map_smul, ih, smul_smul, zpow_sub_one₀ hc0,
        mul_comm]
  have hex : ∀ σ : Weil h', ∃ e : ℂ, a.ρ (resW h h' hq' σ) u = e • u := by
    intro σ
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (resW h h' hq' σ)
    rw [hτ, deg_resW, map_mul, Module.End.mul_apply, huI (ineIncl h τ) τ.2, map_smul,
      show frob h ^ ((n : ℤ) * deg σ) = (frob h ^ n) ^ deg σ by rw [zpow_mul, zpow_natCast], hz, smul_smul]
    exact ⟨_, rfl⟩
  obtain ⟨η', hη'⟩ := exists_eigenChar a.ρ (resW h h' hq') hu hex
  have hval : ∀ t : Ine (F := E') A, ((η' (ineIncl h' t) : ℂˣ) : ℂ) = η (ineIncl h (resI t)) := fun t =>
    DzCliff.eig_unique hu (hη' _) (by rw [resW_ineIncl]; exact huI (ineIncl h (resI t)) (resI t).2)
  have hsm : IsSmooth η' := by
    refine IsSmooth.of_open (U := resI ⁻¹' {s : Ine (F := E) A | a.ρ (ineIncl h s) = 1})
      (IsOpen.preimage continuous_resI a.smooth) (by simp) ?_
    intro t ht
    have h1 : a.ρ (resW h h' hq' (ineIncl h' t)) u = (1 : ℂ) • u := by
      rw [resW_ineIncl, ht, Module.End.one_apply, one_smul]
    exact Units.ext (DzCliff.eig_unique hu (hη' _) h1)
  have hηN : ∀ t : Ine (F := E') A, η' (ineIncl h' t) ^ (g ^ n - 1) = 1 := by
    intro t
    have hp := hper (ineIncl h (resI t)) (resI t).2
    rw [hq] at hp
    have hs0 : η (ineIncl h (resI t)) ≠ 0 := by rw [← hval]; exact Units.ne_zero _
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hval, Units.val_one]
    have h1 : η (ineIncl h (resI t)) ^ (g ^ n - 1) * η (ineIncl h (resI t)) = 1 * η (ineIncl h (resI t)) := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos), hp, one_mul]
    exact mul_right_cancel₀ hs0 h1
  obtain ⟨ξ, hξ⟩ := exists_resChar g A w' h' n hn hN a' ha' K red hr hk η' hsm hηN
  refine ⟨ξ, ?_, ?_⟩
  · intro i0 j0 hi0 hj0 hij
    by_contra hne
    wlog hlt : i0 < j0 generalizing i0 j0
    · exact this j0 i0 hj0 hi0 hij.symm (Ne.symm hne) (by omega)
    obtain ⟨s, hsI, hs⟩ := hmin (j0 - i0) (by omega) (by omega)
    obtain ⟨t0, ht0, hres⟩ := ine_lift g A w h w' h' n hn hg hN (s : G E Ω) hsI
    let t : Ine (F := E') A := ⟨t0, ht0⟩
    have hts : ineIncl h (resI t) = s := Subtype.ext hres
    have hunit : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1 := by
      have h1 := ha'.ord_eq (ineIncl h' t)
      rw [GlobalTheory.SmGL.SphCompletion.ord_completion, deg_ineIncl] at h1
      have hv0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0 := by
        rw [Ne, Valuation.zero_iff]; exact Units.ne_zero _
      have hl : WithZero.log (Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E')) = 0 := by
        simpa using h1
      rw [← WithZero.exp_log hv0, hl, WithZero.exp_zero]
    obtain ⟨x, hx⟩ := exists_int_approx_compl w' _ hunit.le
    have hxw : red x ≠ 0 := by
      intro h0
      have hxm : x ∈ w'.asIdeal := by rw [← hk, RingHom.mem_ker]; exact h0
      have hvx : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
        have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
        rw [e]
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E') w' x).mpr hxm
      have hlt1 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') < 1 := by
        have e : ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') =
            (((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') -
              algebraMap E' (w'.adicCompletion E') (x : E')) + algebraMap E' (w'.adicCompletion E') (x : E') := by ring
        rw [e]
        exact Valuation.map_add_lt _ hx hvx
      rw [hunit] at hlt1
      exact lt_irrefl _ hlt1
    have hξz := hξ t x (Units.mk0 (red x) hxw) rfl hx
    have h1 : (ξ (Units.mk0 (red x) hxw)) ^ g ^ i0 = (ξ (Units.mk0 (red x) hxw)) ^ g ^ j0 := by
      have := congrArg (fun χ : Kˣ →* ℂˣ => χ (Units.mk0 (red x) hxw)) hij
      simpa using this
    rw [hξz] at h1
    have h2 : ((η' (ineIncl h' t) : ℂˣ) : ℂ) ^ g ^ i0 = ((η' (ineIncl h' t) : ℂˣ) : ℂ) ^ g ^ j0 := by
      have := congrArg Units.val h1
      simpa only [Units.val_pow_eq_pow_val] using this
    rw [hval, hts] at h2
    have hp := hper s hsI
    rw [hq] at hp hs
    apply hs
    calc η s ^ g ^ (j0 - i0) = (η s ^ g ^ n) ^ g ^ (j0 - i0) := by rw [hp]
      _ = η s ^ (g ^ n * g ^ (j0 - i0)) := by rw [← pow_mul]
      _ = η s ^ (g ^ j0 * g ^ (n - i0)) := by
          rw [← pow_add, ← pow_add]; congr 2; omega
      _ = (η s ^ g ^ j0) ^ g ^ (n - i0) := by rw [pow_mul]
      _ = (η s ^ g ^ i0) ^ g ^ (n - i0) := by rw [h2]
      _ = η s ^ (g ^ i0 * g ^ (n - i0)) := by rw [← pow_mul]
      _ = η s ^ g ^ n := by rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hi0)]
      _ = η s := hp
  · intro t x z hxz hv
    have hξz := hξ t x z hxz hv
    rw [WD.inePol_of_mem_Ine y (res_mem_Ine t.2), ← hya, WD.charPol_mk]
    rw [show ineIncl h ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩ = ineIncl h (resI t) from rfl,
      hchar (ineIncl h (resI t)) (resI t).2, hq]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow ξ, Units.val_pow_eq_pow_val, hξz, hval]

end DiscreteGroups.sglob.DzType

end
end
