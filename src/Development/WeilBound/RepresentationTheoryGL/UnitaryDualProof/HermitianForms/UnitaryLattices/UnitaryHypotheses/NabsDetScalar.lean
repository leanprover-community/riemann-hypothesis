import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.UnipBLeColFixOne
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.QIterSurjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem

section
noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lat

variable (k) in

def lat0 (m : ℕ) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ valuation k ((1 : kˣ) : k)}
  add_mem' := fun {a b} ha hb i => by
    show valuation k (a i + b i) ≤ _
    exact ((valuation k).map_add _ _).trans (max_le (ha i) (hb i))
  zero_mem' := fun i => by simp
  neg_mem' := fun {a} ha i => by
    show valuation k (-(a i)) ≤ _
    rw [Valuation.map_neg]
    exact ha i

theorem coe_standard_lattice (m : ℕ) : (lat0 k m : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => cball (1 : kˣ) := by
  ext x
  simp only [Set.mem_univ_pi, cball, Set.mem_setOf_eq]
  exact Iff.rfl

theorem isLattice_standard_lattice (m : ℕ) : IsLat (lat0 k m) := by
  unfold IsLat
  rw [coe_standard_lattice]
  exact ⟨isCompact_univ_pi fun _ => isCompact_cball _, isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball _⟩

theorem isLat_sup {m : ℕ} {A₁ A₂ : AddSubgroup (Fin (m + 1) → k)} (h1 : IsLat A₁) (h2 : IsLat A₂) :
    IsLat (A₁ ⊔ A₂) := by
  unfold IsLat at *
  rw [AddSubgroup.add_normal]
  exact ⟨h1.1.add h2.1, h2.2.add_left⟩

end Lat

section Transport

variable {ψ : AddChar k Circle} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem kills_congr {a b : ℕ} (hab : a = b) {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : Kills ψ π a B) : Kills ψ π b B := by
  subst hab; exact h

theorem mirEq_congr {a b : ℕ} (hab : a = b) {ha : a + 1 ≤ N} {hb : b + 1 ≤ N} {s t : ℝ} (hst : s = t)
    {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : MirEq π a ha s B) : MirEq π b hb t B := by
  subst hab; subst hst; exact h

theorem lvl_congr {a b : ℕ} (hab : a = b) {ha : a + 2 ≤ N} {hb : b + 2 ≤ N} {s t : ℝ} (hst : s = t)
    {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : Lvl k ψ π a ha s B) : Lvl k ψ π b hb t B := by
  subst hab; subst hst; exact h

theorem isDens_smul {m : ℕ} {h : m + 2 ≤ N} {A₀ : AddSubgroup (Fin (m + 1) → k)} {B B' I C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hB : IsDens ψ h π A₀ B B') (hI : IsDens ψ h π A₀ I C) (c : ℂ) (hIc : ∀ v w, I v w = c * B v w) :
    ∀ v w, C v w = c * B' v w := by
  intro v w
  obtain ⟨A₁, hA₁, -, hB1⟩ := hB v w
  obtain ⟨A₂, hA₂, -, hI2⟩ := hI v w
  have hL := isLat_sup hA₁ hA₂
  rw [hI2 _ hL le_sup_right, hB1 _ hL le_sup_left, hIc]
  ring

end Transport

section Chain

open Classical in

def chain (hUD : UDens k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : ℕ → (V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  | 0 => B
  | d + 1 =>
    if h : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) then
      Classical.choose (hUD ψ hψc hψ1 (N - 2 - d) N (by obtain ⟨hN, -⟩ := h; omega) V π hs (d : ℝ)
        (chain hUD hψc hψ1 π hs B d) h.2
        (lat0 k (N - 2 - d)) (isLattice_standard_lattice _))
    else 0

variable (hUD : UDens k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ} {V : Type}
  [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

theorem chain_zero : chain hUD hψc hψ1 π hs B 0 = B := rfl

theorem chain_succ (d : ℕ) (hN : d + 2 ≤ N)
    (hL : Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d)) :
    IsDens ψ (by omega : N - 2 - d + 2 ≤ N) π (lat0 k (N - 2 - d)) (chain hUD hψc hψ1 π hs B d)
        (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      IsPsd (chain hUD hψc hψ1 π hs B (d + 1)) ∧ Kills ψ π (N - 2 - d + 1) (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      MirEq π (N - 2 - d) (by omega) ((d : ℝ) + 1) (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      (∀ v, chain hUD hψc hψ1 π hs B (d + 1) v v = 0 →
        v ∈ twKer π (derUnip k N (N - 2 - d + 1)) (lvlChar k ψ N (N - 2 - d + 1)) ⊔
          LinearMap.ker (chain hUD hψc hψ1 π hs B d)) := by
  have hh : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) := ⟨hN, hL⟩
  simp only [chain, dif_pos hh]
  exact Classical.choose_spec (hUD ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ)
    (chain hUD hψc hψ1 π hs B d) hL (lat0 k (N - 2 - d)) (isLattice_standard_lattice _))

theorem isPsd_of_inv (hB : IsInvForm π B) : IsPsd B := by
  obtain ⟨h1, h2, -⟩ := hB
  unfold IsPsd
  refine ⟨h1, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (h2 v hv).le

theorem chain_lvl (hB : IsInvForm π B) :
    ∀ d (hd : d + 2 ≤ N), Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d)
  | 0, hd => by
    refine ⟨isPsd_of_inv π B hB, ?_, ?_⟩
    · refine kills_congr (a := N) (by omega) ?_
      intro v hv w
      rw [twKer_derUnip_self ψ π] at hv
      rw [(Submodule.mem_bot ℂ).1 hv]
      simp
    · intro p _ v w
      simp [chain_zero, hB.2.2]
  | d + 1, hd => by
    obtain ⟨h1, h2, h3, h4, -⟩ := chain_succ hUD hψc hψ1 π hs B d (by omega) (chain_lvl hB d (by omega))
    exact ⟨h2, kills_congr (by omega) h3, mirEq_congr (by omega) (by push_cast; ring) h4⟩

end Chain

end PositivityTheory.RgUd.Form.U.Asm
end
end

section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blkAt_self (N : ℕ) (h : N ≤ N) (g : GL (Fin N) k) : blkAt k N N h g = g := by
  ext a b
  rw [blkAt_apply]
  simp [a.2, b.2]

open Classical in

def atom (hUD : UDens k) (hUA : UAtom k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (d : ℕ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  if h : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) then
    Classical.choose (hUA ψ hψc hψ1 (N - 2 - d) N (by obtain ⟨hN, -⟩ := h; omega) V π hs (d : ℝ)
      (chain hUD hψc hψ1 π hs B d) h.2)
  else 0

variable (hUD : UDens k) (hUA : UAtom k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

theorem atom_spec (d : ℕ) (hN : d + 2 ≤ N)
    (hL : Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d)) :
    IsAtom (by omega : N - 2 - d + 2 ≤ N) π (chain hUD hψc hψ1 π hs B d) (atom hUD hUA hψc hψ1 π hs B d) ∧
      IsPsd (atom hUD hUA hψc hψ1 π hs B d) ∧
      (∀ v, (atom hUD hUA hψc hψ1 π hs B d v v).re ≤ (chain hUD hψc hψ1 π hs B d v v).re) ∧
      (∀ v ∈ DerKer k ψ π (N - 2 - d), ∀ w, atom hUD hUA hψc hψ1 π hs B d v w = 0) ∧
      GLEq k π (N - 2 - d) (by omega) (d : ℝ) (atom hUD hUA hψc hψ1 π hs B d) ∧
      MirEq π (N - 2 - d + 1) (by omega) (d : ℝ) (atom hUD hUA hψc hψ1 π hs B d) := by
  have hh : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) := ⟨hN, hL⟩
  have e : atom hUD hUA hψc hψ1 π hs B d = Classical.choose (hUA ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ)
      (chain hUD hψc hψ1 π hs B d) hL) := by
    rw [atom, dif_pos hh]
  rw [e]
  exact Classical.choose_spec (hUA ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ) (chain hUD hψc hψ1 π hs B d) hL)

theorem lift (hUL : ULift k) (hTB : ThmB k) (hirr : π.IsIrreducible) (hB : IsInvForm π B) :
    ∀ d (hd : d + 1 ≤ N) (C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsPsd C → Kills ψ π (N - d) C →
      MirEq π (N - d - 1) (by omega) (d : ℝ) C →
      (∀ v, (C v v).re ≤ (chain hUD hψc hψ1 π hs B d v v).re) →
      ∃ c : ℂ, ∀ v w, C v w = c * chain hUD hψc hψ1 π hs B d v w
  | 0, hd, C, _, _, hC3, _ => by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hM : MirEq π n (by omega) ((0 : ℕ) : ℝ) C := mirEq_congr (by omega) rfl hC3
    refine hTB n V π hs hirr B hB C fun p hp v w => ?_
    have := hM p hp v w
    rw [blkAt_self] at this
    simpa using this
  | d + 1, hd, C, hC1, hC2, hC3, hC4 => by
    have hL := chain_lvl hUD hψc hψ1 π hs B hB d (by omega)
    obtain ⟨hD, -⟩ := chain_succ hUD hψc hψ1 π hs B d (by omega) hL
    obtain ⟨I, hIL, hIle, hID, -⟩ := hUL ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ)
      (chain hUD hψc hψ1 π hs B d) (chain hUD hψc hψ1 π hs B (d + 1)) C (lat0 k (N - 2 - d)) hL (isLattice_standard_lattice _) hD hC1
      (kills_congr (by omega) hC2) (mirEq_congr (by omega) (by push_cast; ring) hC3) hC4
    obtain ⟨c, hc⟩ := lift hUL hTB hirr hB d (by omega) I hIL.1 (kills_congr (by omega) hIL.2.1)
      (mirEq_congr (by omega) rfl hIL.2.2) hIle
    exact ⟨c, isDens_smul hD hID c hc⟩

theorem chain_rad (hB : IsInvForm π B) :
    ∀ d (hd : d + 1 ≤ N) v, chain hUD hψc hψ1 π hs B d v v = 0 →
      v ∈ twKer π (derUnip k N (N - d)) (lvlChar k ψ N (N - d))
  | 0, _, v, hv => by
    have : v = 0 := by
      by_contra hne
      have := hB.2.1 v hne
      rw [chain_zero] at hv
      rw [hv] at this
      simp at this
    rw [this]
    exact zero_mem _
  | d + 1, hd, v, hv => by
    have hL := chain_lvl hUD hψc hψ1 π hs B hB d (by omega)
    obtain ⟨-, -, -, -, hR⟩ := chain_succ hUD hψc hψ1 π hs B d (by omega) hL
    have hmem := hR v hv
    have e : N - 2 - d + 1 = N - (d + 1) := by omega
    rw [e] at hmem
    suffices hle : LinearMap.ker (chain hUD hψc hψ1 π hs B d) ≤
        twKer π (derUnip k N (N - (d + 1))) (lvlChar k ψ N (N - (d + 1))) from (sup_le le_rfl hle) hmem
    intro x hx
    have hx0 : chain hUD hψc hψ1 π hs B d x x = 0 := by
      rw [LinearMap.mem_ker] at hx
      rw [hx]
      rfl
    have hK := chain_rad hB d (by omega) x hx0
    rw [lvlChar_def] at hK ⊢
    exact twKer_derUnip_le ψ π (a := N - d) (b := N - (d + 1)) (x := N - d - 1) (y := N - (d + 1) - 1)
      (by omega) (by omega) (by omega) hK

theorem atom_prop (hUL : ULift k) (hTB : ThmB k) (hirr : π.IsIrreducible) (hB : IsInvForm π B) (d : ℕ)
    (hd : d + 2 ≤ N) : ∃ c : ℂ, ∀ v w, atom hUD hUA hψc hψ1 π hs B d v w = c * chain hUD hψc hψ1 π hs B d v w := by
  have hL := chain_lvl hUD hψc hψ1 π hs B hB d hd
  obtain ⟨-, hA1, hA2, hA3, -, hA5⟩ := atom_spec hUD hUA hψc hψ1 π hs B d hd hL
  refine lift hUD hψc hψ1 π hs B hUL hTB hirr hB d (by omega) _ hA1 ?_ (mirEq_congr (by omega) rfl hA5) hA2
  intro v hv w
  refine hA3 v ?_ w
  simp only [DerKer]
  rw [lvlChar_def] at hv
  rw [derChar_def]
  exact twKer_derUnip_le ψ π (a := N - d) (b := N - 2 - d + 1) (x := N - d - 1) (y := N - 2 - d + 1)
    (by omega) (by omega) (by omega) hv

theorem atom_eq_zero (hUS : USplit k) (hUL : ULift k) (hTB : ThmB k) (hirr : π.IsIrreducible) (hB : IsInvForm π B)
    (d : ℕ) (hd : d + 2 ≤ N) (hne : ∃ v, chain hUD hψc hψ1 π hs B (d + 1) v v ≠ 0) :
    ∀ v w, atom hUD hUA hψc hψ1 π hs B d v w = 0 := by
  have hL := chain_lvl hUD hψc hψ1 π hs B hB d hd
  obtain ⟨hAt, -⟩ := atom_spec hUD hUA hψc hψ1 π hs B d hd hL
  obtain ⟨hD, -⟩ := chain_succ hUD hψc hψ1 π hs B d hd hL
  obtain ⟨c, hc⟩ := atom_prop hUD hUA hψc hψ1 π hs B hUL hTB hirr hB d hd
  have h0 := (hUS ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ) (chain hUD hψc hψ1 π hs B d)
    (atom hUD hUA hψc hψ1 π hs B d) (chain hUD hψc hψ1 π hs B (d + 1)) (lat0 k (N - 2 - d)) hL (isLattice_standard_lattice _)
    hAt hD).2 c hc hne
  intro v w
  rw [hc, h0, zero_mul]

theorem atom_eq_self (hUS : USplit k) (hB : IsInvForm π B) (d : ℕ) (hd : d + 2 ≤ N)
    (h0 : ∀ v, chain hUD hψc hψ1 π hs B (d + 1) v v = 0) :
    atom hUD hUA hψc hψ1 π hs B d = chain hUD hψc hψ1 π hs B d := by
  have hL := chain_lvl hUD hψc hψ1 π hs B hB d hd
  obtain ⟨hAt, -⟩ := atom_spec hUD hUA hψc hψ1 π hs B d hd hL
  obtain ⟨hD, -⟩ := chain_succ hUD hψc hψ1 π hs B d hd hL
  exact (hUS ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ) (chain hUD hψc hψ1 π hs B d)
    (atom hUD hUA hψc hψ1 π hs B d) (chain hUD hψc hψ1 π hs B (d + 1)) (lat0 k (N - 2 - d)) hL (isLattice_standard_lattice _)
    hAt hD).1 h0

end PositivityTheory.RgUd.Form.U.Asm
end
end

section
noncomputable section

open GlobalTheory.PRep

namespace PositivityTheory.RgUd.Form.U.Asm

theorem mem_fixed_iff_irr {G D : Type} [Group G] [AddCommGroup D] [Module ℂ D] (ρ : Representation ℂ G D)
    (K : Subgroup G) (v : D) : v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by
  change (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

theorem exists_orth_of_finset {D : Type} [AddCommGroup D] [Module ℂ D] (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re) (s : Finset D) :
    ∀ u : D, ∃ w ∈ Submodule.span ℂ (s : Set D), ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - w) m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro u
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    intro m hm
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hm
    simp [hm]
  | insert a s ha ih =>
    intro u
    obtain ⟨wa, hwa, hwa'⟩ := ih a
    obtain ⟨wu, hwu, hwu'⟩ := ih u
    obtain ⟨a', ha'⟩ : ∃ a' : D, a' = a - wa := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = B (u - wu) a' / B a' a' := ⟨_, rfl⟩
    have hsub : Submodule.span ℂ (s : Set D) ≤ Submodule.span ℂ ((insert a s : Finset D) : Set D) :=
      Submodule.span_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    have hamem : a ∈ Submodule.span ℂ ((insert a s : Finset D) : Set D) :=
      Submodule.subset_span (by simp)
    refine ⟨wu + c • a', ?_, ?_⟩
    · rw [ha']
      exact Submodule.add_mem _ (hsub hwu) (Submodule.smul_mem _ _ (Submodule.sub_mem _ hamem (hsub hwa)))
    · have hexp : ∀ m, B (u - (wu + c • a')) m = B (u - wu) m - c * B a' m := by
        intro m
        rw [show u - (wu + c • a') = (u - wu) - c • a' by abel, map_sub, map_smul,
          LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      have hs : ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - (wu + c • a')) m = 0 := by
        intro m hm
        rw [hexp, hwu' m hm, ha', hwa' m hm, mul_zero, sub_zero]
      have key : ∀ m ∈ ((insert a s : Finset D) : Set D), B (u - (wu + c • a')) m = 0 := by
        intro m hm
        rw [Finset.coe_insert, Set.mem_insert_iff] at hm
        rcases hm with hm | hm
        · have hsplit : m = a' + wa := by rw [hm, ha']; abel
          rw [hsplit, map_add, hs wa hwa, add_zero, hexp]
          by_cases h0 : B a' a' = 0
          · have h0' : a' = 0 := by
              by_contra hne
              have := hBp a' hne
              rw [h0] at this
              simp at this
            simp [h0']
          · rw [hc, div_mul_cancel₀ _ h0, sub_self]
        · exact hs m (Submodule.subset_span hm)
      intro m hm
      have hle : Submodule.span ℂ ((insert a s : Finset D) : Set D) ≤ LinearMap.ker (B (u - (wu + c • a'))) :=
        Submodule.span_le.2 (fun m hm => LinearMap.mem_ker.2 (key m hm))
      exact LinearMap.mem_ker.1 (hle hm)

theorem exists_orth_decomp {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D]
    [Module ℂ D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y) (W : Submodule ℂ D)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (u : D) :
    ∃ w ∈ W, ∀ w' ∈ W, B (u - w) w' = 0 := by
  classical
  by_cases hu : u = 0
  · exact ⟨0, W.zero_mem, fun w' _ => by simp [hu]⟩
  let S : Subgroup G :=
    { carrier := {g | ρ g u = u}
      mul_mem' := by
        intro a b (ha : ρ a u = u) (hb : ρ b u = u)
        show ρ (a * b) u = u
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        show ρ 1 u = u
        simp
      inv_mem' := by
        intro a (ha : ρ a u = u)
        show ρ a⁻¹ u = u
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hA.1 u
  let K : Subgroup G := K₁ ⊓ S
  have hKo : IsOpen (K : Set G) := by
    rw [Subgroup.coe_inf]; exact hK₁o.inter hSo
  have hKc : IsCompact (K : Set G) := by
    rw [Subgroup.coe_inf]; exact hK₁c.inter_right (Subgroup.isClosed_of_isOpen S hSo)
  have hKS : ∀ k : K, ρ (k : G) u = u := fun k => (Subgroup.mem_inf.1 k.2).2
  have hBu : B u u ≠ 0 := by
    intro h; have := hBp u hu; rw [h] at this; simp at this
  have hχ : ∀ k : K, (χ k : ℂ) = 1 := by
    intro k
    have h := hBe k u u
    rw [hKS k] at h
    have h2 : ((χ k : ℂ) - 1) * B u u = 0 := by rw [sub_mul, ← h]; ring
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hBu
  have hBK : ∀ (k : K) x y, B (ρ (k : G) x) (ρ (k : G) y) = B x y := by
    intro k x y; rw [hBe, hχ, one_mul]
  have : FiniteDimensional ℂ (fixed ρ K) := hA.2 K hKo hKc
  let M : Submodule ℂ D := W ⊓ fixed ρ K
  have : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨s, hs⟩ : M.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨w, hwM, hw⟩ := exists_orth_of_finset B hBp s u
  rw [hs] at hwM hw
  refine ⟨w, (Submodule.mem_inf.1 hwM).1, ?_⟩
  have huF : u - w ∈ fixed ρ K :=
    Submodule.sub_mem _ ((mem_fixed_iff_irr ρ K u).2 hKS) (Submodule.mem_inf.1 hwM).2
  have hfix := (mem_fixed_iff_irr ρ K _).1 huF
  intro w' hw'
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let f : K → D := fun k => ρ (k : G) w'
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k0
    refine ⟨(fun k : K => (k0 : G)⁻¹ * (k : G)) ⁻¹' {g | ρ g w' = w'},
      (hA.1 w').preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
    · simp
    · intro k hk
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk
      simp only [f]
      conv_lhs => rw [show (k : G) = (k0 : G) * ((k0 : G)⁻¹ * (k : G)) by group]
      rw [map_mul, Module.End.mul_apply, hk]
  obtain ⟨T, hTmem⟩ : ∃ T : Finset D, ∀ v, v ∈ T ↔ ∃ k : K, ρ (k : G) w' = v :=
    ⟨hf.range_finite.toFinset, fun v => by simp only [Set.Finite.mem_toFinset, Set.mem_range, f]⟩
  have hTst : ∀ h : K, ∀ v ∈ T, ρ (h : G) v ∈ T := by
    intro h v hv
    obtain ⟨k, rfl⟩ := (hTmem v).1 hv
    exact (hTmem _).2 ⟨h * k, by rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  have hinv : ∀ h : K, ∀ v, ρ ((h⁻¹ : K) : G) (ρ (h : G) v) = v := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hinv' : ∀ h : K, ∀ v, ρ (h : G) (ρ ((h⁻¹ : K) : G) v) = v := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hsumF : ∑ v ∈ T, v ∈ M := by
    refine Submodule.mem_inf.2 ⟨Submodule.sum_mem _ (fun v hv => ?_), ?_⟩
    · obtain ⟨k, rfl⟩ := (hTmem v).1 hv; exact hW _ _ hw'
    · rw [mem_fixed_iff_irr]
      intro h
      rw [map_sum]
      exact Finset.sum_nbij' (fun v => ρ (h : G) v) (fun v => ρ ((h⁻¹ : K) : G) v) (hTst h) (hTst h⁻¹)
        (fun v _ => hinv h v) (fun v _ => hinv' h v) (fun v _ => rfl)
  have h0 := hw _ hsumF
  rw [map_sum] at h0
  have hterm : ∀ v ∈ T, B (u - w) v = B (u - w) w' := by
    intro v hv
    obtain ⟨k, rfl⟩ := (hTmem v).1 hv
    conv_lhs => rw [← hfix k]
    exact hBK k _ _
  rw [Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hcard : T.card ≠ 0 := Finset.card_ne_zero_of_mem ((hTmem w').2 ⟨1, by simp⟩)
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 hcard
  · exact h1

theorem irr_of_forms {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D] [Module ℂ D]
    [Nontrivial D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBh : ∀ x y, B y x = starRingEnd ℂ (B x y)) (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y)
    (hC : ∀ C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ, (∀ x y, C y x = starRingEnd ℂ (C x y)) → (∀ x, 0 ≤ (C x x).re) →
      (∀ x, (C x x).re ≤ (B x x).re) → (∀ g x y, C (ρ g x) (ρ g y) = (χ g : ℂ) * C x y) →
      ∃ c : ℂ, ∀ x y, C x y = c * B x y) :
    ρ.IsIrreducible := by
  classical
  have key : ∀ W : Subrepresentation ρ, W ≠ ⊥ → W = ⊤ := by
    intro W hWb
    let Wm : Submodule ℂ D := W.toSubmodule
    have hWs : ∀ g, ∀ w ∈ Wm, ρ g w ∈ Wm := fun g w hw => W.apply_mem_toSubmodule g hw
    let Wp : Submodule ℂ D :=
      { carrier := {x | ∀ w ∈ Wm, B x w = 0}
        add_mem' := by
          intro a b ha hb w hw
          rw [map_add, LinearMap.add_apply, ha w hw, hb w hw, add_zero]
        zero_mem' := by intro w _; simp
        smul_mem' := by
          intro c x hx w hw
          rw [map_smul, LinearMap.smul_apply, hx w hw, smul_zero] }
    have hWp : ∀ x, x ∈ Wp ↔ ∀ w ∈ Wm, B x w = 0 := fun x => Iff.rfl
    have hWps : ∀ g, ∀ x ∈ Wp, ρ g x ∈ Wp := by
      intro g x hx
      rw [hWp]
      intro w hw
      have h1 : ρ g (ρ g⁻¹ w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [← h1, hBe, (hWp x).1 hx _ (hWs _ _ hw), mul_zero]
    have hdec := fun u => exists_orth_decomp ρ hA K₁ hK₁o hK₁c χ B hBp hBe Wm hWs u
    have hcompl : IsCompl Wm Wp := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx hxp
        by_contra hne
        have := hBp x hne
        rw [(hWp x).1 hxp x hx] at this
        simp at this
      · rw [codisjoint_iff, eq_top_iff]
        intro u _
        obtain ⟨w, hw, hw'⟩ := hdec u
        rw [show u = w + (u - w) by abel]
        exact Submodule.add_mem_sup hw ((hWp _).2 hw')
    let P : D →ₗ[ℂ] D := Wm.projection Wp hcompl
    have hPW : ∀ x, P x ∈ Wm := fun x => Submodule.projection_apply_mem hcompl x
    have hPw : ∀ w ∈ Wm, P w = w := fun w hw => Submodule.projection_apply_of_mem_left hcompl hw
    have hPq : ∀ x, x - P x ∈ Wp := fun x => Submodule.sub_projection_mem hcompl x
    have hP0 : ∀ q ∈ Wp, P q = 0 := fun q hq => Submodule.projection_apply_of_mem_right hcompl hq
    have hPρ : ∀ g x, P (ρ g x) = ρ g (P x) := by
      intro g x
      have hx : ρ g x = ρ g (P x) + ρ g (x - P x) := by
        rw [← map_add]; congr 1; abel
      rw [hx, map_add, hPw _ (hWs g _ (hPW x)), hP0 _ (hWps g _ (hPq x)), add_zero]
    let C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ := (B ∘ₗ P).compl₂ P
    have hCapp : ∀ x y, C x y = B (P x) (P y) := fun x y => rfl
    have hBsplit : ∀ x, B x x = B (P x) (P x) + B (x - P x) (x - P x) := by
      intro x
      have h1 : B (x - P x) (P x) = 0 := (hWp _).1 (hPq x) _ (hPW x)
      have h2 : B (P x) (x - P x) = 0 := by rw [hBh (x - P x) (P x), h1, map_zero]
      conv_lhs => rw [show x = P x + (x - P x) by abel]
      simp only [map_add, LinearMap.add_apply, h1, h2, add_zero, zero_add]
    have hnn : ∀ x, 0 ≤ (B x x).re := by
      intro x
      by_cases h : x = 0
      · rw [h]; simp
      · exact (hBp _ h).le
    obtain ⟨c, hc⟩ := hC C (fun x y => by rw [hCapp, hCapp, hBh]) (fun x => by rw [hCapp]; exact hnn _)
      (fun x => by
        rw [hCapp, hBsplit x, Complex.add_re]
        have := hnn (x - P x)
        linarith)
      (fun g x y => by rw [hCapp, hCapp, hPρ, hPρ, hBe])
    obtain ⟨w0, hw0, hw0ne⟩ : ∃ w ∈ Wm, w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hWb
      apply Subrepresentation.toSubmodule_injective
      show Wm = ⊥
      exact (Submodule.eq_bot_iff _).2 hcon
    have hc1 : c = 1 := by
      have h := hc w0 w0
      rw [hCapp, hPw w0 hw0] at h
      have hB0 : B w0 w0 ≠ 0 := by
        intro h0; have := hBp w0 hw0ne; rw [h0] at this; simp at this
      have h2 : (c - 1) * B w0 w0 = 0 := by rw [sub_mul, ← h]; ring
      rcases mul_eq_zero.1 h2 with h1 | h1
      · exact sub_eq_zero.1 h1
      · exact absurd h1 hB0
    apply Subrepresentation.toSubmodule_injective
    show Wm = ⊤
    rw [eq_top_iff]
    intro x _
    have hq : x - P x = 0 := by
      by_contra hne
      have h := hc (x - P x) (x - P x)
      rw [hCapp, hc1, one_mul, hP0 _ (hPq x), map_zero] at h
      have := hBp _ hne
      rw [← h] at this
      simp at this
    have hx : x = P x := sub_eq_zero.1 hq
    rw [hx]
    exact hPW x
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : D)
    have h1 : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ D))
    rw [← h] at h1
    exact hx ((Submodule.mem_bot ℂ).1 (h1 : x ∈ (⊥ : Submodule ℂ D)))
  exact { exists_pair_ne := ⟨⊥, ⊤, hne⟩
          eq_bot_or_eq_top := fun W => by
            by_cases h : W = ⊥
            · exact Or.inl h
            · exact Or.inr (key W h) }

end PositivityTheory.RgUd.Form.U.Asm
end
end

section
noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Twist

theorem twist_irr {G D : Type} [Group G] [AddCommGroup D] [Module ℂ D] (ρ : Representation ℂ G D) (χ : G →* ℂˣ)
    (h : ρ.IsIrreducible) : (twist ρ χ).IsIrreducible := by
  let f : Subrepresentation ρ ≃o Subrepresentation (twist ρ χ) :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        show ((χ g : ℂˣ) : ℂ) • ρ g v ∈ W.toSubmodule
        exact W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule g hv)⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        have h1 := W.apply_mem_toSubmodule g hv
        have h2 : ρ g v = (((χ g)⁻¹ : ℂˣ) : ℂ) • (twist ρ χ g v) := by
          show ρ g v = (((χ g)⁻¹ : ℂˣ) : ℂ) • (((χ g : ℂˣ) : ℂ) • ρ g v)
          rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
        rw [h2]
        exact W.toSubmodule.smul_mem _ h1⟩
      left_inv := fun W => rfl
      right_inv := fun W => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff f).1 h

end Twist

section Casts

theorem sub_iff_twKer (ψ : AddChar k Circle) (n j : ℕ) (π : GRep k (n + (j + 1))) :
    Subsingleton (derivB ψ (j + 1) π).V ↔
      twKer π.ρ (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) = ⊤ := by
  obtain ⟨q, hqs, hqk, -⟩ := derDict ψ n j π.ρ
  rw [← hqk]
  constructor
  · intro hs
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact @Subsingleton.elim _ hs _ _
  · intro hk
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, rfl⟩ := hqs x
    obtain ⟨b, rfl⟩ := hqs y
    have ha : a ∈ LinearMap.ker q := hk ▸ Submodule.mem_top
    have hb : b ∈ LinearMap.ker q := hk ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at ha hb
    exact ha.trans hb.symm

theorem cast_twKer (ψ : AddChar k Circle) {a b : ℕ} (e : a = b) (π : GRep k a) (m : ℕ) :
    twKer (π.cast e).ρ (derUnip k b m) (derChar k ψ b m) = ⊤ ↔ twKer π.ρ (derUnip k a m) (derChar k ψ a m) = ⊤ := by
  subst e
  rfl

end Casts

section Desc

variable (hUD : UDens k) (hUA : UAtom k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

theorem chain_psd (hB : IsInvForm π B) : ∀ d, d + 1 ≤ N → IsPsd (chain hUD hψc hψ1 π hs B d)
  | 0, _ => isPsd_of_inv π B hB
  | d + 1, hd => (chain_succ hUD hψc hψ1 π hs B d (by omega) (chain_lvl hUD hψc hψ1 π hs B hB d (by omega))).2.1

theorem chain_kills (hB : IsInvForm π B) : ∀ d, d + 1 ≤ N → Kills ψ π (N - d) (chain hUD hψc hψ1 π hs B d)
  | 0, _ => by
    intro v hv w
    have e : N - 0 = N := by omega
    rw [e, twKer_derUnip_self ψ π] at hv
    rw [(Submodule.mem_bot ℂ).1 hv]
    simp
  | d + 1, hd => kills_congr (by omega)
      (chain_succ hUD hψc hψ1 π hs B d (by omega) (chain_lvl hUD hψc hψ1 π hs B hB d (by omega))).2.2.1

include hUA in

theorem twisted_kernel_forms_nonvanishing (hUS : USplit k) (hB : IsInvForm π B) :
    ∀ e d, d + e + 1 = N → (∃ v, chain hUD hψc hψ1 π hs B d v v ≠ 0) →
      ∃ n', n' + d + 1 ≤ N ∧ twKer π (derUnip k N n') (derChar k ψ N n') ≠ ⊤
  | 0, d, hde, ⟨v, hv⟩ => by
    refine ⟨0, by omega, fun htop => hv ?_⟩
    have hK := chain_kills hUD hψc hψ1 π hs B hB d (by omega)
    have e1 : N - d = 1 := by omega
    rw [e1] at hK
    refine hK v ?_ v
    have hle : twKer π (derUnip k N 0) (derChar k ψ N 0) ≤ twKer π (derUnip k N 1) (lvlChar k ψ N 1) :=
      twKer_mono π _ _ (le_inf inf_le_left (inf_le_left.trans (unipB_le_colFix_one N))) fun u => rfl
    exact hle (htop ▸ Submodule.mem_top)
  | e + 1, d, hde, ⟨v, hv⟩ => by
    have hd2 : d + 2 ≤ N := by omega
    by_cases h0 : ∀ w, chain hUD hψc hψ1 π hs B (d + 1) w w = 0
    · have hA := atom_eq_self hUD hUA hψc hψ1 π hs B hUS hB d hd2 h0
      obtain ⟨-, -, -, hK, -⟩ := atom_spec hUD hUA hψc hψ1 π hs B d hd2 (chain_lvl hUD hψc hψ1 π hs B hB d hd2)
      refine ⟨N - 2 - d + 1, by omega, fun htop => hv ?_⟩
      have hmem : v ∈ DerKer k ψ π (N - 2 - d) := by
        unfold DerKer
        rw [htop]
        exact Submodule.mem_top
      have := hK v hmem v
      rwa [hA] at this
    · push_neg at h0
      obtain ⟨n', hn', hne⟩ := twisted_kernel_forms_nonvanishing hUS hB e (d + 1) (by omega) h0
      exact ⟨n', by omega, hne⟩

theorem chain_ne_of (hB : IsInvForm π B) (d n' : ℕ) (hd : d + 1 ≤ N) (hn' : n' + d < N)
    (hne : twKer π (derUnip k N n') (derChar k ψ N n') ≠ ⊤) : ∃ v, chain hUD hψc hψ1 π hs B d v v ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hne
  rw [eq_top_iff]
  intro v _
  have hv := chain_rad hUD hψc hψ1 π hs B hB d hd v (hall v)
  rw [lvlChar_def] at hv
  rw [derChar_def]
  exact twKer_derUnip_le ψ π (a := N - d) (b := n') (x := N - d - 1) (y := n') (by omega) (by omega) (by omega) hv

end Desc

end PositivityTheory.RgUd.Form.U.Asm
end
end

section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Factor

variable {V D : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup D] [Module ℂ D]

theorem factor {C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hC : ∀ v w, C w v = starRingEnd ℂ (C v w)) (q : V →ₗ[ℂ] D)
    (hk : ∀ v ∈ LinearMap.ker q, ∀ w, C v w = 0) {v v' w w' : V} (hv : q v = q v') (hw : q w = q w') :
    C v w = C v' w' := by
  have h1 : v - v' ∈ LinearMap.ker q := by rw [LinearMap.mem_ker, map_sub, hv, sub_self]
  have h2 : w - w' ∈ LinearMap.ker q := by rw [LinearMap.mem_ker, map_sub, hw, sub_self]
  have e1 : C v w = C v' w := by
    have := hk _ h1 w
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have e2 : C v' w = C v' w' := by
    have := hk _ h2 v'
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [hC w v', hC w' v', this]
  rw [e1, e2]

end Factor

theorem dpow_val (n : ℕ) (t : ℝ) (g : GL (Fin n) k) :
    ((dpow n t g : ℂˣ) : ℂ) = ((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) := by
  simp only [dpow, detChar, MonoidHom.coe_comp, Function.comp_apply, absPow]
  rw [MonoidHom.coe_toHomUnits]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Complex.ofReal_cpow (nabs_pos k _).le]

theorem top_core {n N : ℕ} (h : n ≤ N) {V D : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup D] [Module ℂ D]
    [Nontrivial D] (π : Representation ℂ (GL (Fin N) k) V) (ρ : Representation ℂ (GL (Fin n) k) D)
    (hadm : IsAdmissible ρ) (q : V →ₗ[ℂ] D) (hqs : Function.Surjective q)
    (hqe : ∀ g v, q (π (blkAt k n N h g) v) = ρ g (q v)) (s t : ℝ) (hst : 2 * t + s = 0)
    (E : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hE1 : IsPsd E) (hE2 : ∀ v ∈ LinearMap.ker q, ∀ w, E v w = 0)
    (hE3 : ∀ v, E v v = 0 → v ∈ LinearMap.ker q)
    (hE4 : ∀ g v w, E (π (blkAt k n N h g) v) (π (blkAt k n N h g) w) =
      ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * E v w)
    (hLift : ∀ C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, IsPsd C → (∀ v ∈ LinearMap.ker q, ∀ w, C v w = 0) →
      (∀ g v w, C (π (blkAt k n N h g) v) (π (blkAt k n N h g) w) =
        ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * C v w) →
      (∀ v, (C v v).re ≤ (E v v).re) → ∃ c : ℂ, ∀ v w, C v w = c * E v w) :
    (twist ρ (dpow n t)).IsIrreducible ∧ IsUnitarisable (twist ρ (dpow n t)) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.2 hqs)
  have hqr : ∀ x, q (r x) = x := fun x => LinearMap.congr_fun hr x
  set Bt : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ := (E ∘ₗ r).compl₂ r with hBt
  have hBt_apply : ∀ x y, Bt x y = E (r x) (r y) := fun x y => rfl
  have hdesc : ∀ v w, Bt (q v) (q w) = E v w := fun v w => by
    rw [hBt_apply]
    exact factor hE1.1 q hE2 (hqr _) (hqr _)
  have hBh : ∀ x y, Bt y x = starRingEnd ℂ (Bt x y) := fun x y => by
    rw [hBt_apply, hBt_apply, hE1.1]
  have hBp : ∀ x, x ≠ 0 → 0 < (Bt x x).re := by
    intro x hx
    rw [hBt_apply]
    rcases (hE1.2 (r x)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hx
      have h0 : E (r x) (r x) = 0 := Complex.ext heq.symm (diag_real hE1.1 _)
      have := hE3 _ h0
      rw [LinearMap.mem_ker, hqr] at this
      exact this
  have hBe : ∀ g x y, Bt (ρ g x) (ρ g y) = ((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * Bt x y := by
    intro g x y
    obtain ⟨v, rfl⟩ := hqs x
    obtain ⟨w, rfl⟩ := hqs y
    rw [← hqe, ← hqe, hdesc, hdesc, hE4]
  refine ⟨?_, ⟨Bt, hBh, hBp, fun g x y => ?_⟩⟩
  · apply twist_irr
    obtain ⟨K₁, hK₁o, hK₁c, -⟩ := GlobalTheory.T.compact_open_subgroups_basis k n Set.univ Filter.univ_mem
    refine irr_of_forms ρ hadm K₁ hK₁o hK₁c (fun g => nabs k (GeneralLinearGroup.det g) ^ s) Bt hBh hBp hBe ?_
    intro Ct hCh hCp hCle hCe
    set C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := (Ct ∘ₗ q).compl₂ q with hC
    have hC_apply : ∀ v w, C v w = Ct (q v) (q w) := fun v w => rfl
    obtain ⟨c, hc⟩ := hLift C ⟨fun v w => by rw [hC_apply, hC_apply, hCh], fun v => by rw [hC_apply]; exact hCp _⟩
      (fun v hv w => by rw [hC_apply, LinearMap.mem_ker.1 hv, map_zero, LinearMap.zero_apply])
      (fun g v w => by rw [hC_apply, hC_apply, hqe, hqe, hCe])
      (fun v => by rw [hC_apply, ← hdesc]; exact hCle _)
    refine ⟨c, fun x y => ?_⟩
    obtain ⟨v, rfl⟩ := hqs x
    obtain ⟨w, rfl⟩ := hqs y
    rw [← hC_apply, hc, hdesc]
  · show Bt (((dpow n t g : ℂˣ) : ℂ) • ρ g x) (((dpow n t g : ℂˣ) : ℂ) • ρ g y) = Bt x y
    have hsm : ∀ (c : ℂ) (X Y : D), Bt (c • X) (c • Y) = c * (starRingEnd ℂ c * Bt X Y) := by
      intro c X Y
      rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul]
    rw [hsm, hBe, dpow_val, Complex.conj_ofReal]
    have hpos := nabs_pos k (GeneralLinearGroup.det g)
    have e : (nabs k (GeneralLinearGroup.det g) ^ t) * ((nabs k (GeneralLinearGroup.det g) ^ t) *
        (nabs k (GeneralLinearGroup.det g) ^ s)) = 1 := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos, show t + (t + s) = 0 by linarith, Real.rpow_zero]
    calc ((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * (((nabs k (GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) *
          (((nabs k (GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * Bt x y))
        = (((nabs k (GeneralLinearGroup.det g) ^ t) * ((nabs k (GeneralLinearGroup.det g) ^ t) *
          (nabs k (GeneralLinearGroup.det g) ^ s)) : ℝ) : ℂ) * Bt x y := by push_cast; ring
      _ = Bt x y := by rw [e]; simp

end PositivityTheory.RgUd.Form.U.Asm
end
end

section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mirU_apply {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) (a b : Fin (n + 1))
    (hab : ¬ ((b : ℕ) = n ∧ (a : ℕ) < n)) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b = if a = b then 1 else 0 := by
  obtain ⟨v, hv⟩ := (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k n u hu :
    ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv']
  show (1 + colMat k n v.toAdd) a b = _
  rw [Matrix.add_apply, Matrix.one_apply]
  have hc : colMat k n v.toAdd a b = 0 := by
    simp only [colMat]
    split_ifs with hb
    · have ha0 : ¬ (a : ℕ) < n := fun h' => hab ⟨by rw [hb, Fin.val_last], h'⟩
      have ha : a = Fin.last n := by
        ext
        have := a.isLt
        rw [Fin.val_last]
        omega
      rw [ha, Fin.lastCases_last]
    · rfl
  rw [hc, add_zero]

theorem blkAt_mirU_apply {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n) (hu : mirabolicProjection k n u = 1) (a b : Fin N)
    (hab : ¬ ((b : ℕ) = n ∧ (a : ℕ) < n)) :
    ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) a b =
      if a = b then 1 else 0 := by
  rw [blkAt_apply]
  by_cases ha : (a : ℕ) < n + 1
  · rw [dif_pos ha]
    by_cases hb : (b : ℕ) < n + 1
    · rw [dif_pos hb, mirU_apply u hu _ _ (by simpa using hab)]
      by_cases e : a = b
      · subst e
        simp
      · rw [if_neg e, if_neg]
        intro e'
        exact e (Fin.ext (by simpa using congrArg Fin.val e'))
    · rw [dif_neg hb, if_neg]
      intro e
      subst e
      exact hb ha
  · rw [dif_neg ha]

theorem blkAt_mirU_mem {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) ∈ derUnip k N n := by
  refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => ?_⟩
  · rw [Fin.lt_def] at hji
    rw [blkAt_mirU_apply h u hu i j (by omega), if_neg (fun e => by rw [e] at hji; omega)]
  · rw [blkAt_mirU_apply h u hu i i (by omega), if_pos rfl]
  · rw [blkAt_mirU_apply h u hu i j (by omega), Matrix.one_apply]

theorem derChar_blkAt_mirU (ψ : AddChar k Circle) {n N : ℕ} (h : n + 1 ≤ N) (u : Mir k n)
    (hu : mirabolicProjection k n u = 1) : derChar k ψ N n ⟨_, blkAt_mirU_mem h u hu⟩ = 1 := by
  rw [derChar_def]
  simp only [whitCharFrom, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  show ((blkAt k (n + 1) N h (u : GL (Fin (n + 1)) k) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
  rw [blkAt_mirU_apply h u hu _ _ (by omega), if_neg (fun e => by rw [e] at h1; omega)]

theorem blkAt_levi {n N : ℕ} (h : n + 1 ≤ N) (g : GL (Fin n) k) :
    blkAt k (n + 1) N h ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = blkAt k n N (by omega) g := by
  ext a b
  rw [blkAt_apply, blkAt_apply]
  have hl : ∀ (a' b' : Fin (n + 1)), (((levi k n g : Mir k n) : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) a' b' = glEmbMat k n (g : Matrix (Fin n) (Fin n) k) a' b' :=
    fun _ _ => rfl
  by_cases ha : (a : ℕ) < n
  · have ha' : (a : ℕ) < n + 1 := by omega
    rw [dif_pos ha', dif_pos ha]
    by_cases hb : (b : ℕ) < n
    · have hb' : (b : ℕ) < n + 1 := by omega
      rw [dif_pos hb', dif_pos hb, hl, glEmbMat_apply']
      simp only [ha, hb, dif_pos]
    · rw [dif_neg hb]
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true]
      · rw [dif_neg hb']
  · rw [dif_neg ha]
    by_cases ha' : (a : ℕ) < n + 1
    · rw [dif_pos ha']
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, dif_neg, not_false_eq_true]
        simp only [Fin.ext_iff]
      · rw [dif_neg hb']
        split_ifs with e <;> first | rfl | (simp only [Fin.ext_iff] at e; omega)
    · rw [dif_neg ha']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_mir {n : ℕ} (p : Mir k n) :
    Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det (mirabolicProjection k n p) := by
  have hl := (mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · rw [hl, Fin.succAbove_last]
    simp only [eLast, Pi.single_eq_same, mul_one, Fin.val_last]
    rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul]
    rfl
  · intro j _ hj
    rw [hl, eLast, Pi.single_eq_of_ne hj]
    simp
  · simp

theorem mir_act (ψ : AddChar k Circle) {n N : ℕ} (h : n + 1 ≤ N) {V D : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup D] [Module ℂ D] (π : Representation ℂ (GL (Fin N) k) V) (ρ' : Representation ℂ (GL (Fin n) k) D)
    (q : V →ₗ[ℂ] D) (hq1 : ∀ g v, q (π (blkAt k n N (by omega) g) v) = ρ' g (q v))
    (hq2 : twKer π (derUnip k N n) (derChar k ψ N n) ≤ LinearMap.ker q) (p : Mir k n) :
    (∀ v, q (π (blkAt k (n + 1) N h p) v) = ρ' (mirabolicProjection k n p) (q v)) ∧
      Matrix.GeneralLinearGroup.det (p : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det (mirabolicProjection k n p) := by
  have hu1 : mirabolicProjection k n (p * (levi k n (mirabolicProjection k n p))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi, mul_inv_cancel]
  have hp : (p : GL (Fin (n + 1)) k) = ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k) *
      ((levi k n (mirabolicProjection k n p) : Mir k n) : GL (Fin (n + 1)) k) := by
    rw [← Subgroup.coe_mul, inv_mul_cancel_right]
  have hkill : ∀ w, q (π (blkAt k (n + 1) N h
      ((p * (levi k n (mirabolicProjection k n p))⁻¹ : Mir k n) : GL (Fin (n + 1)) k)) w) = q w := by
    intro w
    rw [← sub_eq_zero, ← map_sub]
    apply hq2
    refine Submodule.subset_span ⟨⟨_, blkAt_mirU_mem h _ hu1⟩, w, ?_⟩
    rw [derChar_blkAt_mirU ψ h _ hu1]
    simp
  refine ⟨fun v => ?_, det_mir p⟩
  conv_lhs => rw [hp]
  rw [map_mul, map_mul, Module.End.mul_apply, hkill, blkAt_levi, hq1]

end PositivityTheory.RgUd.Form.U.Asm
end
end

section
noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gLEq_congr {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {a b : ℕ} (hab : a = b) {ha : a + 1 ≤ N} {hb : b + 1 ≤ N} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (h : GLEq k π a ha s B) : GLEq k π b hb s B := by
  subst hab; exact h

theorem isAtom_congr {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {a b : ℕ} (hab : a = b) {ha : a + 2 ≤ N} {hb : b + 2 ≤ N} {B B₀ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (h : IsAtom ha π B B₀) : IsAtom hb π B B₀ := by
  subst hab; exact h

theorem scalAt_eq (n N : ℕ) (h : n ≤ N) (z : kˣ) :
    scalAt k n N h z = blkAt k n N h (GeneralLinearGroup.scalar (Fin n) z) := by
  unfold scalAt
  congr 1

theorem nabs_det_scalar (n : ℕ) (z : kˣ) :
    nabs k (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) z)) = nabs k z ^ n := by
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]
  simp [nabs, map_pow]

theorem derivTop_of (hUA : UAtom k) (hUD : UDens k) (hUS : USplit k) (hUL : ULift k) (hUAd : UAdm k)
    (hTB : ThmB k) : DerivTop k := by
  intro ψ hψc hψ1 n h π hh1 hsm hirr hunit hnt hsub
  obtain ⟨j, rfl⟩ : ∃ j, h = j + 1 := ⟨h - 1, by omega⟩
  obtain ⟨B, hBh, hBp, hBi⟩ := hunit
  have hB : IsInvForm π.ρ B := ⟨hBh, hBp, hBi⟩
  obtain ⟨q, hqs, hqk, hqe⟩ := derDict ψ n j π.ρ
  have hvan : ∀ n', n' < n → twKer π.ρ (derUnip k (n + (j + 1)) n') (derChar k ψ (n + (j + 1)) n') = ⊤ := by
    intro n' hn'
    have e : n + (j + 1) = n' + ((n + j - n') + 1) := by omega
    exact (cast_twKer ψ e π n').1 ((sub_iff_twKer ψ n' (n + j - n') (π.cast e)).1 (hsub n' _ e (by omega)))
  have hE1 : IsPsd (chain hUD hψc hψ1 π.ρ hsm B j) := chain_psd hUD hψc hψ1 π.ρ hsm B hB j (by omega)
  have hker : twKer π.ρ (derUnip k (n + (j + 1)) (n + (j + 1) - j)) (lvlChar k ψ (n + (j + 1)) (n + (j + 1) - j)) ≤
      LinearMap.ker q := by
    rw [hqk, lvlChar_def, derChar_def]
    exact twKer_derUnip_le ψ π.ρ (a := n + (j + 1) - j) (b := n) (x := n + (j + 1) - j - 1) (y := n)
      (by omega) (by omega) (by omega)
  have hE3 : ∀ v, chain hUD hψc hψ1 π.ρ hsm B j v v = 0 → v ∈ LinearMap.ker q :=
    fun v hv => hker (chain_rad hUD hψc hψ1 π.ρ hsm B hB j (by omega) v hv)
  have hq2 : twKer π.ρ (derUnip k (n + (j + 1)) n) (derChar k ψ (n + (j + 1)) n) ≤ LinearMap.ker q := by
    rw [hqk]
    exact le_rfl

  have hE24 : (∀ v ∈ LinearMap.ker q, ∀ w, chain hUD hψc hψ1 π.ρ hsm B j v w = 0) ∧
      ∀ (g : GL (Fin n) k) v w, chain hUD hψc hψ1 π.ρ hsm B j (π.ρ (blkAt k n (n + (j + 1)) (by omega) g) v)
        (π.ρ (blkAt k n (n + (j + 1)) (by omega) g) w) =
        ((nabs k (GeneralLinearGroup.det g) ^ (j : ℝ) : ℝ) : ℂ) * chain hUD hψc hψ1 π.ρ hsm B j v w := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      refine ⟨fun v hv w => ?_, fun g v w => ?_⟩
      · have hK := chain_kills hUD hψc hψ1 π.ρ hsm B hB j (by omega)
        have e1 : 0 + (j + 1) - j = 1 := by omega
        rw [e1] at hK
        refine hK v ?_ w
        have hle : twKer π.ρ (derUnip k (0 + (j + 1)) 0) (derChar k ψ (0 + (j + 1)) 0) ≤
            twKer π.ρ (derUnip k (0 + (j + 1)) 1) (lvlChar k ψ (0 + (j + 1)) 1) :=
          twKer_mono π.ρ _ _ (le_inf inf_le_left (inf_le_left.trans (unipB_le_colFix_one _))) fun u => rfl
        rw [hqk] at hv
        exact hle hv
      · have hg : g = 1 := by
          ext i
          exact Fin.elim0 i
        subst hg
        simp [nabs]
    · obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
      have hN2 : j + 2 ≤ n₀ + 1 + (j + 1) := by omega
      have h0 : ∀ v, chain hUD hψc hψ1 π.ρ hsm B (j + 1) v v = 0 := by
        by_contra hc
        push_neg at hc
        obtain ⟨n', hn', hne⟩ := twisted_kernel_forms_nonvanishing hUD hUA hψc hψ1 π.ρ hsm B hUS hB n₀ (j + 1) (by omega) hc
        exact hne (hvan n' (by omega))
      have hA := atom_eq_self hUD hUA hψc hψ1 π.ρ hsm B hUS hB j hN2 h0
      obtain ⟨-, -, -, hK, hG, -⟩ := atom_spec hUD hUA hψc hψ1 π.ρ hsm B j hN2
        (chain_lvl hUD hψc hψ1 π.ρ hsm B hB j hN2)
      rw [hA] at hK hG
      refine ⟨fun v hv w => ?_, fun g v w => ?_⟩
      · unfold DerKer at hK
        have e2 : n₀ + 1 + (j + 1) - 2 - j + 1 = n₀ + 1 := by omega
        rw [e2] at hK
        rw [hqk] at hv
        exact hK v hv w
      · have hG' : GLEq k π.ρ n₀ (by omega) (j : ℝ) (chain hUD hψc hψ1 π.ρ hsm B j) := gLEq_congr (by omega) hG
        exact hG' g v w
  obtain ⟨hE2, hE4⟩ := hE24
  refine top_core (by omega : n ≤ n + (j + 1)) π.ρ (derivB ψ (j + 1) π).ρ
    (hUAd ψ hψc hψ1 n (j + 1) π hsm hirr) q hqs hqe (j : ℝ) ((1 - ((j + 1 : ℕ) : ℝ)) / 2) (by push_cast; ring)
    (chain hUD hψc hψ1 π.ρ hsm B j) hE1 hE2 hE3 hE4 ?_
  intro C hC1 hC2 hC3 hC4
  refine lift hUD hψc hψ1 π.ρ hsm B hUL hTB hirr hB j (by omega) C hC1 (fun v hv w => hC2 v (hker hv) w) ?_ hC4
  refine mirEq_congr (a := n) (ha := by omega) (by omega) rfl ?_
  intro p hp v w
  obtain ⟨hact, hdet⟩ := mir_act ψ (by omega : n + 1 ≤ n + (j + 1)) π.ρ (derivB ψ (j + 1) π).ρ q hqe hq2 ⟨p, hp⟩
  have e : C (π.ρ (blkAt k (n + 1) (n + (j + 1)) (by omega) p) v) (π.ρ (blkAt k (n + 1) (n + (j + 1)) (by omega) p) w) =
      C (π.ρ (blkAt k n (n + (j + 1)) (by omega) (mirabolicProjection k n ⟨p, hp⟩)) v)
        (π.ρ (blkAt k n (n + (j + 1)) (by omega) (mirabolicProjection k n ⟨p, hp⟩)) w) :=
    factor hC1.1 q hC2 ((hact v).trans (hqe _ v).symm) ((hact w).trans (hqe _ w).symm)
  rw [e, hC3, ← hdet]

set_option maxHeartbeats 1000000 in

theorem derivPos_of (hUA : UAtom k) (hUD : UDens k) (hUS : USplit k) (hUL : ULift k) (hUSh : UShell k)
    (hUE : UEig k) (hTB : ThmB k) : DerivPos k := by
  intro ψ hψc hψ1 n i π hi hsm hirr hunit hex W _ _ σ ω hW hsq hcc z hz
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨B, hBh, hBp, hBi⟩ := hunit
  have hB : IsInvForm π.ρ B := ⟨hBh, hBp, hBi⟩
  obtain ⟨n', h', e, hlt, hnt'⟩ := hex
  obtain ⟨j', rfl⟩ : ∃ j', h' = j' + 1 := ⟨h' - 1, by omega⟩
  have hne : twKer π.ρ (derUnip k (n + (j + 1)) n') (derChar k ψ (n + (j + 1)) n') ≠ ⊤ := by
    intro htop
    have h2 := (sub_iff_twKer ψ n' j' (π.cast e)).2 ((cast_twKer ψ e π n').2 htop)
    exact not_subsingleton _ h2
  obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
  set t : ℝ := (1 - ((j + 1 : ℕ) : ℝ)) / 2 with ht
  obtain ⟨x, hx0, hxe⟩ := hUE ψ hψc hψ1 (n₀ + 1) (j + 1) π hsm hirr t W σ ω hW hsq hcc z
  obtain ⟨q, hqs, hqk, hqe⟩ := derDict ψ (n₀ + 1) j π.ρ
  obtain ⟨v, rfl⟩ := hqs x
  set g := GeneralLinearGroup.scalar (Fin (n₀ + 1)) z with hg
  set ct : ℂ := ((dpow (n₀ + 1) t g : ℂˣ) : ℂ) with hct
  have hct0 : ct ≠ 0 := Units.ne_zero _
  set c : ℂ := ct⁻¹ * (ω z : ℂ) with hc
  have hx0' : q v ≠ (0 : TwJacquet (iterPhi k ψ j (resM k π.ρ)).ρ (MirUin k (n₀ + 1)) 1) := hx0
  have hρ : GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = c • q v := by
    have h1 : ct • GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = (ω z : ℂ) • q v := hxe
    calc GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) = ct⁻¹ • (ct • GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v)) := by
          rw [smul_smul, inv_mul_cancel₀ hct0, one_smul]
      _ = c • q v := by rw [h1, smul_smul]
  have hN2 : j + 2 ≤ n₀ + 1 + (j + 1) := by omega

  have hchne := chain_ne_of hUD hψc hψ1 π.ρ hsm B hB (j + 1) n' (by omega) (by omega) hne
  have hA0 := atom_eq_zero hUD hUA hψc hψ1 π.ρ hsm B hUS hUL hTB hirr hB j hN2 hchne
  have hAz : atom hUD hUA hψc hψ1 π.ρ hsm B j = 0 := by
    ext a b
    simp [hA0 a b]
  have hL := chain_lvl hUD hψc hψ1 π.ρ hsm B hB j hN2
  obtain ⟨hAt, -⟩ := atom_spec hUD hUA hψc hψ1 π.ρ hsm B j hN2 hL
  rw [hAz] at hAt
  have hL' : Lvl k ψ π.ρ n₀ (by omega) (j : ℝ) (chain hUD hψc hψ1 π.ρ hsm B j) := lvl_congr (by omega) rfl hL
  have hAt' : IsAtom (by omega : n₀ + 2 ≤ n₀ + 1 + (j + 1)) π.ρ (chain hUD hψc hψ1 π.ρ hsm B j) 0 :=
    isAtom_congr (by omega) hAt
  have hmem : π.ρ (scalAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) z) v - c • v ∈ DerKer k ψ π.ρ n₀ := by
    have : π.ρ (scalAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) z) v - c • v ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, map_smul, scalAt_eq]
      have h2 : q (π.ρ (blkAt k (n₀ + 1) (n₀ + 1 + (j + 1)) (by omega) g) v) = GlobalTheory.BZMir.deriv k ψ j π.ρ g (q v) :=
        hqe g v
      rw [h2, hρ, sub_self]
    rw [hqk] at this
    exact this
  have hnot : v ∉ DerKer k ψ π.ρ n₀ ⊔ LinearMap.ker (chain hUD hψc hψ1 π.ρ hsm B j) := by
    intro hv
    have hle : LinearMap.ker (chain hUD hψc hψ1 π.ρ hsm B j) ≤ DerKer k ψ π.ρ n₀ := by
      intro a ha
      have ha0 : chain hUD hψc hψ1 π.ρ hsm B j a a = 0 := by
        rw [LinearMap.mem_ker] at ha
        rw [ha]
        rfl
      have hr := chain_rad hUD hψc hψ1 π.ρ hsm B hB j (by omega) a ha0
      rw [lvlChar_def] at hr
      unfold DerKer
      rw [derChar_def]
      exact twKer_derUnip_le ψ π.ρ (a := n₀ + 1 + (j + 1) - j) (b := n₀ + 1) (x := n₀ + 1 + (j + 1) - j - 1)
        (y := n₀ + 1) (by omega) (by omega) (by omega) hr
    have hv' : v ∈ LinearMap.ker q := by
      rw [hqk]
      exact (sup_le le_rfl hle) hv
    exact hx0' (LinearMap.mem_ker.1 hv')
  have hsh := hUSh ψ hψc hψ1 n₀ (n₀ + 1 + (j + 1)) (by omega) π.V π.ρ hsm (j : ℝ)
    (chain hUD hψc hψ1 π.ρ hsm B j) hL' hAt' z c v hz hmem hnot

  have ha := nabs_pos k z
  set a := nabs k z with ha_def
  have hctv : ct = (((a ^ (n₀ + 1) : ℝ) ^ t : ℝ) : ℂ) := by
    rw [hct, dpow_val, hg, nabs_det_scalar]
  have hω : (ω z : ℂ) = c * ct := by
    rw [hc, mul_comm, ← mul_assoc, mul_inv_cancel₀ hct0, one_mul]
  have hnct : ‖ct‖ ^ 2 = a ^ (-(((n₀ : ℝ) + 1) * j)) := by
    rw [hctv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.rpow_natCast a (n₀ + 1),
      ← Real.rpow_mul ha.le, ← Real.rpow_natCast _ 2, ← Real.rpow_mul ha.le, ht]
    congr 1
    push_cast
    ring
  have hprod : ‖(ω z : ℂ)‖ ^ 2 < 1 := by
    rw [hω, norm_mul, mul_pow, hnct]
    have hpos : 0 < a ^ (-(((n₀ : ℝ) + 1) * j)) := Real.rpow_pos_of_pos ha _
    calc ‖c‖ ^ 2 * a ^ (-(((n₀ : ℝ) + 1) * j)) < a ^ (((n₀ : ℝ) + 1) * j) * a ^ (-(((n₀ : ℝ) + 1) * j)) :=
          mul_lt_mul_of_pos_right hsh hpos
      _ = 1 := by rw [← Real.rpow_add ha, add_neg_cancel, Real.rpow_zero]
  nlinarith [norm_nonneg (ω z : ℂ)]

theorem uAsm : UAsm k := fun hUA hUD hUS hUL hUSh hUE hUAd hTB =>
  ⟨derivTop_of hUA hUD hUS hUL hUAd hTB, derivPos_of hUA hUD hUS hUL hUSh hUE hTB⟩

end PositivityTheory.RgUd.Form.U.Asm
end
end
