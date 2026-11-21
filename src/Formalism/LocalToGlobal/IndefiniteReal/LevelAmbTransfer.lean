import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransfer
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Lemmata.RankOneOrbitForms.RankOneForm
import Formalism.LocalToGlobal.GlobalTheory.DivPassage

section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer.Lat

open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.IndefR.LatticeTransfer

section

variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] in
theorem mem_cut {A : Submodule (𝓞 K) V} {p : V →ₗ[K] V} (hp : ∀ a, p (p a) = p a) {a : V} :
    a ∈ cut A p ↔ a ∈ A ∧ p a = a := by
  unfold cut
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_range]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨a, h⟩⟩
  rintro ⟨z, rfl⟩
  exact hp z

theorem exists_smul_mem {A : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (A : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K
    (A : Set V) x hx
  refine ⟨t, nonZeroDivisors.coe_ne_zero t, ?_⟩
  rw [Submodule.span_eq] at ht
  exact ht

theorem mem_span_of_smul_mem {A : Submodule (𝓞 K) V} {x : V} {d : 𝓞 K} (hd : d ≠ 0)
    (hx : d • x ∈ A) : x ∈ Submodule.span K (A : Set V) := by
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have h1 : x = (d : K)⁻¹ • (d • x) := by
    rw [← IsScalarTower.algebraMap_smul K d x, smul_smul]
    simp [hdK]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

theorem span_cut {A : Submodule (𝓞 K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    (p : V →ₗ[K] V) : Submodule.span K (cut A p : Set V) = LinearMap.range p := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro a ha
    exact ha.2
  · intro u hu
    obtain ⟨d, hd, hdu⟩ := exists_smul_mem (A := A) (x := u) (by rw [hA]; trivial)
    refine mem_span_of_smul_mem hd ⟨hdu, ?_⟩
    have : d • u = (d : K) • u := (IsScalarTower.algebraMap_smul K d u).symm
    change d • u ∈ LinearMap.range p
    rw [this]
    exact Submodule.smul_mem _ _ hu

theorem rkK_cut {A : Submodule (𝓞 K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    (p : V →ₗ[K] V) : rkK (cut A p) = finrank K (LinearMap.range p) := by
  unfold rkK
  rw [span_cut hA]

theorem fg_cut {A : Submodule (𝓞 K) V} (hA : A.FG) (p : V →ₗ[K] V) : (cut A p).FG :=
  hA.of_le inf_le_left

omit [NumberField K] in
theorem map_osmul {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (p : V →ₗ[K] W) (d : 𝓞 K) (a : V) : p (d • a) = d • p a := by
  rw [← IsScalarTower.algebraMap_smul K d a, map_smul, IsScalarTower.algebraMap_smul]

end

section

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}

def Tr (p₀ p : V →ₗ[K] V) (x y : Fin n → V →ₗ[K] V) (c : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ a, p₀ (p₀ a) = p₀ a) ∧ (∀ a, p (p a) = p a) ∧
  (∀ j a, p₀ a = a → p (x j a) = x j a) ∧ (∀ i a, p a = a → p₀ (y i a) = y i a) ∧
  c.det ≠ 0 ∧ (∀ i j a, p₀ a = a → y i (x j a) = c i j • a) ∧
  (∀ a, p a = a → ∑ j, ∑ i, c⁻¹ j i • x j (y i a) = a)

variable {p₀ p : V →ₗ[K] V} {x y : Fin n → V →ₗ[K] V} {c : Matrix (Fin n) (Fin n) K}

theorem Tr.yx_sum (h : Tr p₀ p x y c) (a : Fin n → V) (ha : ∀ j, p₀ (a j) = a j) (i : Fin n) :
    y i (∑ j, x j (a j)) = ∑ j, c i j • a j := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => h.2.2.2.2.2.1 i j _ (ha j)

theorem Tr.first_axis_injective (h : Tr p₀ p x y c) (a : Fin n → V) (ha : ∀ j, p₀ (a j) = a j)
    (h0 : ∑ j, x j (a j) = 0) : a = 0 := by
  have h1 : ∀ i, ∑ j, c i j • a j = 0 := fun i => by
    rw [← h.yx_sum a ha i, h0, map_zero]
  have hu : IsUnit c.det := isUnit_iff_ne_zero.mpr h.2.2.2.2.1
  funext k
  have h2 : ∑ i, c⁻¹ k i • ∑ j, c i j • a j = a k := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hu, Matrix.one_apply]
    simp
  rw [← h2]
  simp [h1]

theorem Tr.inj_y (h : Tr p₀ p x y c) (a : V) (ha : p a = a) (h0 : ∀ i, y i a = 0) : a = 0 := by
  rw [← h.2.2.2.2.2.2 a ha]
  simp [h0]

theorem Tr.rank [FiniteDimensional K V] (h : Tr p₀ p x y c) :
    finrank K (LinearMap.range p) = n * finrank K (LinearMap.range p₀) := by
  have hfix0 : ∀ a : LinearMap.range p₀, p₀ a = a := by
    rintro ⟨_, z, rfl⟩; exact h.1 z
  have hfix : ∀ a : LinearMap.range p, p a = a := by
    rintro ⟨_, z, rfl⟩; exact h.2.1 z
  have hpi : finrank K (Fin n → LinearMap.range p₀) = n * finrank K (LinearMap.range p₀) := by
    rw [Module.finrank_pi_fintype]; simp
  rw [← hpi]
  apply le_antisymm
  · let Y : LinearMap.range p →ₗ[K] (Fin n → LinearMap.range p₀) :=
      LinearMap.pi fun i => LinearMap.codRestrict _ (y i ∘ₗ (LinearMap.range p).subtype)
        fun a => ⟨_, h.2.2.2.1 i a (hfix a)⟩
    refine LinearMap.finrank_le_finrank_of_injective (f := Y) ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply Subtype.ext
    refine h.inj_y a (hfix a) fun i => ?_
    exact congrArg Subtype.val (congrFun ha i)
  · let X : (Fin n → LinearMap.range p₀) →ₗ[K] LinearMap.range p :=
      LinearMap.codRestrict _ (∑ j, x j ∘ₗ (LinearMap.range p₀).subtype ∘ₗ LinearMap.proj j)
        fun a => by
          rw [LinearMap.sum_apply]
          exact Submodule.sum_mem _ fun j _ => ⟨_, h.2.2.1 j (a j) (hfix0 _)⟩
    refine LinearMap.finrank_le_finrank_of_injective (f := X) ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 := congrArg Subtype.val ha
    simp only [X, LinearMap.codRestrict_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, LinearMap.proj_apply, ZeroMemClass.coe_zero] at h1
    have h2 := h.first_axis_injective (fun j => (a j : V)) (fun j => hfix0 _) h1
    funext j
    exact Subtype.ext (congrFun h2 j)

end

section

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem pe_facts {ε e : V →ₗ[K] V} (hε : ε ∘ₗ ε = ε) (he : e ∘ₗ e = e) (hc : e ∘ₗ ε = ε ∘ₗ e) :
    (∀ a, (ε ∘ₗ e) ((ε ∘ₗ e) a) = (ε ∘ₗ e) a) ∧
    ∀ a, (ε ∘ₗ e) a = a ↔ ε a = a ∧ e a = a := by
  have h1 : ∀ a, ε (ε a) = ε a := fun a => LinearMap.congr_fun hε a
  have h2 : ∀ a, e (e a) = e a := fun a => LinearMap.congr_fun he a
  have h3 : ∀ a, e (ε a) = ε (e a) := fun a => LinearMap.congr_fun hc a
  refine ⟨fun a => ?_, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · simp only [LinearMap.comp_apply, h3, h1, h2]
  · simp only [LinearMap.comp_apply] at h
    constructor
    · rw [← h, h1]
    · rw [← h, h3, h2]
  · simp only [LinearMap.comp_apply, h.1, h.2]

theorem tr_of_core (hP : IdemP) {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    {τ : Representation K G T} {H₀ : Subgroup G} {χ₀ : H₀ →* (𝓞 K)ˣ} {H : Subgroup G}
    {χ : H →* (𝓞 K)ˣ} {n : ℕ} {γ δ : Fin n → G} {c : Matrix (Fin n) (Fin n) K}
    {Γ : Matrix (Fin n) (Fin n) (𝓞 K)} (h : CoreData τ H₀ χ₀ H χ γ δ c Γ)
    (ρ : Representation K G V) (he : eS τ ρ ∘ₗ eS τ ρ = eS τ ρ) :
    Tr (epP H₀ χ₀ ρ ∘ₗ eS τ ρ) (epP H χ ρ ∘ₗ eS τ ρ) (fun j => epP H χ ρ ∘ₗ ρ (γ j))
      (fun i => epP H₀ χ₀ ρ ∘ₗ ρ (δ i)) c := by
  obtain ⟨hE, hEp⟩ := hP K G V ρ
  obtain ⟨hc, hcp, -⟩ := hE T τ
  have f0 := pe_facts (hEp H₀ χ₀).1 he (hcp H₀ χ₀)
  have f1 := pe_facts (hEp H χ).1 he (hcp H χ)
  have key : ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (g : G) (a : V), eS τ ρ a = a →
      (epP H χ ρ ∘ₗ eS τ ρ) ((epP H χ ρ ∘ₗ ρ g) a) = (epP H χ ρ ∘ₗ ρ g) a := by
    intro H χ g a ha
    have h1 : ∀ a, epP H χ ρ (epP H χ ρ a) = epP H χ ρ a :=
      fun a => LinearMap.congr_fun (hEp H χ).1 a
    have h2 : ∀ a, eS τ ρ (epP H χ ρ a) = epP H χ ρ (eS τ ρ a) :=
      fun a => LinearMap.congr_fun (hcp H χ) a
    have h3 : eS τ ρ (ρ g a) = ρ g (eS τ ρ a) := LinearMap.congr_fun (hc g) a
    simp only [LinearMap.comp_apply, h2, h1, h3, ha]
  obtain ⟨hd, -, -, hV⟩ := h
  refine ⟨f0.1, f1.1, fun j a ha => key H χ _ a ((f0.2 a).1 ha).2,
    fun i a ha => key H₀ χ₀ _ a ((f1.2 a).1 ha).2, hd, fun i j a ha => (hV V ρ).1 i j a ha,
    fun a ha => (hV V ρ).2 a ha⟩

theorem smul_mem_cut (hP : IdemP) (ρ : Representation K G V) {A : Submodule (𝓞 K) V}
    (hA : ∀ g : G, ∀ a ∈ A, ρ g a ∈ A) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (g : G)
    {p : V →ₗ[K] V} (hp : ∀ a, p (p a) = p a) {a : V} (ha : a ∈ A)
    (hx : p ((epP H χ ρ ∘ₗ ρ g) a) = (epP H χ ρ ∘ₗ ρ g) a) :
    (Fintype.card G : 𝓞 K) • (epP H χ ρ ∘ₗ ρ g) a ∈ cut A p := by
  rw [mem_cut hp]
  refine ⟨((hP K G V ρ).2 H χ).2 A hA _ (hA g a ha), ?_⟩
  rw [map_osmul, hx]

variable {S : Type} [Fintype S] {T : S → Type} [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
  [∀ s, FiniteDimensional K (T s)] {τ : ∀ s, Representation K G (T s)}

theorem sandwich (hE : IdemE) (hP : IdemP) (hτ : IsGood τ) (ρ : Representation K G V)
    {A : Submodule (𝓞 K) V} (hA : ∀ g : G, ∀ a ∈ A, ρ g a ∈ A) (H : Subgroup G)
    (χ : H →* (𝓞 K)ˣ) :
    (∀ s, cut A (epP H χ ρ ∘ₗ eS (τ s) ρ) ≤ cut A (epP H χ ρ ∘ₗ eGood τ ρ)) ∧
    (∀ a ∈ cut A (epP H χ ρ ∘ₗ eGood τ ρ),
      (Fintype.card G : 𝓞 K) • a ∈ ⨆ s, cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) ∧
    ∀ s, ∀ a ∈ cut A (epP H χ ρ ∘ₗ eS (τ s) ρ), eS (τ s) ρ a = a := by
  obtain ⟨he, ho⟩ := hE K G S T τ hτ V ρ
  obtain ⟨hE', hEp⟩ := hP K G V ρ
  have f := fun s => pe_facts (hEp H χ).1 (he s) ((hE' (T s) (τ s)).2.1 H χ)
  have hge : ∀ s a, eGood τ ρ (eS (τ s) ρ a) = eS (τ s) ρ a := by
    intro s a
    classical
    unfold eGood
    rw [LinearMap.sum_apply, Finset.sum_eq_single s]
    · exact LinearMap.congr_fun (he s) a
    · intro t _ hts
      exact LinearMap.congr_fun (ho t s hts) a
    · simp
  refine ⟨fun s a ha => ⟨ha.1, ?_⟩, fun a ha => ?_, fun s a ha => ?_⟩
  · obtain ⟨z, hz⟩ := ha.2
    refine ⟨eS (τ s) ρ z, ?_⟩
    rw [← hz]
    simp only [LinearMap.comp_apply, hge]
  · obtain ⟨haA, z, hz⟩ := ha
    have hz' : a = ∑ s, epP H χ ρ (eS (τ s) ρ z) := by
      rw [← hz]
      simp only [LinearMap.comp_apply, eGood, LinearMap.sum_apply, map_sum]
    have hs : ∀ s, eS (τ s) ρ a = epP H χ ρ (eS (τ s) ρ z) := by
      intro s
      have h2 : ∀ a, eS (τ s) ρ (epP H χ ρ a) = epP H χ ρ (eS (τ s) ρ a) :=
        fun a => LinearMap.congr_fun ((hE' (T s) (τ s)).2.1 H χ) a
      have h3 : eS (τ s) ρ (eGood τ ρ z) = eS (τ s) ρ z := by
        classical
        unfold eGood
        rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single s]
        · exact LinearMap.congr_fun (he s) z
        · intro t _ hts
          exact LinearMap.congr_fun (ho s t hts.symm) z
        · simp
      rw [← hz, LinearMap.comp_apply, h2, h3]
    have : (Fintype.card G : 𝓞 K) • a = ∑ s, (Fintype.card G : 𝓞 K) • eS (τ s) ρ a := by
      rw [← Finset.smul_sum]
      simp only [hs]
      rw [← hz']
    rw [this]
    refine Submodule.sum_mem _ fun s _ => Submodule.mem_iSup_of_mem s ?_
    rw [mem_cut (f s).1]
    refine ⟨(hE' (T s) (τ s)).2.2 A hA a haA, ?_⟩
    rw [map_osmul, hs]
    exact congrArg _ ((f s).1 z)
  · exact (((f s).2 a).1 ((mem_cut (f s).1).1 ha).2).2

end

end Formalism.IndefR.LatticeTransfer.Lat
end
end

section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement Formalism.HN _root_.Formalism.IndefR.LatticeTransfer.Lat

theorem Lat.log_le_half {n N : ℕ} (h : n ^ 2 ≤ N) :
    Real.log n ≤ Real.log N / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Real.log_natCast_nonneg N
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · have h1 : Real.log ((n : ℝ) ^ 2) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by exact_mod_cast h)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith

theorem Lat.cube_mem {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    {B : Submodule (𝓞 K) V} {N : 𝓞 K} {z : V} (h : N • z ∈ B) : N ^ 3 • z ∈ B := by
  have : N ^ 3 • z = N ^ 2 • N • z := by rw [smul_smul]; ring_nf
  rw [this]
  exact B.smul_mem _ h

set_option maxHeartbeats 400000 in
theorem all_parts_transfer_of_facts (hE : IdemE) (hP : IdemP) (hC : Core) (hD : DimSq) (hM : Metric) :
    AllPartsTransfer := by
  intro K _ _ _ _ G _ _ S _ T _ _ _ τ H₀ χ₀ H χ hτ hM1 V _ _ _ _ ι _ _ b X ρ hX hU A hA
  obtain ⟨hfg, hspan, hst⟩ := hA
  have : FiniteDimensional K V := Module.Finite.of_basis b
  choose γ δ c Γ hcore using hC K G S T τ H₀ χ₀ H χ hτ hM1
  obtain ⟨he, ho⟩ := hE K G S T τ hτ V ρ
  have tr := fun s => tr_of_core hP (hcore s) ρ (he s)
  obtain ⟨hsa, hnorm⟩ := hM K G V ι b X ρ hX hU
  have hN : 0 < Fintype.card G := Fintype.card_pos
  have hla : 0 ≤ Real.log (Fintype.card G : ℝ) := Real.log_natCast_nonneg _
  have horth : ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) s t, s ≠ t →
      Formalism.BranchingDeterminantCap.OrthAt b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) (cut A (epP H χ ρ ∘ₗ eS (τ t) ρ)) := by
    intro H χ s t hst' v x hx y hy
    have sw := (sandwich hE hP hτ ρ hst H χ).2.2
    rw [← sw s x hx, hsa, ← sw t y hy]
    have : eS (τ s) ρ (eS (τ t) ρ y) = 0 := LinearMap.congr_fun (ho s t hst') y
    rw [this]
    exact Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_zero_right b X v x
  have sw1 := sandwich hE hP hτ ρ hst H χ
  have sw0 := sandwich hE hP hτ ρ hst H₀ χ₀
  have os1 := Formalism.BranchingDeterminantCap.orthSandwich K V ι b X hX S (fun s => cut A (epP H χ ρ ∘ₗ eS (τ s) ρ))
    (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) (Fintype.card G) (fg_cut hfg _) hN (horth H χ) sw1.1 sw1.2.1
  have os0 := Formalism.BranchingDeterminantCap.orthSandwich K V ι b X hX S (fun s => cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))
    (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) (Fintype.card G) (fg_cut hfg _) hN (horth H₀ χ₀) sw0.1
    sw0.2.1
  have hrk : ∀ s, rkK (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) =
      nS (τ s) H χ * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) := fun s => by
    rw [rkK_cut hspan, rkK_cut hspan]; exact (tr s).rank
  have hxm : ∀ s j, ∀ a ∈ cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ),
      ((Fintype.card G : 𝓞 K) ^ 3) • (epP H χ ρ ∘ₗ ρ (γ s j)) a ∈
        cut A (epP H χ ρ ∘ₗ eS (τ s) ρ) := fun s j a ha =>
    cube_mem (smul_mem_cut hP ρ hst H χ _ (tr s).2.1 ha.1
      ((tr s).2.2.1 j a ((mem_cut (tr s).1).1 ha).2))
  have hym : ∀ s i, ∀ a ∈ cut A (epP H χ ρ ∘ₗ eS (τ s) ρ),
      ((Fintype.card G : 𝓞 K) ^ 3) • (epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) a ∈
        cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) := fun s i a ha =>
    cube_mem (smul_mem_cut hP ρ hst H₀ χ₀ _ (tr s).1 ha.1
      ((tr s).2.2.2.1 i a ((mem_cut (tr s).2.1).1 ha).2))
  have hyi : ∀ s, ∀ a ∈ cut A (epP H χ ρ ∘ₗ eS (τ s) ρ),
      (∀ i, (epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) a = 0) → a = 0 := fun s a ha h0 =>
    (tr s).inj_y a ((mem_cut (tr s).2.1).1 ha).2 h0
  have hrk0 : rkK (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) =
      ∑ s, nS (τ s) H χ * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) := by
    rw [os1.1]; exact Finset.sum_congr rfl fun s _ => hrk s
  have h3a : ∀ s, |degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) -
      (nS (τ s) H χ : ℝ) * degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))| ≤
      (6 * Real.log (Fintype.card G) + Real.log (nS (τ s) H χ)) *
        ((nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))) := by
    intro s
    by_cases hn : nS (τ s) H χ = 0
    · simp [degT, hrk s, hn]
    by_cases hr : cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) = ⊥
    · have h0 : rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) = 0 := by
        rw [hr]; simp [rkK]
      simp [degT, hrk s, h0]
    exact Formalism.BranchingDeterminantCap.transferPart K V ι b X hX _ _ _ (Fintype.card G)
      (fun j => epP H χ ρ ∘ₗ ρ (γ s j)) (fun i => epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) (fg_cut hfg _)
      (fg_cut hfg _) hr (Nat.pos_of_ne_zero hn) hN (hxm s) (hym s) (fun i v => hnorm H χ _ v)
      (fun i v => hnorm H₀ χ₀ _ v)
      (fun a ha h0 => (tr s).first_axis_injective a (fun j => ((mem_cut (tr s).1).1 (ha j)).2) h0) (hyi s) (hrk s)
  have h3b : ∀ s, (6 * Real.log (Fintype.card G) + Real.log (nS (τ s) H χ)) *
        ((nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))) ≤
      6.5 * Real.log (Fintype.card G) *
        ((nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))) := by
    intro s
    have := log_le_half ((hD K G S T τ hτ s).2 H χ)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hcast : ((∑ s, nS (τ s) H χ * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) : ℕ) : ℝ) =
      ∑ s, (nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) := by push_cast; rfl
  have o12 : ∑ s, degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) ≤
      degT b X (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) := os1.2.1
  have o13 : degT b X (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) ≤
      ∑ s, degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) + 2 * Real.log (Fintype.card G) *
        (rkK (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) : ℝ) := os1.2.2
  have o02 : ∑ s, degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) ≤
      degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) := os0.2.1
  have o03 : degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) ≤
      ∑ s, degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) + 2 * Real.log (Fintype.card G) *
        (rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) : ℝ) := os0.2.2
  rw [hrk0] at o13
  rw [os0.1, Nat.cast_sum] at o03
  have h4 := Formalism.BranchingDeterminantCap.transferDeg S (fun s => (rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) : ℝ))
    (fun s => (nS (τ s) H χ : ℝ)) (fun s => degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)))
    (fun s => degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ))) (Real.log (Fintype.card G))
    (degT b X (cut A (epP H χ ρ ∘ₗ eGood τ ρ)))
    (fun s => ((h3a s).trans (h3b s)).trans (le_of_eq (by norm_num))) o12 (by rw [← hcast]; exact o13)
    hla (fun s => by positivity)
  have h810 : 8.5 * Real.log (Fintype.card G : ℝ) ≤ 10 * Real.log (Fintype.card G : ℝ) := by
    linarith only [hla]
  have h85 : (17 / 2 : ℝ) = 8.5 := by norm_num
  rw [h85, ← hcast] at h4
  refine ⟨⟨hrk, hrk0⟩, ⟨iSup_le sw1.1, sw1.2.1, fun s t hst' x hx y hy v => horth H χ s t hst' v x hx y hy,
    sub_nonneg.2 o12, sub_le_iff_le_add'.2 o13, sub_nonneg.2 o02, sub_le_iff_le_add'.2 o03⟩,
    fun s => ⟨h3a s, h3b s⟩, ⟨?_, ?_⟩, fun h0 => ⟨?_, add_le_add_right h810 _⟩⟩
  · exact h4
  · exact mul_le_mul_of_nonneg_right h810 (Nat.cast_nonneg _)
  · have := Formalism.BranchingDeterminantCap.transferMuMax K V ι b X hX S (fun s => cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))
      (fun s => cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) (cut A (epP H χ ρ ∘ₗ eGood τ ρ))
      (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) (Fintype.card G) (fun s => nS (τ s) H χ)
      (fun s i => epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) (fg_cut hfg _) (fg_cut hfg _) h0 hN
      (fun s => (hD K G S T τ hτ s).2 H χ) (horth H χ) sw1.1 sw1.2.1 sw0.1 hym
      (fun s i v => hnorm H₀ χ₀ _ v) hyi
    rw [h85] at this
    exact this

end Formalism.IndefR.LatticeTransfer
end
end

section
open Module NumberField

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace CharacterLemmas

theorem trace_of_diag {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I] [DecidableEq I]
    (v : Basis I ℂ V) (h : V →ₗ[ℂ] V) (c : I → ℂ) (hv : ∀ i, h (v i) = c i • v i) :
    LinearMap.trace ℂ V h = ∑ i, c i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ v h, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hv i, map_smul, Basis.repr_self]
  simp

theorem eigen_data {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ∃ (I : Type) (_ : Fintype I) (μ : I → ℂ), Fintype.card I = finrank ℂ V ∧
      (∀ i, μ i ^ orderOf g = 1) ∧ LinearMap.trace ℂ V (ρ g) = ∑ i, μ i ∧
      LinearMap.trace ℂ V (ρ g⁻¹) = ∑ i, starRingEnd ℂ (μ i) := by
  classical
  set s : Module.End ℂ V := ρ g with hs
  set n := orderOf g with hn
  have hn0 : 0 < n := orderOf_pos g
  have hsn : s ^ n = 1 := by rw [hs, ← map_pow, hn, pow_orderOf_eq_one, map_one]
  have hsq : Squarefree (Polynomial.X ^ n - 1 : Polynomial ℂ) :=
    (Polynomial.X_pow_sub_one_separable_iff.mpr (by exact_mod_cast hn0.ne')).squarefree
  have hss : s.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (by simp [hsn])
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    s.eigenspaces_iSupIndep hss.iSup_eigenspace_eq_top
  let I := (ν : ℂ) × Fin (finrank ℂ (s.eigenspace ν))
  let v : Basis I ℂ V := eigenDecomp.collectedBasis fun μ ↦ finBasis ℂ (s.eigenspace μ)
  have hI : Fintype I := FiniteDimensional.fintypeBasisIndex v
  let μ : I → ℂ := Sigma.fst
  have hsv (i : I) : s (v i) = μ i • v i :=
    Module.End.mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ i)
  have hpow : ∀ (i : I) (k : ℕ), (s ^ k) (v i) = μ i ^ k • v i := by
    intro i k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hsv, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hμn : ∀ i, μ i ^ n = 1 := by
    intro i
    have h1 := hpow i n
    rw [hsn, Module.End.one_apply] at h1
    have h2 : (μ i ^ n - 1) • v i = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 (v.ne_zero i)
  have hμ0 : ∀ i, μ i ≠ 0 := by
    intro i h0
    have := hμn i
    rw [h0, zero_pow hn0.ne'] at this
    exact zero_ne_one this
  have hinv : ∀ i, ρ g⁻¹ (v i) = (starRingEnd ℂ) (μ i) • v i := by
    intro i
    have h1 : ρ g⁻¹ (s (v i)) = v i := by
      rw [hs, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hsv, map_smul] at h1
    have h2 : (μ i)⁻¹ = (starRingEnd ℂ) (μ i) :=
      Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (hμn i) hn0.ne')
    rw [← h2]
    calc ρ g⁻¹ (v i) = (μ i)⁻¹ • (μ i • ρ g⁻¹ (v i)) := by
          rw [smul_smul, inv_mul_cancel₀ (hμ0 i), one_smul]
      _ = (μ i)⁻¹ • v i := by rw [h1]
  exact ⟨I, hI, μ, (finrank_eq_card_basis v).symm, hμn, trace_of_diag v _ μ hsv,
    trace_of_diag v _ _ hinv⟩

theorem char_complex {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    IsIntegral ℤ (LinearMap.trace ℂ V (ρ g)) ∧
      LinearMap.trace ℂ V (ρ g⁻¹) = star (LinearMap.trace ℂ V (ρ g)) ∧
      ‖LinearMap.trace ℂ V (ρ g)‖ ≤ (finrank ℂ V : ℝ) := by
  obtain ⟨I, hI, μ, hcard, hμ, htr, htr'⟩ := eigen_data ρ g
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [htr]
    refine IsIntegral.sum _ fun i _ => ?_
    refine IsIntegral.of_pow (orderOf_pos g) ?_
    rw [hμ i]
    exact isIntegral_one
  · rw [htr', htr, star_sum]
    rfl
  · rw [htr]
    calc ‖∑ i, μ i‖ ≤ ∑ i, ‖μ i‖ := norm_sum_le _ _
      _ = ∑ _i : I, (1 : ℝ) := Finset.sum_congr rfl fun i _ => by
          have h1 : ‖μ i‖ ^ orderOf g = 1 := by rw [← norm_pow, hμ i, norm_one]
          exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h1
      _ = (finrank ℂ V : ℝ) := by simp [hcard]

def repC {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Group G] {T : Type} [AddCommGroup T]
    [Module K T] [FiniteDimensional K T] (τ : Representation K G T) :
    Representation ℂ G (Fin (finrank K T) → ℂ) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin (finrank K T)) (Fin (finrank K T)) ℂ ≃ₐ[ℂ] _) :
      Matrix (Fin (finrank K T)) (Fin (finrank K T)) ℂ →* _).comp
    (((σ.mapMatrix : Matrix (Fin (finrank K T)) (Fin (finrank K T)) K →+* _) :
        Matrix (Fin (finrank K T)) (Fin (finrank K T)) K →* _).comp
      (((LinearMap.toMatrixAlgEquiv (Module.finBasis K T)) : (T →ₗ[K] T) →* _).comp τ))

theorem trace_repC {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Group G] {T : Type}
    [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T) (g : G) :
    LinearMap.trace ℂ _ (repC σ τ g) = σ (charOf τ g) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin (finrank K T))), charOf,
    LinearMap.trace_eq_matrix_trace K (Module.finBasis K T) (τ g)]
  simp [repC, LinearMap.toMatrix_eq_toMatrix', Matrix.trace, map_sum, LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.toMatrix_apply]

end CharacterLemmas

open CharacterLemmas

theorem charFacts : CharFacts := by
  intro K _ _ G _ _ T _ _ _ τ g
  have hmain : ∀ σ : K →+* ℂ, IsIntegral ℤ (σ (charOf τ g)) ∧
      σ (charOf τ g⁻¹) = star (σ (charOf τ g)) ∧ ‖σ (charOf τ g)‖ ≤ (finrank K T : ℝ) := by
    intro σ
    obtain ⟨h1, h2, h3⟩ := char_complex (repC σ τ) g
    rw [trace_repC, trace_repC] at h2
    rw [trace_repC] at h1 h3
    refine ⟨h1, h2, ?_⟩
    simpa using h3
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩
  refine ⟨?_, fun σ' => ⟨(hmain σ').2.1, (hmain σ').2.2⟩⟩
  exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).1 (hmain σ).1

theorem liftChar : LiftChar := by
  intro K _ _ H _ _ χ
  have hint : ∀ h, IsIntegral ℤ ((χ h : Kˣ) : K) := by
    intro h
    refine IsIntegral.of_pow (orderOf_pos h) ?_
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
    exact isIntegral_one
  let φ : H →* 𝓞 K :=
    { toFun := fun h => ⟨((χ h : Kˣ) : K), hint h⟩
      map_one' := by
        apply RingOfIntegers.ext
        show ((χ 1 : Kˣ) : K) = 1
        rw [map_one, Units.val_one]
      map_mul' := fun a b => by
        apply RingOfIntegers.ext
        show ((χ (a * b) : Kˣ) : K) = ((χ a : Kˣ) : K) * ((χ b : Kˣ) : K)
        rw [map_mul, Units.val_mul] }
  exact ⟨φ.toHomUnits, fun h => rfl⟩

theorem dimSq_of (h : Schur) : DimSq := by
  intro K _ _ G _ _ S T _ _ _ τ hgood s
  obtain ⟨-, -, hsum⟩ := h K G S T τ hgood
  have hs := hsum s
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩
  have hdim : charOf (τ s) 1 = (finrank K (T s) : K) := by
    unfold charOf
    rw [map_one, LinearMap.trace_one]
  have hterm : ∀ x : G, σ (charOf (τ s) x⁻¹ * charOf (τ s) x) =
      ((‖σ (charOf (τ s) x)‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [map_mul, ((charFacts K G (T s) (τ s) x).2 σ).1]
    push_cast
    exact Complex.conj_mul' _
  have e1 := congrArg σ hs
  rw [map_sum, map_natCast] at e1
  simp_rw [hterm] at e1
  have e2 : (∑ x : G, ‖σ (charOf (τ s) x)‖ ^ 2 : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast e1
  have key : ((finrank K (T s) : ℝ)) ^ 2 ≤ (Fintype.card G : ℝ) := by
    rw [← e2]
    have h1 : ‖σ (charOf (τ s) 1)‖ ^ 2 = ((finrank K (T s) : ℝ)) ^ 2 := by
      rw [hdim, map_natCast, Complex.norm_natCast]
    rw [← h1]
    exact Finset.single_le_sum (f := fun x : G => ‖σ (charOf (τ s) x)‖ ^ 2)
      (fun x _ => by positivity) (Finset.mem_univ 1)
  have key' : finrank K (T s) ^ 2 ≤ Fintype.card G := by exact_mod_cast key
  refine ⟨key', fun H χ => le_trans ?_ key'⟩
  exact Nat.pow_le_pow_left (Submodule.finrank_le _) 2

end Formalism.IndefR.LatticeTransfer
end
end

section
open Module NumberField Matrix

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace BlockMetrics

section Forms

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)

theorem fc_smul (c : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  have h : Formalism.HermitianLatticesTheory.vecAt b v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.vecAt b v x := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]
  simp only [Formalism.HermitianLatticesTheory.fcoord, h, Matrix.mulVec_smul]

def fcA : V →+ (ι → ℂ) :=
  AddMonoidHom.mk' (Formalism.HermitianLatticesTheory.fcoord b X v) (Formalism.HermitianLatticesTheory.fcoord_add b X v)

theorem fc_sum {α : Type} (s : Finset α) (f : α → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ a ∈ s, f a) = ∑ a ∈ s, Formalism.HermitianLatticesTheory.fcoord b X v (f a) := by
  exact map_sum (fcA b X v) f s

theorem maj_sum_left {α : Type} (s : Finset α) (c : α → K) (f : α → V) (y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (∑ a ∈ s, c a • f a) y =
      ∑ a ∈ s, star (v.embedding (c a)) * Formalism.HermitianLatticesTheory.majAt b X v (f a) y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem maj_sum_right {α : Type} (s : Finset α) (c : α → K) (f : α → V) (x : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (∑ a ∈ s, c a • f a) =
      ∑ a ∈ s, v.embedding (c a) * Formalism.HermitianLatticesTheory.majAt b X v x (f a) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem maj_add_left (x x' y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (x + x') y = Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x' y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, star_add, add_mul,
    Finset.sum_add_distrib]

theorem maj_add_right (x y y' : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (y + y') = Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x y' := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

theorem maj_smul_left (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (a • x) y = starRingEnd ℂ (v.embedding a) * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply]
  ring

theorem maj_smul_right (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (a • y) = v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem maj_self (x : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x x = ((Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 : ℝ) : ℂ) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' _

theorem normAt_eq_sqrt (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  rw [maj_self, Complex.ofReal_re, Real.sqrt_sq]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  exact Real.sqrt_nonneg _

theorem normAt_eq_norm (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x =
      ‖(WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]

theorem fcoord_map (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] V) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (φ x) =
      ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v).mulVec
        (Formalism.HermitianLatticesTheory.fcoord b X v x) := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (φ x) =
      ((LinearMap.toMatrix b b φ).map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← LinearMap.toMatrix_mulVec_repr b b φ x, RingHom.map_mulVec]
    rfl
  simp only [Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]

end Forms

theorem dense_emb {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsComplex) :
    DenseRange v.embedding := by
  rcases Complex.subfield_eq_of_closed (v.embedding.fieldRange.isClosed_topologicalClosure) with h | h
  · exfalso
    have hr : ComplexEmbedding.IsReal v.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      have hx : v.embedding x ∈ v.embedding.fieldRange.topologicalClosure :=
        v.embedding.fieldRange.le_topologicalClosure (RingHom.mem_fieldRange.2 ⟨x, rfl⟩)
      rw [h] at hx
      obtain ⟨r, hr⟩ := RingHom.mem_fieldRange.1 hx
      rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
      simp
    exact (InfinitePlace.isComplex_iff.1 hv) hr
  · intro z
    have hz : z ∈ v.embedding.fieldRange.topologicalClosure := by
      rw [h]; exact Subfield.mem_top z
    have hc : (v.embedding.fieldRange.topologicalClosure : Set ℂ) = closure (Set.range v.embedding) := by
      rw [← RingHom.coe_fieldRange]; rfl
    rw [← hc]; exact hz

theorem dense_fcoord {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    DenseRange fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι) := by
  have hemb : DenseRange v.embedding := dense_emb v (IsTotallyComplex.isComplex v)
  have h1 : DenseRange fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x := by
    have hpi : DenseRange (Pi.map fun _ : ι => v.embedding) := DenseRange.piMap fun _ => hemb
    have hr : Set.range (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) =
        Set.range (Pi.map fun _ : ι => v.embedding) := by
      ext u; constructor
      · rintro ⟨x, rfl⟩; exact ⟨fun i => b.repr x i, rfl⟩
      · rintro ⟨c, rfl⟩
        refine ⟨b.equivFun.symm c, ?_⟩
        funext i
        have hc := congr_fun (b.equivFun.apply_symm_apply c) i
        rw [Basis.equivFun_apply] at hc
        show v.embedding (b.repr (b.equivFun.symm c) i) = v.embedding (c i)
        rw [hc]
    rw [DenseRange, hr]; exact hpi
  have h2 : Continuous fun u : ι → ℂ => (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι) := by
    fun_prop
  have h3 : Function.Surjective fun u : ι → ℂ =>
      (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι) := by
    intro w
    refine ⟨(X v).mulVec (WithLp.ofLp w), ?_⟩
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v)]
  exact h3.denseRange.comp h1 h2

theorem opNormAt_le_of_points {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (φ : V →ₗ[K] V) (v : InfinitePlace K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, Formalism.HermitianLatticesTheory.normAt b X v (φ f) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v f) :
    Formalism.HN.opNormAt b X b X v φ ≤ C := by
  unfold Formalism.HN.opNormAt
  set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v)) with hTd
  refine ContinuousLinearMap.opNorm_le_bound T hC fun u => ?_
  refine (dense_fcoord b X hX v).induction_on (p := fun w => ‖T w‖ ≤ C * ‖w‖) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro f
    have hT : T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)) =
        WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (φ f)) := by
      rw [fcoord_map b X v hX φ f]; rfl
    show ‖T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f))‖ ≤ C * ‖WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)‖
    rw [hT, ← normAt_eq_norm, ← normAt_eq_norm]
    exact h f

theorem sesq_ext {K V : Type} [Field K] [AddCommGroup V] [Module K V] {F G : V → V → ℂ}
    {σ : K →+* ℂ} (hσ : ∃ a : K, (σ a).im ≠ 0)
    (hF : (∀ x x' y, F (x + x') y = F x y + F x' y) ∧ (∀ x y y', F x (y + y') = F x y + F x y') ∧
      (∀ (a : K) x y, F (a • x) y = starRingEnd ℂ (σ a) * F x y) ∧
      (∀ (a : K) x y, F x (a • y) = σ a * F x y))
    (hG : (∀ x x' y, G (x + x') y = G x y + G x' y) ∧ (∀ x y y', G x (y + y') = G x y + G x y') ∧
      (∀ (a : K) x y, G (a • x) y = starRingEnd ℂ (σ a) * G x y) ∧
      (∀ (a : K) x y, G x (a • y) = σ a * G x y))
    (h : ∀ x, F x x = G x x) (x y : V) : F x y = G x y := by
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨F1, F2, F3, F4⟩ := hF
  obtain ⟨G1, G2, G3, G4⟩ := hG
  have e1 := h (x + y)
  have e2 := h (a • x + y)
  simp only [F1, F2, F3, F4, G1, G2, G3, G4] at e1 e2
  rw [h x, h y] at e1 e2
  have hne : starRingEnd ℂ (σ a) - σ a ≠ 0 := by
    intro h0
    apply ha
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have key : (starRingEnd ℂ (σ a) - σ a) * (F x y - G x y) = 0 := by
    linear_combination e2 - σ a * e1
  rcases mul_eq_zero.1 key with h0 | h0
  · exact absurd h0 hne
  · exact sub_eq_zero.1 h0

theorem exists_im_ne_zero {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (v : InfinitePlace K) : ∃ a : K, (v.embedding a).im ≠ 0 := by
  have hv := IsTotallyComplex.isComplex v
  rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hv
  by_contra hcon
  push_neg at hcon
  apply hv
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hcon a)

end BlockMetrics

open BlockMetrics

private theorem normAt_smul_indefinite_real {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (a • x) = ‖v.embedding a‖ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  rw [normAt_eq_norm, normAt_eq_norm, fc_smul, WithLp.toLp_smul, norm_smul]

private theorem normAt_add_le {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + y) ≤ Formalism.HermitianLatticesTheory.normAt b X v x + Formalism.HermitianLatticesTheory.normAt b X v y := by
  rw [normAt_eq_norm, normAt_eq_norm, normAt_eq_norm, Formalism.HermitianLatticesTheory.fcoord_add, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem normAt_finset_sum_le {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {α : Type} (s : Finset α)
    (f : α → V) :
    Formalism.HermitianLatticesTheory.normAt b X v (∑ a ∈ s, f a) ≤ ∑ a ∈ s, Formalism.HermitianLatticesTheory.normAt b X v (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (normAt_smul_indefinite_real b X v (0 : K) (0 : V)).le
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (normAt_add_le b X v _ _).trans (add_le_add le_rfl ih)

theorem metric : Metric := by
  intro K _ _ _ _ G _ _ V _ _ _ _ ι _ _ b X ρ hX hU
  have hinv : ∀ (g : G) (y : V), ρ g (ρ g⁻¹ y) = y := by
    intro g y
    show (ρ g * ρ g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hρ : ∀ (v : InfinitePlace K) (g : G) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y) := by
    intro v g x y
    calc Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y
        = Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) (ρ g (ρ g⁻¹ y)) := by rw [hinv]
      _ = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y) := hU v g x _
  refine ⟨fun T _ _ _ τ v x y => ?_, fun H χ g v => ?_⟩
  · have hc := fun g => (charFacts K G T τ g).2 v.embedding
    have hc1 : starRingEnd ℂ (v.embedding (charOf τ 1 / (Fintype.card G : K))) =
        v.embedding (charOf τ 1 / (Fintype.card G : K)) := by
      have h1 := (hc 1).1
      rw [inv_one] at h1
      simp only [map_div₀, map_natCast]
      rw [starRingEnd_apply, ← h1]
    simp only [Formalism.IndefR.TransferLatticeStatement.eS, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [maj_smul_left, maj_smul_right, maj_sum_left, maj_sum_right, hc1]
    congr 1
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
    have hg := (hc g⁻¹).1
    rw [inv_inv] at hg
    simp only [Equiv.inv_apply, inv_inv]
    rw [hρ, ← hg]
  · have hρn : ∀ (k : G) (z : V), Formalism.HermitianLatticesTheory.normAt b X v (ρ k z) = Formalism.HermitianLatticesTheory.normAt b X v z := by
      intro k z; rw [normAt_eq_sqrt, hU, ← normAt_eq_sqrt]
    have hχ : ∀ h : H, ‖v.embedding (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1 := by
      intro h
      rw [InfinitePlace.norm_embedding_eq]
      have ht : χ h⁻¹ ∈ NumberField.Units.torsion K := χ.isOfFinOrder (isOfFinOrder_of_finite h⁻¹)
      exact (NumberField.Units.mem_torsion K).1 ht v
    refine opNormAt_le_of_points b X hX _ v 1 zero_le_one fun f => ?_
    rw [one_mul, LinearMap.comp_apply]
    simp only [Formalism.IndefR.TransferLatticeStatement.epP, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [normAt_smul_indefinite_real]
    refine (mul_le_mul_of_nonneg_left (normAt_finset_sum_le b X v _ _) (norm_nonneg _)).trans ?_
    simp only [normAt_smul_indefinite_real, hχ, hρn, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
    rw [Fintype.card_eq_nat_card, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.card_pos (α := H)).ne'), one_mul]


end Formalism.IndefR.LatticeTransfer
end
end

section
open Module NumberField

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace IdempotentLemmas

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

lemma charOf_conj {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (g h : G) : charOf τ (h * g * h⁻¹) = charOf τ g := by
  unfold charOf
  by_cases hf : Module.Finite K T
  · rw [map_mul τ, map_mul τ, LinearMap.trace_mul_comm K (τ h * τ g), ← mul_assoc, ← map_mul τ,
      inv_mul_cancel, map_one, one_mul]
  · have h0 : LinearMap.trace K T = 0 := by
      first
      | exact LinearMap.trace_eq_zero_of_not_finite hf
      | exact LinearMap.trace_eq_zero_of_not_finite (R := K) (M := T) hf
      | (rw [LinearMap.trace, dif_neg]; rintro ⟨_, ⟨b⟩⟩; exact hf (Module.Finite.of_basis b))
      | (unfold LinearMap.trace; rw [dif_neg]; rintro ⟨_, ⟨b⟩⟩; exact hf (Module.Finite.of_basis b))
    simp [h0]

lemma eS_mul_rho {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (y : G) :
    eS τ ρ * ρ y = (charOf τ 1 / (Fintype.card G : K)) • ∑ g : G, charOf τ (y * g⁻¹) • ρ g := by
  unfold eS
  rw [smul_mul_assoc, Finset.sum_mul]
  congr 1
  simp_rw [smul_mul_assoc, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight y) _ _ (fun x => by simp [mul_inv_rev])

lemma eS_mul_asAlg {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (a : MonoidAlgebra K G) :
    eS τ ρ * ρ.asAlgebraHom a = (charOf τ 1 / (Fintype.card G : K)) •
      ∑ g : G, LinearMap.trace K T (τ.asAlgebraHom a * τ g⁻¹) • ρ g := by
  induction a using MonoidAlgebra.induction_on with
  | of y =>
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of, eS_mul_rho]
    simp only [charOf, ← map_mul]
  | add f g hf hg =>
    rw [map_add, mul_add, hf, hg, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_add, add_mul, map_add, add_smul]
  | smul r f hf =>
    rw [map_smul, mul_smul_comm, hf, smul_comm r, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_mul_assoc, map_smul, smul_eq_mul, mul_smul]

lemma eS_comm {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (g : G) :
    eS τ ρ * ρ g = ρ g * eS τ ρ := by
  rw [eS_mul_rho]
  unfold eS
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  simp_rw [mul_smul_comm, ← map_mul]
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulLeft]
  congr 1
  rw [show g * (g * x)⁻¹ = g * x⁻¹ * g⁻¹ by group, charOf_conj]

lemma trace_eS {T U : Type} [AddCommGroup T] [Module K T] [AddCommGroup U] [Module K U]
    (τ : Representation K G T) (σ : Representation K G U) :
    LinearMap.trace K U (eS τ σ) =
      charOf τ 1 / (Fintype.card G : K) * ∑ x : G, charOf τ x⁻¹ * charOf σ x := by
  unfold eS
  rw [map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

lemma sum_char_eq [CharZero K] {T U : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K G T) (σ : Representation K G U) :
    ∑ x : G, charOf τ x⁻¹ * charOf σ x =
      (Fintype.card G : K) * finrank K (Representation.IntertwiningMap τ σ) := by
  have hc : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have : Invertible (Nat.card G : K) := invertibleOfNonzero hc
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank τ σ
  rw [← Nat.card_eq_fintype_card, ← h, mul_inv_cancel_left₀ hc]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_comm]
  rfl

lemma finrank_int_self {T : Type} [AddCommGroup T] [Module K T] [Nontrivial T]
    (τ : Representation K G T)
    (h : ∀ f : T →ₗ[K] T, (∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f) → ∃ c : K, f = c • LinearMap.id) :
    finrank K (Representation.IntertwiningMap τ τ) = 1 := by
  have hne : Representation.IntertwiningMap.id τ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : T)
    intro h0
    apply hv
    have := congrArg (fun f : Representation.IntertwiningMap τ τ => f v) h0
    simpa using this
  rw [finrank_eq_one_iff_of_nonzero' _ hne]
  intro w
  obtain ⟨c, hc⟩ := h w.toLinearMap (fun g => w.isIntertwining' g)
  refine ⟨c, ?_⟩
  apply DFunLike.ext
  intro v
  have hv : w v = c • v := by
    rw [← Representation.IntertwiningMap.toLinearMap_apply, hc]
    simp
  rw [hv]
  simp

lemma int_eq_zero {T U : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K G T) (σ : Representation K G U)
    (hτ : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hσ : ∀ W : Submodule K U, (∀ g : G, ∀ w ∈ W, σ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hch : charOf τ ≠ charOf σ) (f : Representation.IntertwiningMap τ σ) : f = 0 := by
  by_contra hf
  have hf' : f.toLinearMap ≠ 0 := fun h =>
    hf (Representation.IntertwiningMap.ext (by simpa using h))
  have hker : LinearMap.ker f.toLinearMap = ⊥ := by
    rcases hτ (LinearMap.ker f.toLinearMap) (fun g w hw => by
      simp only [LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hw ⊢
      rw [f.isIntertwining, hw, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hf'
  have hrange : LinearMap.range f.toLinearMap = ⊤ := by
    rcases hσ (LinearMap.range f.toLinearMap) (fun g w hw => by
      obtain ⟨v, rfl⟩ := hw
      exact ⟨τ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hf'
    · exact h
  let e : T ≃ₗ[K] U := LinearEquiv.ofBijective f.toLinearMap
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩
  have he : ∀ x, e x = f x := fun x => rfl
  apply hch
  funext g
  have hconj : e.conj (τ g) = σ g := by
    apply LinearMap.ext
    intro u
    rw [LinearEquiv.conj_apply_apply, he, f.isIntertwining, ← he, LinearEquiv.apply_symm_apply]
  show LinearMap.trace K T (τ g) = LinearMap.trace K U (σ g)
  rw [← hconj, LinearMap.trace_conj']

def eAlg {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T) :
    MonoidAlgebra K G :=
  ∑ x : G, MonoidAlgebra.single x (charOf τ 1 / (Fintype.card G : K) * charOf τ x⁻¹)

lemma asAlg_eAlg {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) :
    ρ.asAlgebraHom (eAlg τ) = eS τ ρ := by
  unfold eAlg eS
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.asAlgebraHom_single, mul_smul]

lemma comm_epP [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (X : Module.End K V) (hX : ∀ g, X * ρ g = ρ g * X)
    (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) : X * epP H χ ρ = epP H χ ρ * X := by
  unfold epP
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, hX]

lemma idem_gen {V : Type} [AddCommGroup V] [Module K V] {H : Type} [Group H] {_ : Fintype H}
    (a : H → K) (ha : ∀ h k, a h * a k = a (h * k)) (π : H →* Module.End K V)
    (hn : (Nat.card H : K) ≠ 0) :
    ((Nat.card H : K)⁻¹ • ∑ h : H, a h • π h) * ((Nat.card H : K)⁻¹ • ∑ h : H, a h • π h) =
      (Nat.card H : K)⁻¹ • ∑ h : H, a h • π h := by
  have key : (∑ h : H, a h • π h) * (∑ h : H, a h • π h) = (Nat.card H : K) • ∑ h : H, a h • π h := by
    rw [Finset.sum_mul]
    have e0 : ∀ h : H, (a h • π h) * ∑ k : H, a k • π k = ∑ m : H, a m • π m := by
      intro h
      rw [Finset.mul_sum]
      have e : ∀ k : H, (a h • π h) * (a k • π k) = a (h * k) • π (h * k) := by
        intro k
        rw [smul_mul_smul_comm, ha, map_mul]
      simp_rw [e]
      exact Equiv.sum_comp (Equiv.mulLeft h) (fun m => a m • π m)
    simp_rw [e0]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card]
  rw [smul_mul_smul_comm, key, smul_smul]
  congr 1
  field_simp

end IdempotentLemmas

open IdempotentLemmas

theorem keyZero : KeyZero := by
  intro K _ G _ _ T _ _ τ V _ _ ρ a ha
  rw [← Module.End.mul_eq_comp]
  simpa [ha] using eS_mul_asAlg τ ρ a

theorem schur : Schur := by
  intro K _ _ G _ _ S T _ _ _ τ hgood
  obtain ⟨hnt, hirr, habs, hinj⟩ := hgood
  have hcomm : ∀ s t, ∃ c : K, eS (τ s) (τ t) = c • LinearMap.id := fun s t =>
    habs t _ (fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
      exact eS_comm (τ s) (τ t) g)
  have hdim : ∀ s, charOf (τ s) 1 = (finrank K (T s) : K) := fun s => by
    unfold charOf
    rw [map_one, LinearMap.trace_one]
  have hpos : ∀ s, (finrank K (T s) : K) ≠ 0 := fun s => by
    haveI := hnt s
    exact_mod_cast (Module.finrank_pos (R := K) (M := T s)).ne'
  have hcard : (Fintype.card G : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htr : ∀ s t, LinearMap.trace K (T t) (eS (τ s) (τ t)) =
      (finrank K (T s) : K) * finrank K (Representation.IntertwiningMap (τ s) (τ t)) := by
    intro s t
    rw [trace_eS, sum_char_eq, hdim]
    field_simp
  have hone : ∀ s, finrank K (Representation.IntertwiningMap (τ s) (τ s)) = 1 := fun s => by
    haveI := hnt s
    exact finrank_int_self (τ s) (habs s)
  have hsum : ∀ s, ∑ x : G, charOf (τ s) x⁻¹ * charOf (τ s) x = (Fintype.card G : K) := by
    intro s
    rw [sum_char_eq, hone s, Nat.cast_one, mul_one]
  refine ⟨fun s => ?_, fun s t hst => ?_, hsum⟩
  · obtain ⟨c, hc⟩ := hcomm s s
    have h1 := htr s s
    rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul, hone s, Nat.cast_one, mul_one] at h1
    have h2 : (c - 1) * (finrank K (T s) : K) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    have h3 : c = 1 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (hpos s))
    rw [hc, h3, one_smul]
  · obtain ⟨c, hc⟩ := hcomm s t
    have hne : charOf (τ s) ≠ charOf (τ t) := fun h => hst (hinj s t h)
    haveI : Subsingleton (Representation.IntertwiningMap (τ s) (τ t)) :=
      ⟨fun f g => (int_eq_zero (τ s) (τ t) (hirr s) (hirr t) hne f).trans
        (int_eq_zero (τ s) (τ t) (hirr s) (hirr t) hne g).symm⟩
    have h1 := htr s t
    rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul,
      Module.finrank_zero_of_subsingleton (R := K) (M := Representation.IntertwiningMap (τ s) (τ t)),
      Nat.cast_zero, mul_zero] at h1
    have h3 : c = 0 := (mul_eq_zero.1 h1).resolve_right (hpos t)
    rw [hc, h3, zero_smul]

theorem idemE : IdemE := by
  intro K _ _ G _ _ S T _ _ _ τ hgood V _ _ ρ
  obtain ⟨h1, h2, -⟩ := schur K G S T τ hgood
  have key : ∀ s t, eS (τ s) ρ ∘ₗ eS (τ t) ρ = (charOf (τ s) 1 / (Fintype.card G : K)) •
      ∑ g : G, LinearMap.trace K (T s) (eS (τ t) (τ s) * τ s g⁻¹) • ρ g := by
    intro s t
    rw [← Module.End.mul_eq_comp, ← asAlg_eAlg (τ t) ρ, eS_mul_asAlg, asAlg_eAlg]
  refine ⟨fun s => ?_, fun s t hst => ?_⟩
  · rw [key, h1 s]
    unfold eS
    congr 1
  · rw [key, h2 t s (Ne.symm hst)]
    simp

theorem idemP_of (h : CharFacts) : IdemP := by
  intro K _ _ G _ _ V _ _ _ _ ρ
  have hs' : ∀ (r : 𝓞 K) (v : V), ((r : K)) • v = r • v := fun r v => algebraMap_smul K r v
  have hcard : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨fun T _ _ _ τ => ⟨fun g => eS_comm τ ρ g,
    fun H χ => comm_epP ρ (eS τ ρ) (fun g => eS_comm τ ρ g) H χ, fun A hA a ha => ?_⟩,
    fun H χ => ⟨?_, fun A hA a ha => ?_⟩⟩
  · have hint : ∀ x : G, IsIntegral ℤ (charOf τ 1 * charOf τ x⁻¹) :=
      fun x => (h K G T τ 1).1.mul (h K G T τ x⁻¹).1
    have hd : (Fintype.card G : K) * (charOf τ 1 / (Fintype.card G : K)) = charOf τ 1 := by
      field_simp
    rw [← hs', show ((Fintype.card G : 𝓞 K) : K) = (Fintype.card G : K) by simp, eS,
      LinearMap.smul_apply, smul_smul, hd, LinearMap.sum_apply, Finset.smul_sum]
    refine A.sum_mem fun x _ => ?_
    rw [LinearMap.smul_apply, smul_smul]
    have hx : charOf τ 1 * charOf τ x⁻¹ ∈ integralClosure ℤ K := hint x
    let r : 𝓞 K := ⟨_, hx⟩
    have hm := A.smul_mem r (hA x a ha)
    have he : (charOf τ 1 * charOf τ x⁻¹) • ρ x a = r • ρ x a := hs' r (ρ x a)
    rw [he]
    exact hm
  · have hn : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    show epP H χ ρ * epP H χ ρ = epP H χ ρ
    unfold epP
    exact idem_gen (fun h : H => (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K))
      (fun h k => by simp only [mul_inv_rev, map_mul, Units.val_mul]; ring)
      (ρ.comp H.subtype) hn
  · have hn : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hI : ((Fintype.card G : 𝓞 K) : K) * (Nat.card H : K)⁻¹ = ((H.index : 𝓞 K) : K) := by
      have hG : (Fintype.card G : K) = (Nat.card H : K) * H.index := by
        rw [← Nat.card_eq_fintype_card, ← H.card_mul_index, Nat.cast_mul]
      simp only [map_natCast]
      rw [hG]
      field_simp
    rw [← hs']
    unfold epP
    rw [LinearMap.smul_apply, smul_smul, hI, hs', LinearMap.sum_apply]
    refine A.smul_mem _ (A.sum_mem fun h _ => ?_)
    rw [LinearMap.smul_apply, hs']
    exact A.smul_mem _ (hA _ _ ha)

end Formalism.IndefR.LatticeTransfer
end
end

section
open Module NumberField

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace NormTraceLemmas

section Lin

variable {K : Type} [Field K] {G : Type} [Group G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]

theorem exists_strictHenselian_absolutely_closed_local_ring (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ε₀ ε : T →ₗ[K] T) (h1 : finrank K (LinearMap.range ε₀) = 1) :
    ∃ (γ δ : Fin (finrank K (LinearMap.range ε)) → G)
      (c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K),
      c.det ≠ 0 ∧
      (∀ i j, c i j = LinearMap.trace K T (ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j))) ∧
      (∀ i j, ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j) ∘ₗ ε₀ = c i j • ε₀) ∧
      ∑ j, ∑ i, c⁻¹ j i • (ε ∘ₗ τ (γ j) ∘ₗ ε₀ ∘ₗ τ (δ i) ∘ₗ ε) = ε := by
  first | exact Bl.RankOneOrbitForms.goal1 .. | (apply Bl.RankOneOrbitForms.goal1 <;> assumption) | (intros; apply Bl.RankOneOrbitForms.goal1 <;> assumption)

end Lin

section Char

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]

open Classical in

theorem trace_formula (τ : Representation K G T) (H₀ H : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ)
    (χ : H →* (𝓞 K)ˣ) (a b : G) :
    LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) =
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹) *
        ∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b) := by
  simp only [← Module.End.mul_eq_comp, epP, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_smul, map_sum, smul_eq_mul, ← map_mul, charOf, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h₀ _ => Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul (algebraMap (𝓞 K) K)]
  ring

theorem norm_chi (H : Subgroup G) [Finite H] (χ : H →* (𝓞 K)ˣ) (h : H) (σ : K →+* ℂ) :
    ‖σ (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1 := by
  have hu : ((χ h : (𝓞 K)ˣ) : 𝓞 K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have h2 : σ (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) ^ Nat.card H = 1 := by
    have := congrArg (σ.comp (algebraMap (𝓞 K) K)) hu
    rw [map_pow, map_one] at this
    exact this
  exact Complex.norm_eq_one_of_pow_eq_one h2 Nat.card_pos.ne'

variable [NumberField K]

theorem norm_trace_le (hC : CharFacts) (τ : Representation K G T) (H₀ H : Subgroup G)
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b))‖ ≤ (finrank K T : ℝ) := by
  classical
  rw [trace_formula, map_mul, norm_mul]
  have hA : ‖σ ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹)‖ =
      (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ := by
    simp [map_mul, map_inv₀, map_natCast, norm_inv]
  rw [hA]
  have hB : ‖σ (∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b))‖ ≤
      ∑ _h₀ : H₀, ∑ _h : H, (finrank K T : ℝ) := by
    rw [map_sum]
    refine norm_sum_le_of_le _ fun h₀ _ => ?_
    rw [map_sum]
    refine norm_sum_le_of_le _ fun h _ => ?_
    rw [map_mul, map_mul, norm_mul, norm_mul, norm_chi, norm_chi, one_mul, one_mul]
    exact ((hC K G T τ _).2 σ).2
  have hpos : (0 : ℝ) ≤ (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ := by positivity
  calc (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ * ‖_‖ ≤
        (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ * ∑ _h₀ : H₀, ∑ _h : H, (finrank K T : ℝ) :=
        mul_le_mul_of_nonneg_left hB hpos
    _ = (finrank K T : ℝ) := by
        have h0 : (Nat.card H₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        have h1 : (Nat.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
        field_simp

theorem integral_mem (hC : CharFacts) (τ : Representation K G T) (H₀ H : Subgroup G)
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) :
    (Fintype.card G : K) ^ 2 * LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) ∈
      integralClosure ℤ K := by
  classical
  rw [trace_formula]
  have hG0 : (Fintype.card G : K) = (Nat.card H₀ : K) * (H₀.index : K) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hG1 : (Fintype.card G : K) = (Nat.card H : K) * (H.index : K) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hsq : (Fintype.card G : K) ^ 2 =
      ((Nat.card H₀ : K) * (H₀.index : K)) * ((Nat.card H : K) * (H.index : K)) := by
    rw [sq]
    nth_rw 1 [hG0]
    rw [hG1]
  have h0 : (Nat.card H₀ : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hsq, show ∀ x : K, (Nat.card H₀ : K) * (H₀.index : K) * ((Nat.card H : K) * (H.index : K)) *
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹ * x) = (H₀.index : K) * (H.index : K) * x from
      fun x => by field_simp]
  refine mul_mem (mul_mem (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _))
    (Subalgebra.sum_mem _ fun h₀ _ => Subalgebra.sum_mem _ fun h _ => mul_mem (mul_mem ?_ ?_) ?_)
  · exact RingOfIntegers.isIntegral_coe _
  · exact RingOfIntegers.isIntegral_coe _
  · exact (hC K G T τ _).1

end Char

section Alg

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

open Classical in

def epA (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) : MonoidAlgebra K G :=
  ((Nat.card H : ℕ) : K)⁻¹ •
    ∑ h : H, MonoidAlgebra.single (h : G) ((((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K))

theorem asAlg_epA (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) : ρ.asAlgebraHom (epA H χ) = epP H χ ρ := by
  simp only [epA, epP, map_smul, map_sum, Representation.asAlgebraHom_single]

def eA {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T) : MonoidAlgebra K G :=
  (charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, MonoidAlgebra.single x (charOf τ x⁻¹)

theorem asAlg_eA {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) :
    ρ.asAlgebraHom (eA τ) = eS τ ρ := by
  simp only [eA, eS, map_smul, map_sum, Representation.asAlgebraHom_single]

end Alg

end NormTraceLemmas

open NormTraceLemmas in

theorem core_of (hC : CharFacts) (hK : KeyZero) (hS : Schur) (hP : IdemP) : Core := by
  intro K _ _ G _ _ S T _ _ _ τ H₀ χ₀ H χ hgood hM1 s
  obtain ⟨γ, δ, c, hdet, htr, he1, he2⟩ :=
    exists_strictHenselian_absolutely_closed_local_ring (τ s) (hgood.2.1 s) (epP H₀ χ₀ (τ s)) (epP H χ (τ s)) (hM1 s)
  refine ⟨γ, δ, c, fun i j => ⟨(Fintype.card G : K) ^ 2 * c i j, ?_⟩, hdet, fun i j => rfl, ?_, ?_⟩
  · rw [htr i j]
    exact integral_mem hC (τ s) H₀ H χ₀ χ (δ i) (γ j)
  · intro i j σ
    rw [htr i j]
    exact norm_trace_le hC (τ s) H₀ H χ₀ χ (δ i) (γ j) σ
  · intro V _ _ ρ
    let _ : Module (𝓞 K) V := Module.compHom V (algebraMap (𝓞 K) K)
    have : IsScalarTower (𝓞 K) K V := ⟨fun x y v => by
      change (x • y) • v = (algebraMap (𝓞 K) K x) • (y • v)
      rw [Algebra.smul_def, mul_smul]⟩
    obtain ⟨hPe, hPε⟩ := hP K G V ρ
    obtain ⟨hcg, hcε, -⟩ := hPe (T s) (τ s)
    have ce_g : ∀ g x, eS (τ s) ρ (ρ g x) = ρ g (eS (τ s) ρ x) :=
      fun g x => LinearMap.congr_fun (hcg g) x
    have ce₀ : ∀ x, eS (τ s) ρ (epP H₀ χ₀ ρ x) = epP H₀ χ₀ ρ (eS (τ s) ρ x) :=
      fun x => LinearMap.congr_fun (hcε H₀ χ₀) x
    have ce : ∀ x, eS (τ s) ρ (epP H χ ρ x) = epP H χ ρ (eS (τ s) ρ x) :=
      fun x => LinearMap.congr_fun (hcε H χ) x
    have ii₀ : ∀ x, epP H₀ χ₀ ρ (epP H₀ χ₀ ρ x) = epP H₀ χ₀ ρ x :=
      fun x => LinearMap.congr_fun (hPε H₀ χ₀).1 x
    have ii : ∀ x, epP H χ ρ (epP H χ ρ x) = epP H χ ρ x :=
      fun x => LinearMap.congr_fun (hPε H χ).1 x
    have hee : ∀ x, eS (τ s) ρ (eS (τ s) ρ x) = eS (τ s) ρ x := by
      intro x
      have h0 : (τ s).asAlgebraHom (eA (τ s) - 1) = 0 := by
        rw [map_sub, asAlg_eA, (hS K G S T τ hgood).1 s, map_one, Module.End.one_eq_id, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ h0) x
      simp only [LinearMap.comp_apply, map_sub, asAlg_eA, map_one, LinearMap.sub_apply,
        Module.End.one_apply, LinearMap.zero_apply, sub_eq_zero] at this
      exact this
    constructor
    · intro i j a ha
      have ea : eS (τ s) ρ a = a := by
        calc eS (τ s) ρ a = eS (τ s) ρ (epP H₀ χ₀ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ce₀, hee, ha]
      have e0a : epP H₀ χ₀ ρ a = a := by
        calc epP H₀ χ₀ ρ a = epP H₀ χ₀ ρ (epP H₀ χ₀ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ii₀, ha]
      have hx : (τ s).asAlgebraHom (epA H₀ χ₀ * MonoidAlgebra.of K G (δ i) * epA H χ *
          MonoidAlgebra.of K G (γ j) * epA H₀ χ₀ - c i j • epA H₀ χ₀) = 0 := by
        simp only [map_sub, map_mul, map_smul, asAlg_epA, Representation.asAlgebraHom_of,
          Module.End.mul_eq_comp, LinearMap.comp_assoc]
        rw [he1 i j, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ hx) a
      simp only [LinearMap.comp_apply, map_sub, map_mul, map_smul, asAlg_epA,
        Representation.asAlgebraHom_of, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply, LinearMap.zero_apply, ce₀, ce_g, ce, ea, e0a, sub_eq_zero] at this
      exact this
    · intro a ha
      have ea : eS (τ s) ρ a = a := by
        calc eS (τ s) ρ a = eS (τ s) ρ (epP H χ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ce, hee, ha]
      have Ea : epP H χ ρ a = a := by
        calc epP H χ ρ a = epP H χ ρ (epP H χ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ii, ha]
      have hy : (τ s).asAlgebraHom (∑ j, ∑ i, c⁻¹ j i • (epA H χ * MonoidAlgebra.of K G (γ j) *
          epA H₀ χ₀ * MonoidAlgebra.of K G (δ i) * epA H χ) - epA H χ) = 0 := by
        simp only [map_sub, map_sum, map_mul, map_smul, asAlg_epA, Representation.asAlgebraHom_of,
          Module.End.mul_eq_comp, LinearMap.comp_assoc]
        rw [he2, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ hy) a
      simp only [LinearMap.comp_apply, map_sub, map_sum, map_mul, map_smul, asAlg_epA,
        Representation.asAlgebraHom_of, LinearMap.sub_apply, LinearMap.sum_apply,
        Module.End.mul_apply, LinearMap.smul_apply, LinearMap.zero_apply, ce₀, ce_g, ce, ea, Ea,
        sub_eq_zero] at this
      exact this

end Formalism.IndefR.LatticeTransfer
end
end

section
namespace Formalism.IndefR.LatticeTransfer

theorem dimSq : DimSq := dimSq_of schur

theorem idemP : IdemP := idemP_of charFacts

theorem core : Core := core_of charFacts keyZero schur idemP

theorem all_parts_transfer_holds : AllPartsTransfer := all_parts_transfer_of_facts idemE idemP core dimSq metric

end Formalism.IndefR.LatticeTransfer
end

section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.L2.GlobalTheoryTheory.DivPassage

theorem levelAmb_transfer
    {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {D0 D1 : ℕ}
    (A : LevelAmb K D0 D1) {G : Type} [Group G] [Fintype G] {T : A.S → Type}
    [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)] [∀ s, FiniteDimensional K (T s)]
    (τ : ∀ s, Representation K G (T s)) (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G)
    (χ : H →* (𝓞 K)ˣ) (ρ : Representation K G (Fin A.Dg → K))
    (hτ : IsGood τ) (hM : M1 τ H₀ χ₀)
    (h0 : A.ep0.mulVecLin = epP H₀ χ₀ ρ) (h1 : A.ep1.mulVecLin = epP H χ ρ)
    (hs : ∀ s, (A.es s).mulVecLin = eS (τ s) ρ) (hn : ∀ s, A.nS s = nS (τ s) H χ)
    (hG : A.G = Fintype.card G) (hgood : eGood τ ρ = LinearMap.id)
    (hX : A.FramesG) (hL : A.LatG) (hst : ∀ g : G, ∀ a ∈ A.Rg, ρ g a ∈ A.Rg)
    (hU : IsUnitaryRep (Pi.basisFun K (Fin A.Dg)) A.Xg ρ) :
    A.Ranks ∧ A.Deg0 ∧ A.Deg1 ∧ (A.latticeAtSharpLevel ≠ ⊥ → A.MaxT) := by
  have h15 := all_parts_transfer_holds
  have hlat : IsGLat ρ A.Rg := ⟨hL.fg, hL.span_eq_top, hst⟩
  have p := h15 K G A.S T τ H₀ χ₀ H χ hτ hM _ _ (Pi.basisFun K (Fin A.Dg)) A.Xg ρ hX hU A.Rg hlat
  have q := h15 K G A.S T τ H₀ χ₀ H₀ χ₀ hτ hM _ _ (Pi.basisFun K (Fin A.Dg)) A.Xg ρ hX hU A.Rg hlat
  have e0 : A.latticeAtBaseLevel = cut A.Rg (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ) := by
    rw [hgood, LinearMap.comp_id, ← h0]; rfl
  have e1 : A.latticeAtSharpLevel = cut A.Rg (epP H χ ρ ∘ₗ eGood τ ρ) := by
    rw [hgood, LinearMap.comp_id, ← h1]; rfl
  have es : ∀ s, A.Rs s = cut A.Rg (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) := fun s => by
    rw [← h0, ← hs, ← Matrix.mulVecLin_mul]; rfl
  unfold TransferLatticeConditions at p q
  dsimp only at p q
  simp only [← e0, ← e1, ← es, ← hn, ← hG] at p
  have hM' : ∀ s, nS (τ s) H₀ χ₀ = 1 := hM
  simp only [← e0, ← es, hM', one_mul] at q
  obtain ⟨⟨-, r1⟩, ⟨-, -, -, -, -, -, d0⟩, -, ⟨d1, -⟩, m⟩ := p
  have r0 := q.1.2
  have h85 : (8.5 : ℝ) = 17 / 2 := by norm_num
  rw [h85] at d1 m
  refine ⟨⟨r0, r1⟩, ?_, ?_, fun h => (m h).1⟩
  · unfold LevelAmb.Deg0
    rw [r0, Nat.cast_sum]
    exact sub_le_iff_le_add'.1 d0
  · unfold LevelAmb.Deg1
    rw [r1]
    have := (abs_le.1 d1).1
    exact sub_le_iff_le_add.2 (by
      have h2 := neg_le_sub_iff_le_add.1 this
      exact h2)

end Formalism.IndefR.LatticeTransfer
end
end
