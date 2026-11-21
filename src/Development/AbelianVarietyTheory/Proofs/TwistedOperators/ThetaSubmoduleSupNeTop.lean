import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RkSubSuccLe
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingTopEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmIndCoinvariants
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq

section
section
namespace GlobalTheory

theorem card_record_indices_le_of_chain_bound {α : Type} [Preorder α] (Q : α → Prop) (L : ℕ)
    (h : ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q (N i)) → r ≤ L)
    {r : ℕ} (a : Fin r → α) (ha : ∀ i, Q (a i)) (T : Finset (Fin r))
    (hT : ∀ j ∈ T, ∀ i < j, a i < a j) : T.card ≤ L := by
  refine h T.card (fun k => a (T.orderEmbOfFin rfl k)) ?_ (fun k => ha _)
  intro k k' hk
  exact hT _ (T.orderEmbOfFin_mem rfl k') _ ((T.orderEmbOfFin rfl).strictMono hk)

theorem modular_chain_bound_add {α : Type} [Lattice α] [IsModularLattice α] (C : α)
    (Q Q1 Q2 : α → Prop) (L1 L2 : ℕ)
    (hQ1 : ∀ x, Q x → Q1 (x ⊓ C)) (hQ2 : ∀ x, Q x → Q2 (x ⊔ C))
    (h1 : ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q1 (N i)) → r ≤ L1)
    (h2 : ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q2 (N i)) → r ≤ L2)
    (r : ℕ) (N : Fin r → α) (hN : StrictMono N) (hQ : ∀ i, Q (N i)) : r ≤ L1 + L2 := by
  classical
  let Ta : Finset (Fin r) := Finset.univ.filter fun j => ∀ i < j, N i ⊓ C < N j ⊓ C
  let Tb : Finset (Fin r) := Finset.univ.filter fun j => ∀ i < j, N i ⊔ C < N j ⊔ C
  have hA : Ta.card ≤ L1 :=
    card_record_indices_le_of_chain_bound Q1 L1 h1 (fun i => N i ⊓ C) (fun i => hQ1 _ (hQ i)) Ta
      (fun j hj => (Finset.mem_filter.1 hj).2)
  have hB : Tb.card ≤ L2 :=
    card_record_indices_le_of_chain_bound Q2 L2 h2 (fun i => N i ⊔ C) (fun i => hQ2 _ (hQ i)) Tb
      (fun j hj => (Finset.mem_filter.1 hj).2)
  have hU : (Finset.univ : Finset (Fin r)) ⊆ Ta ∪ Tb := by
    intro j _
    by_contra hj
    simp only [Ta, Tb, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
      not_forall] at hj
    obtain ⟨⟨i, hi, hia⟩, ⟨i', hi', hib⟩⟩ := hj
    have hk : max i i' < j := max_lt hi hi'
    have ea : N i ⊓ C = N j ⊓ C :=
      eq_of_le_of_not_lt (inf_le_inf_right C (hN hi).le) hia
    have eb : N i' ⊔ C = N j ⊔ C :=
      eq_of_le_of_not_lt (sup_le_sup_right (hN hi').le C) hib
    have e : N (max i i') = N j :=
      eq_of_le_of_inf_le_of_sup_le (hN hk).le
        (ea ▸ inf_le_inf_right C (hN.monotone (le_max_left i i')))
        (eb ▸ sup_le_sup_right (hN.monotone (le_max_right i i')) C)
    exact (hN hk).ne e
  have := (Finset.card_le_card hU).trans (Finset.card_union_le Ta Tb)
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_length_bound_of_sup_inf : ∀ {α : Type} [Lattice α] [IsModularLattice α] (C : α) (Q Q1 Q2 : α → Prop) (L1 L2 : ℕ),
    (∀ x, Q x → Q1 (x ⊓ C)) → (∀ x, Q x → Q2 (x ⊔ C)) →
    (∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q1 (N i)) → r ≤ L1) →
    (∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q2 (N i)) → r ≤ L2) →
    ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q (N i)) → r ≤ L1 + L2 := by
  atlas_forward_decl GlobalTheory.modular_chain_bound_add
end

section
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology

namespace GlobalTheory.ThetaGLCover

section Homog

variable {H Y : Type} [Group H] [TopologicalSpace H] [TopologicalSpace Y] [T2Space Y]

def orbInd (r : Y → H → Y) (hc : ∀ y, Continuous (r y)) (ho : ∀ y, IsOpenMap (r y)) (y : Y) {K : Subgroup H}
    (h1 : IsOpen (K : Set H)) (h2 : IsCompact (K : Set H)) : SB Y :=
  ⟨(r y '' K).indicator fun _ => 1,
    GlobalTheory.SBExtend.indicator_mem_SB (h2.image (hc y)) ⟨(h2.image (hc y)).isClosed, ho y _ h1⟩⟩

variable {r : Y → H → Y} (hc : ∀ y, Continuous (r y)) (ho : ∀ y, IsOpenMap (r y))
  (h1 : ∀ x, r x 1 = x) (hm : ∀ x g h, r x (g * h) = r (r x g) h)

include h1 hm in

theorem exists_sum_orbInd {K : Subgroup H} (hK1 : IsOpen (K : Set H)) (hK2 : IsCompact (K : Set H)) (Φ : SB Y)
    (hΦ : ∀ y, ∀ x ∈ K, Φ.1 (r y x) = Φ.1 y) :
    ∃ t : Finset Y, (∀ y ∈ t, Φ.1 y ≠ 0) ∧ Φ = ∑ y ∈ t, Φ.1 y • orbInd r hc ho y hK1 hK2 := by
  classical
  obtain ⟨s, hs⟩ := Φ.2.2.isCompact.elim_finite_subcover (fun y => r y '' K) (fun y => ho y _ hK1)
    (fun y _ => Set.mem_iUnion.2 ⟨y, 1, K.one_mem, h1 y⟩)
  have hs' : ∀ z, Φ.1 z ≠ 0 → ∃ y ∈ s, z ∈ r y '' K := fun z hz => by
    simpa using hs (subset_tsupport _ hz)
  clear hs
  induction s using Finset.induction_on generalizing Φ with
  | empty =>
    refine ⟨∅, by simp, Subtype.ext (funext fun z => ?_)⟩
    by_contra hz
    simpa using hs' z hz
  | insert y s _ ih =>
    have hval : ∀ z ∈ r y '' K, Φ.1 z = Φ.1 y := by
      rintro _ ⟨x, hx, rfl⟩
      exact hΦ y x hx
    have hinv : ∀ z, ∀ x ∈ K, (r z x ∈ r y '' K ↔ z ∈ r y '' K) := by
      intro z x hx
      constructor
      · rintro ⟨u, hu, e⟩
        exact ⟨u * x⁻¹, K.mul_mem hu (K.inv_mem hx), by rw [hm, e, ← hm, mul_inv_cancel, h1]⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u * x, K.mul_mem hu hx, hm _ _ _⟩
    set Ψ : SB Y := Φ - Φ.1 y • orbInd r hc ho y hK1 hK2 with hΨ
    have hΨv : ∀ z, Ψ.1 z = Φ.1 z - Φ.1 y * (r y '' K).indicator (fun _ => (1 : ℂ)) z := fun _ => rfl
    have hin : ∀ z ∈ r y '' K, Ψ.1 z = 0 := fun z hz => by
      rw [hΨv, Set.indicator_of_mem hz, hval z hz, mul_one, sub_self]
    have hout : ∀ z ∉ r y '' K, Ψ.1 z = Φ.1 z := fun z hz => by
      rw [hΨv, Set.indicator_of_notMem hz, mul_zero, sub_zero]
    obtain ⟨t, ht, e⟩ := ih Ψ (fun z x hx => by
        by_cases hz : z ∈ r y '' K
        · rw [hin z hz, hin _ ((hinv z x hx).2 hz)]
        · rw [hout z hz, hout _ (mt (hinv z x hx).1 hz), hΦ z x hx])
      (fun z hz => by
        have hz' : z ∉ r y '' K := fun h => hz (hin z h)
        obtain ⟨u, hu, h⟩ := hs' z (by rwa [← hout z hz'])
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact absurd h hz'
        · exact ⟨u, hu, h⟩)
    have ht' : ∀ z ∈ t, Ψ.1 z = Φ.1 z := fun z hz => hout z fun h => ht z hz (hin z h)
    have e' : Ψ = ∑ z ∈ t, Φ.1 z • orbInd r hc ho z hK1 hK2 :=
      e.trans (Finset.sum_congr rfl fun z hz => by rw [ht' z hz])
    by_cases hy : Φ.1 y = 0
    · refine ⟨t, fun z hz => ht' z hz ▸ ht z hz, ?_⟩
      rw [← e', hΨ, hy, zero_smul, sub_zero]
    · have hyt : y ∉ t := fun h => ht y h (hin y ⟨1, K.one_mem, h1 y⟩)
      refine ⟨insert y t, fun z hz => ?_, ?_⟩
      · rcases Finset.mem_insert.1 hz with rfl | hz
        · exact hy
        · exact ht' z hz ▸ ht z hz
      · rw [Finset.sum_insert hyt, ← e', hΨ, add_sub_cancel]

variable {M : Type} [AddCommGroup M] [Module ℂ M] (c : H →* ℂˣ) (l : SB Y →ₗ[ℂ] M)
  (hl : ∀ h (Φ Φ' : SB Y), (∀ y, Φ'.1 y = (c h : ℂ) * Φ.1 (r y h)) → l Φ' = l Φ)

include h1 hm hl in
theorem map_orbInd_translate (y : Y) (h : H) {K K' : Subgroup H} (hK1 : IsOpen (K : Set H))
    (hK2 : IsCompact (K : Set H)) (hK1' : IsOpen (K' : Set H)) (hK2' : IsCompact (K' : Set H))
    (hKK : ∀ x, x ∈ K' ↔ h⁻¹ * x * h ∈ K) :
    l (orbInd r hc ho (r y h) hK1 hK2) = (c h : ℂ) • l (orbInd r hc ho y hK1' hK2') := by
  rw [← map_smul]
  refine (hl h _ _ fun z => ?_).symm
  show (c h : ℂ) * (r y '' K').indicator (fun _ => (1 : ℂ)) z =
    (c h : ℂ) * (r (r y h) '' K).indicator (fun _ => (1 : ℂ)) (r z h)
  have : z ∈ r y '' K' ↔ r z h ∈ r (r y h) '' K := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, (hKK u).1 hu, by rw [← hm, ← hm]; congr 1; group⟩
    · rintro ⟨u, hu, e⟩
      refine ⟨h * u * h⁻¹, (hKK _).2 (by simpa [mul_assoc] using hu), ?_⟩
      rw [hm, hm, e, ← hm, mul_inv_cancel, h1]
  by_cases hz : z ∈ r y '' K'
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (this.1 hz)]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (mt this.2 hz)]

include h1 hm hl in
theorem map_orbInd_normal (y : Y) {K J : Subgroup H} (hK1 : IsOpen (K : Set H))
    (hK2 : IsCompact (K : Set H)) (hJ1 : IsOpen (J : Set H)) (hJ2 : IsCompact (J : Set H))
    (hKc : ∀ x ∈ K, c x = 1) (hJK : J ≤ K) (hn : ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    ∃ a : ℂ, a ≠ 0 ∧ l (orbInd r hc ho y hK1 hK2) = a • l (orbInd r hc ho y hJ1 hJ2) := by
  have hv : ∀ z, (orbInd r hc ho y hK1 hK2).1 z = (r y '' K).indicator (fun _ => (1 : ℂ)) z := fun _ => rfl
  obtain ⟨t, ht, e⟩ := exists_sum_orbInd hc ho h1 hm hJ1 hJ2 (orbInd r hc ho y hK1 hK2) (fun z x hx => by
    have : r z x ∈ r y '' K ↔ z ∈ r y '' K := by
      constructor
      · rintro ⟨u, hu, e⟩
        exact ⟨u * x⁻¹, K.mul_mem hu (K.inv_mem (hJK hx)), by rw [hm, e, ← hm, mul_inv_cancel, h1]⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u * x, K.mul_mem hu (hJK hx), hm _ _ _⟩
    rw [hv, hv]
    by_cases hz : z ∈ r y '' K
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (this.2 hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (mt this.1 hz)])
  refine ⟨t.card, ?_, ?_⟩
  · intro h0
    have : t = ∅ := Finset.card_eq_zero.1 (by exact_mod_cast h0)
    rw [this, Finset.sum_empty] at e
    have h2 := hv y
    rw [e, Set.indicator_of_mem (show y ∈ r y '' K from ⟨1, K.one_mem, h1 y⟩)] at h2
    exact zero_ne_one h2
  · rw [e, map_sum, Finset.sum_congr rfl (g := fun _ => l (orbInd r hc ho y hJ1 hJ2)), Finset.sum_const,
      Nat.cast_smul_eq_nsmul]
    intro z hz
    have hz' : z ∈ r y '' K := Set.mem_of_indicator_ne_zero (hv z ▸ ht z hz)
    rw [hv, Set.indicator_of_mem hz', one_smul]
    obtain ⟨u, hu, rfl⟩ := hz'
    rw [map_orbInd_translate hc ho h1 hm c l hl y u hJ1 hJ2 hJ1 hJ2 fun x => ⟨fun hx => by
      simpa using hn _ (K.inv_mem hu) x hx, fun hx => by simpa [mul_assoc] using hn _ hu _ hx⟩, hKc u hu]
    simp

include h1 hm hl in
theorem map_orbInd_le [IsTopologicalGroup H] (y : Y) {K J : Subgroup H} (hK1 : IsOpen (K : Set H))
    (hK2 : IsCompact (K : Set H)) (hJ1 : IsOpen (J : Set H)) (hJ2 : IsCompact (J : Set H))
    (hKc : ∀ x ∈ K, c x = 1) (hJK : J ≤ K) :
    ∃ a : ℂ, a ≠ 0 ∧ l (orbInd r hc ho y hK1 hK2) = a • l (orbInd r hc ho y hJ1 hJ2) := by
  let N : Subgroup H :=
    { carrier := {x | ∀ u ∈ K, u * x * u⁻¹ ∈ J}
      one_mem' := fun u _ => by simp
      mul_mem' := fun {x x'} hx hx' u hu => by
        simpa [mul_assoc] using J.mul_mem (hx u hu) (hx' u hu)
      inv_mem' := fun {x} hx u hu => by simpa [mul_assoc] using J.inv_mem (hx u hu) }
  have hNJ : N ≤ J := fun x hx => by simpa using hx 1 K.one_mem
  have hN1 : IsOpen (N : Set H) := by
    refine N.isOpen_of_mem_nhds (g := 1) (hK2.eventually_forall_of_forall_eventually
      (P := fun x u => u * x * u⁻¹ ∈ J) fun u _ => ?_)
    exact (hJ1.preimage (f := fun z : H × H => z.2 * z.1 * z.2⁻¹) (by fun_prop)).mem_nhds (by simp)
  have hN2 : IsCompact (N : Set H) := hJ2.of_isClosed_subset (N.isClosed_of_isOpen hN1) hNJ
  have hn : ∀ x ∈ K, ∀ j ∈ N, x * j * x⁻¹ ∈ N := fun x hx j hj u hu => by
    simpa [mul_assoc] using hj _ (K.mul_mem hu hx)
  obtain ⟨a, ha, e⟩ := map_orbInd_normal hc ho h1 hm c l hl y hK1 hK2 hN1 hN2 hKc (hNJ.trans hJK) hn
  obtain ⟨b, hb, e'⟩ := map_orbInd_normal hc ho h1 hm c l hl y hJ1 hJ2 hN1 hN2 (fun x hx => hKc x (hJK hx)) hNJ
    fun x hx => hn x (hJK hx)
  exact ⟨a / b, div_ne_zero ha hb, by rw [e, e', smul_smul, div_mul_cancel₀ _ hb]⟩

omit hc ho in
include h1 hm hl in

theorem exists_generator [IsTopologicalGroup H] [SigmaCompactSpace H] [LocallyCompactSpace Y]
    (hcc : Continuous fun p : Y × H => r p.1 p.2) (htr : ∀ y y', ∃ h, r y h = y')
    (hb : ∀ U ∈ 𝓝 (1 : H), ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H) ∧ (K : Set H) ⊆ U)
    (hcs : IsSmoothChar c) : ∃ v : M, ∀ Φ, l Φ ∈ Submodule.span ℂ {v} := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y₀⟩⟩
  · exact ⟨0, fun Φ => by rw [show Φ = 0 from Subtype.ext (funext fun y => hY.elim y), map_zero]; exact zero_mem _⟩
  have hc : ∀ y, Continuous (r y) := fun y => hcc.comp (Continuous.prodMk_right y)
  have ho : ∀ y, IsOpenMap (r y) := by
    letI : MulAction H Y :=
      { smul := fun g y => r y g⁻¹
        one_smul := fun y => by show r y 1⁻¹ = y; rw [inv_one, h1]
        mul_smul := fun g h y => by show r y (g * h)⁻¹ = r (r y h⁻¹) g⁻¹; rw [_root_.mul_inv_rev, hm] }
    haveI : ContinuousSMul H Y := ⟨hcc.comp (continuous_snd.prodMk continuous_fst.inv)⟩
    haveI : MulAction.IsPretransitive H Y := ⟨fun y y' => by
      obtain ⟨h, e⟩ := htr y y'
      exact ⟨h⁻¹, by show r y h⁻¹⁻¹ = y'; rw [inv_inv, e]⟩⟩
    intro y
    have := (isOpenMap_smul_of_sigmaCompact (G := H) y).comp (Homeomorph.inv H).isOpenMap
    convert this using 1
    funext g
    show r y g = r y g⁻¹⁻¹
    rw [inv_inv]
  have hker : (c.ker : Set H) ∈ 𝓝 1 := IsOpen.mem_nhds hcs c.ker.one_mem
  obtain ⟨K₀, a1, a2, a3⟩ := hb _ hker
  refine ⟨l (orbInd r hc ho y₀ a1 a2), fun Φ => ?_⟩
  obtain ⟨K, b1, b2, b3⟩ := hb _ (Filter.inter_mem hker
    (GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action H Y r h1 hm hcc Φ))
  obtain ⟨t, -, e⟩ := exists_sum_orbInd hc ho h1 hm b1 b2 Φ fun y x hx => (b3 hx).2 y
  rw [e, map_sum]
  refine Submodule.sum_mem _ fun y _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨h, rfl⟩ := htr y₀ y
  let φ : H ≃ₜ H := (Homeomorph.mulLeft h⁻¹).trans (Homeomorph.mulRight h)
  let K' : Subgroup H := K.comap (MulAut.conj h⁻¹).toMonoidHom
  have hK' : (K' : Set H) = φ ⁻¹' K := by ext x; simp [K', φ]
  have c1 : IsOpen (K' : Set H) := hK' ▸ b1.preimage φ.continuous
  have c2 : IsCompact (K' : Set H) := hK' ▸ φ.isCompact_preimage.2 b2
  have c3 : ∀ x ∈ K', c x = 1 := fun x hx => by
    have : c (h⁻¹ * x * h) = 1 := (b3 (show h⁻¹ * x * h ∈ K by simpa [K'] using hx)).1
    simpa [mul_comm] using this
  rw [map_orbInd_translate hc ho h1 hm c l hl y₀ h b1 b2 c1 c2 fun x => by simp [K']]
  refine Submodule.smul_mem _ _ ?_
  have d1 : IsOpen ((K' ⊓ K₀ : Subgroup H) : Set H) := c1.inter a1
  have d2 : IsCompact ((K' ⊓ K₀ : Subgroup H) : Set H) :=
    c2.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ d1) Set.inter_subset_left
  obtain ⟨a, -, e1⟩ := map_orbInd_le hc ho h1 hm c l hl y₀ c1 c2 d1 d2 c3 inf_le_left
  obtain ⟨b, hb0, e2⟩ := map_orbInd_le hc ho h1 hm c l hl y₀ a1 a2 d1 d2 (fun x hx => a3 hx) inf_le_right
  rw [e1, e2]
  exact Submodule.mem_span_singleton.2 ⟨a / b, by rw [smul_smul, div_mul_cancel₀ _ hb0]⟩

end Homog

section Strata

open GlobalTheory.RankStrataProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

theorem continuous_slice {X G : Type} [TopologicalSpace X] [TopologicalSpace G] (r : X → G → X)
    (h : Continuous fun p : X × G => r p.1 p.2) (g : G) : Continuous fun x => r x g :=
  h.comp (Continuous.prodMk_left g)

def embL (e : c ⊕ d ≃ a) : Levi k (Two c d) →* parabLower k (two e) :=
  (leviEmb k (two e)).codRestrict _ fun _ => leviEmb_mem_parabLower k _ _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem proj_embL (e : c ⊕ d ≃ a) (g : Levi k (Two c d)) : leviProjLower k (two e) (embL e g) = g := by
  funext x
  ext i j
  exact leviEmb_apply_same k (two e) g x i j

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem pAct_embL (e : c ⊕ d ≃ a) (s : Set ℕ) (y : ColZero k b e s) (p : parabLower k (two e)) :
    pAct e s y (embL e (leviProjLower k (two e) p)) = pAct e s y p := by
  rw [← pAct_eq, proj_embL, pAct_eq]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_embL (e : c ⊕ d ≃ a) (p : parabLower k (two e)) :
    GeneralLinearGroup.det (leviEmb k (two e) (leviProjLower k (two e) p)) =
      GeneralLinearGroup.det (p : GL a k) := by
  rw [det_leviEmb]
  exact (det_parab k (opp (two e)) p).symm

variable (k a b) in

def rChar : GL a k →* ℂˣ := (omChar a b 1).comp (MonoidHom.inl _ _)

theorem isSmoothChar_one : IsSmoothChar (1 : kˣ →* ℂˣ) := by unfold IsSmoothChar; simp

theorem isSmoothChar_rChar : IsSmoothChar (rChar k a b) :=
  (isSmoothChar_omChar isSmoothChar_one).comp _ (continuous_id.prodMk continuous_const)

variable (k b) in

def levRep (e : c ⊕ d ≃ a) (s : Set ℕ) : Representation ℂ (Levi k (Two c d)) (SB (ColZero k b e s)) :=
  twist (sbRep (fun y g => pAct e s y (embL e g))
    (fun y => Subtype.ext (by rw [map_one]; exact rAct_one s y.1))
    (fun y g h => Subtype.ext (by rw [map_mul]; exact rAct_mul s y.1 _ _))
    (fun g => ((continuous_rAct s).comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _))
    (deltaHalf k (Two c d) * (rChar k a b).comp (leviEmb k (two e)))

theorem levRep_apply (e : c ⊕ d ≃ a) (s : Set ℕ) (g : Levi k (Two c d)) (Φ : SB (ColZero k b e s))
    (y : ColZero k b e s) : (levRep k b e s g Φ).1 y =
      ((deltaHalf k (Two c d) g * rChar k a b (leviEmb k (two e) g) : ℂˣ) : ℂ) * Φ.1 (pAct e s y (embL e g)) := rfl

theorem isSmooth_levRep (e : c ⊕ d ≃ a) (s : Set ℕ) : IsSmooth (levRep k b e s) := by
  refine isSmooth_twist (isSmooth_of_nhds fun Φ => ?_)
    ((isSmoothChar_deltaHalf k).mul (isSmoothChar_rChar.comp _ (continuous_leviEmb k _)))
  refine (GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action _ (ColZero k b e s)
    (fun y g => pAct e s y (embL e g))
    (fun y => Subtype.ext (by rw [map_one]; exact rAct_one s y.1))
    (fun y g h => Subtype.ext (by rw [map_mul]; exact rAct_mul s y.1 _ _))
    (((continuous_rAct s).comp ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_leviEmb k (two e)).comp continuous_snd))).subtype_mk _) Φ).mono fun u hu => ?_
  exact Subtype.ext (funext hu)

omit [Fintype d] [DecidableEq d] [DecidableEq c] [Fintype c] [DecidableEq a] [DecidableEq b] in
theorem isClosed_colZero (e : c ⊕ d ≃ a) (s : Set ℕ) :
    IsClosed {x : RankIn k a b s | ∀ i j, x.1 i (e (.inr j)) = 0} := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_subtype_val.matrix_elem _ _) continuous_const

theorem exists_indEquiv (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) :
    ∃ E : SB (RankIn k a b {κ}) ≃ₗ[ℂ] IndSpLower (two e) (levRep k b e {κ}),
      ∀ Φ g y, ((E Φ).1.1 g).1 y = (rChar k a b g : ℂ) * Φ.1 (rAct _ y.1 g) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨-, -, -, -, -, -, -, -, hPK⟩ := LeviInt.levi_integral_facts k _ a _ (opp (two e))
  exact GlobalTheory.SBInduced.sb_induced (GL a k) (RankIn k a b {κ}) (ColZero k b e {κ})
    (SB (ColZero k b e {κ})) (rAct {κ}) (rAct_one _) (rAct_mul _) (continuous_rAct _)
    Subtype.val (isClosed_colZero e _).isClosedEmbedding_subtypeVal (parabLower k (two e)) (KO k a)
    SplitFlip.isCompact_KO
    (fun x => by
      obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k b c d a e x.1 (x.2.trans hκ)
      obtain ⟨p, hp', w, hw, h⟩ := hPK g⁻¹
      refine ⟨pAct e _ ⟨rAct _ x g, by rwa [rAct_val]⟩ ⟨p, hp'⟩, w, hw, ?_⟩
      show x = rAct _ (rAct _ (rAct _ x g) p) w
      rw [← rAct_mul, ← rAct_mul, ← h, mul_inv_cancel, rAct_one])
    (pAct e _) (fun _ _ => rfl)
    (fun y y' g h => (mem_parabLower_two k).2 fun i j => by
      refine congrFun (GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k b c d a e y.1.1 (y.1.2.trans hκ) y.2
        (fun m => g.val (e (.inl m)) (e (.inr j))) (funext fun l => ?_)) i
      have := y'.2 l j
      rw [← h, rAct_val, mul_apply_of_cols e y.2] at this
      exact this)
    (rChar k a b) isSmoothChar_rChar _ (LinearEquiv.refl ℂ _)
    (fun p w y => by
      show (((deltaHalf k (Two c d) (leviProjLower k (two e) p))⁻¹ : ℂˣ) : ℂ) *
        (((deltaHalf k (Two c d) (leviProjLower k (two e) p) *
          rChar k a b (leviEmb k (two e) (leviProjLower k (two e) p)) : ℂˣ) : ℂ) *
          w.1 (pAct e _ y (embL e (leviProjLower k (two e) p)))) = _ * w.1 (pAct e _ y p)
      have : rChar k a b (leviEmb k (two e) (leviProjLower k (two e) p)) = rChar k a b p := by
        simp only [rChar, omChar, MonoidHom.comp_apply, MonoidHom.mul_apply, detChar_apply, MonoidHom.inl_apply,
          MonoidHom.coe_fst, MonoidHom.coe_snd, det_embL]
      rw [pAct_embL, this, ← mul_assoc, ← Units.val_mul, inv_mul_cancel_left])

def colL (e : c ⊕ d ≃ a) (s : Set ℕ) (y : ColZero k b e s) (h : GL b k) : ColZero k b e s :=
  ⟨lAct s y.1 h, fun i j => by rw [lAct_val, mul_apply]; simp [y.2]⟩

omit [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
theorem continuous_colL (e : c ⊕ d ≃ a) (s : Set ℕ) :
    Continuous fun p : ColZero k b e s × GL b k => colL e s p.1 p.2 :=
  ((continuous_lAct s).comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq d] in
theorem colL_transitive (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) (y y' : ColZero k b e {κ}) :
    ∃ h, colL e _ y h = y' := by
  have inj : ∀ z : ColZero k b e {κ},
      Function.Injective (z.1.1.submatrix id fun i => e (.inl i)).mulVecLin := fun z =>
    (injective_iff_map_eq_zero _).2 (GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k b c d a e z.1.1 (z.1.2.trans hκ) z.2)
  obtain ⟨φ, hφ⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.ofInjective _ (inj y)).symm.trans (LinearEquiv.ofInjective _ (inj y')))
  have hφ' : ∀ v, φ ((y.1.1.submatrix id fun i => e (.inl i)) *ᵥ v) =
      (y'.1.1.submatrix id fun i => e (.inl i)) *ᵥ v := fun v => by
    have := hφ (LinearEquiv.ofInjective _ (inj y) v)
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at this
    exact this.symm
  let g : GL b k := ⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨g⁻¹, Subtype.ext (Subtype.ext ?_)⟩
  show (lAct _ y.1 g⁻¹).1 = _
  rw [lAct_val, inv_inv]
  ext i l
  obtain ⟨l | l, rfl⟩ := e.surjective l
  · have h1 := congrFun (hφ' (Pi.single l 1)) i
    rw [← LinearEquiv.coe_coe, ← LinearMap.toMatrix'_mulVec] at h1
    simpa [mul_apply, mulVec, dotProduct, g, Pi.single_apply] using h1
  · rw [y'.2, mul_apply]; simp [y.2]

def leftRep (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) :
    Representation ℂ (GL b k) (SB (ColZero k b e s)) :=
  twist (sbRep (colL e s) (fun y => Subtype.ext (lAct_one s y.1))
    (fun y g h => Subtype.ext (lAct_mul s y.1 g h))
    (continuous_slice (colL e s) (continuous_colL e s))) ψ

omit [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
theorem leftRep_apply (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (h : GL b k) (Φ : SB (ColZero k b e s))
    (y : ColZero k b e s) : (leftRep e s ψ h Φ).1 y = (ψ h : ℂ) * Φ.1 (colL e s y h) := rfl

def leftOp (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (h : GL b k) :
    (levRep k b e s).IntertwiningMap (levRep k b e s) where
  toLinearMap := leftRep e s ψ h
  isIntertwining' g := LinearMap.ext fun Φ => Subtype.ext (funext fun y => by
    have : pAct e s (colL e s y h) (embL e g) = colL e s (pAct e s y (embL e g)) h :=
      Subtype.ext (Subtype.ext (by
        show (rAct s (lAct s y.1 h) _).1 = (lAct s (rAct s y.1 _) h).1
        rw [rAct_val, lAct_val, lAct_val, rAct_val, Matrix.mul_assoc]))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, leftRep_apply, levRep_apply, levRep_apply, leftRep_apply, this,
      mul_left_comm])

theorem leftOp_apply (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (h : GL b k) (Φ : SB (ColZero k b e s))
    (y : ColZero k b e s) : (leftOp e s ψ h Φ).1 y = (ψ h : ℂ) * Φ.1 (colL e s y h) := rfl

def rel (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) : Submodule ℂ (SB (ColZero k b e s)) :=
  Submodule.span ℂ {y | ∃ h z, y = leftOp e s ψ h z - z}

theorem rel_le (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (g : Levi k (Two c d)) :
    rel e s ψ ≤ (rel e s ψ).comap (levRep k b e s g) := Submodule.span_le.2 (by
  rintro _ ⟨h, z, rfl⟩
  refine Submodule.subset_span ⟨h, levRep k b e s g z, ?_⟩
  rw [map_sub, (leftOp e s ψ h).isIntertwining])

def coinvRep (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) :
    Representation ℂ (Levi k (Two c d)) (SB (ColZero k b e s) ⧸ rel e s ψ) :=
  (levRep k b e s).quotient _ (rel_le e s ψ)

def coinvMk (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) :
    (levRep k b e s).IntertwiningMap (coinvRep e s ψ) where
  toLinearMap := (rel e s ψ).mkQ
  isIntertwining' _ := rfl

theorem coinvMk_surjective (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) :
    Function.Surjective (coinvMk e s ψ) := (rel e s ψ).mkQ_surjective

theorem mem_rel_of_coinvMk (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) (x : SB (ColZero k b e s))
    (hx : coinvMk e s ψ x = 0) : x ∈ Submodule.span ℂ {y | ∃ h z, y = leftOp e s ψ h z - z} :=
  (Submodule.Quotient.mk_eq_zero (rel e s ψ)).1 hx

theorem isSmooth_coinvRep (e : c ⊕ d ≃ a) (s : Set ℕ) (ψ : GL b k →* ℂˣ) : IsSmooth (coinvRep e s ψ) :=
  (IsSubquotient.of_surjective (coinvMk e s ψ) (rel e s ψ).mkQ_surjective).isSmooth (isSmooth_levRep e s)

theorem finiteDimensional_coinv (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) {ψ : GL b k →* ℂˣ}
    (hψ : IsSmoothChar ψ) : FiniteDimensional ℂ (SB (ColZero k b e {κ}) ⧸ rel e {κ} ψ) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : LocallyCompactSpace (Matrix b a k) := inferInstanceAs (LocallyCompactSpace (b → a → k))
  have hlc : IsLocallyClosed {x : Matrix b a k | x.rank ∈ ({κ} : Set ℕ)} := by
    refine ⟨_, _, isOpen_le_rank κ, isClosed_rank_lt (κ + 1), Set.ext fun x => ?_⟩
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
    omega
  have : LocallyCompactSpace (RankIn k a b {κ}) := hlc.locallyCompactSpace
  have : LocallyCompactSpace (ColZero k b e {κ}) := (isClosed_colZero e _).locallyCompactSpace
  obtain ⟨v, hv⟩ := exists_generator (r := colL e {κ}) (fun y => Subtype.ext (lAct_one _ y.1))
    (fun y g h => Subtype.ext (lAct_mul _ y.1 g h)) ψ (rel e {κ} ψ).mkQ
    (fun h Φ Φ' hΦ => (Submodule.Quotient.eq _).2 (Submodule.subset_span
      ⟨h, Φ, congrArg (· - Φ) (Subtype.ext (funext hΦ))⟩))
    (continuous_colL e _) (colL_transitive e hκ) (fun U hU => by
      obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k b U hU
      exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩) hψ
  have h2 : Submodule.span ℂ {v} = ⊤ := eq_top_iff.2 fun x _ => by
    obtain ⟨Φ, rfl⟩ := (rel e {κ} ψ).mkQ_surjective x
    exact hv Φ
  exact ⟨h2 ▸ Submodule.fg_span_singleton v⟩

theorem exists_indLower_coinv (e : c ⊕ d ≃ a) {V U Γ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U]
    [Module ℂ U] {σ : Representation ℂ (Levi k (Two c d)) V} {τ : Representation ℂ (Levi k (Two c d)) U}
    (hσ : IsSmooth σ) (A : σ.IntertwiningMap τ) (T : Γ → σ.IntertwiningMap σ) (hA : Function.Surjective A)
    (hT : ∀ x, A x = 0 → x ∈ Submodule.span ℂ {y : V | ∃ γ z, y = T γ z - z}) :
    ∃ q : IndSpLower (two e) σ →ₗ[ℂ] IndSpLower (two e) τ, Function.Surjective q ∧
      (∀ g f, q (parIndLower (two e) σ g f) = parIndLower (two e) τ g (q f)) ∧
      ∀ f, q f = 0 → f ∈ Submodule.span ℂ {w : IndSpLower (two e) σ | ∃ (γ : Γ) (z : IndSpLower (two e) σ),
        ∀ x, w.1.1 x = T γ (z.1.1 x) - z.1.1 x} := by
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := LeviInt.levi_integral_facts k _ a _ (opp (two e))
  obtain ⟨h1, h2⟩ := IndCoinv.smInd_coinvariants (GL a k) (parabLower k (two e)) (KO k a) hP
    SplitFlip.isCompact_KO hPK (exists_open_normalised_subgroup_subset k a) _ _ _ _
    (isSmooth_comp (isSmooth_twist hσ (isSmoothChar_deltaHalf k).inv) (leviProjLower k (two e)) hcont)
    (compMap (twistMap A (deltaHalf k _)⁻¹) (leviProjLower k (two e))) Γ
    (fun h => compMap (twistMap (T h) (deltaHalf k _)⁻¹) (leviProjLower k (two e))) hA hT
  refine ⟨(smIndMap (compMap (twistMap A (deltaHalf k _)⁻¹) (leviProjLower k (two e)))).toLinearMap, h1,
    fun _ _ => rfl, fun f hf => Submodule.span_mono ?_ (h2 f hf)⟩
  rintro _ ⟨γ, z, rfl⟩
  exact ⟨γ, z, fun _ => rfl⟩

theorem exists_coinvMap (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) {ψ : GL b k →* ℂˣ}
    (hψ : IsSmoothChar ψ) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (Levi k (Two c d)) W),
      IsSmooth τ ∧ HasFiniteLength τ ∧
    ∃ q : SB (RankIn k a b {κ}) →ₗ[ℂ] IndSpLower (two e) τ, Function.Surjective q ∧
      (∀ g (Φ Φ' : SB (RankIn k a b {κ})), (∀ x, Φ'.1 x = (rChar k a b g : ℂ) * Φ.1 (rAct _ x g)) →
        q Φ' = parIndLower (two e) τ g (q Φ)) ∧
      ∀ Φ, q Φ = 0 → Φ ∈ Submodule.span ℂ {w : SB (RankIn k a b {κ}) | ∃ (h : GL b k)
        (Ψ : SB (RankIn k a b {κ})), ∀ x, w.1 x = (ψ h : ℂ) * Ψ.1 (lAct _ x h) - Ψ.1 x} := by
  haveI := finiteDimensional_coinv e hκ hψ
  refine ⟨_, _, _, coinvRep e {κ} ψ, isSmooth_coinvRep _ _ _,
    FinitenessModel.hasFiniteLength_of_finiteDimensional _, ?_⟩
  refine (exists_indEquiv (k := k) (b := b) e hκ).elim fun E hE => ?_
  refine (exists_indLower_coinv e (isSmooth_levRep (k := k) (b := b) e {κ})
    (coinvMk e {κ} ψ) (leftOp e {κ} ψ) (coinvMk_surjective e {κ} ψ) (mem_rel_of_coinvMk e {κ} ψ)).elim
    fun q hh => ?_
  have h1 := hh.1
  have hq := hh.2.1
  have h2 := hh.2.2
  refine ⟨q ∘ₗ E.toLinearMap, h1.comp E.surjective, fun g Φ Φ' h => ?_, fun Φ hΦ => ?_⟩
  · have : E Φ' = parIndLower (two e) (levRep k b e {κ}) g (E Φ) :=
      Subtype.ext (Subtype.ext (funext fun x => Subtype.ext (funext fun y => by
        rw [parIndLower_apply, hE, hE, h, map_mul, rAct_mul, Units.val_mul, mul_assoc])))
    exact (congrArg q this).trans (hq _ _)
  · have h3 := h2 (E Φ) hΦ
    rw [← E.symm_apply_apply Φ]
    refine Submodule.mem_comap.1 (Submodule.span_le.2 ?_ h3 : E Φ ∈ Submodule.comap E.symm.toLinearMap _)
    rintro w ⟨h, z, hw⟩
    obtain ⟨Ψ, rfl⟩ := E.surjective z
    let Ψ' : SB (RankIn k a b {κ}) := twist (sbRep (lAct {κ}) (lAct_one _) (lAct_mul _)
      (continuous_slice (lAct {κ}) (continuous_lAct _))) ψ h Ψ
    have hΨ' : ∀ x, Ψ'.1 x = (ψ h : ℂ) * Ψ.1 (lAct _ x h) := fun _ => rfl
    clear_value Ψ'
    have : w = E (Ψ' - Ψ) :=
      Subtype.ext (Subtype.ext (funext fun x => Subtype.ext (funext fun y => by
        have h4 : rAct _ (colL e {κ} y h).1 x = lAct _ (rAct _ y.1 x) h := Subtype.ext (by
          show (rAct _ (lAct _ y.1 h) _).1 = _
          rw [rAct_val, lAct_val, lAct_val, rAct_val, Matrix.mul_assoc])
        rw [hw, Submodule.coe_sub, Pi.sub_apply, leftOp_apply, hE, hE, hE, Submodule.coe_sub, Pi.sub_apply,
          hΨ', h4]
        ring)))
    refine Submodule.subset_span ⟨h, Ψ, fun x => ?_⟩
    rw [this, LinearEquiv.coe_coe, E.symm_apply_apply, Submodule.coe_sub, Pi.sub_apply, hΨ']

end Strata

section Main

open GlobalTheory.RankStrataProof GlobalTheory.ThetaGLSub GlobalTheory.ThetaGLRank

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

variable (k n m) in

def res (ρ : ℕ) : rkSub k n m ρ →ₗ[ℂ] SB (RankIn k (Fin m) (Fin n) {ρ}) where
  toFun Φ := ⟨fun x => Φ.1 x.1, comp_mem_SB_of_isInducing IsInducing.subtypeVal ⟨Φ.1, Φ.2.1⟩
    (isClosed_rank_lt (ρ + 1)) (fun y => Nat.lt_succ_of_le (le_of_eq y.2)) fun x hx h0 =>
      ⟨⟨x, le_antisymm (Nat.le_of_lt_succ hx) (not_lt.1 fun h => h0 (Φ.2.2 x h))⟩, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem res_surjective (ρ : ℕ) : Function.Surjective (res k n m ρ) := by
  intro f
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin m) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin m → k))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin m) k) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin m → k))
  obtain ⟨G, hG, hG0⟩ := GlobalTheory.SBExtend.exists_extension (Matrix (Fin n) (Fin m) k) {x | ρ ≤ x.rank}
    {x | x.rank ∈ ({ρ} : Set ℕ)} (isOpen_le_rank ρ) (fun x hx => le_of_eq (Eq.symm hx)) f
  exact ⟨⟨G.1, G.2, fun x hx => hG0 x (not_le.2 hx)⟩, Subtype.ext (funext hG)⟩

theorem mem_of_res_eq_zero {ρ : ℕ} {Φ : rkSub k n m ρ} (h : res k n m ρ Φ = 0) : Φ.1 ∈ rkSub k n m (ρ + 1) := by
  refine ⟨Φ.2.1, fun x hx => ?_⟩
  by_cases h1 : x.rank < ρ
  · exact Φ.2.2 x h1
  · exact congrFun (congrArg Subtype.val h) ⟨x, le_antisymm (Nat.le_of_lt_succ hx) (not_lt.1 h1)⟩

theorem om_apply (g : GL (Fin m) k) (h : GL (Fin n) k) {Φ : Matrix (Fin n) (Fin m) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (Fin n) (Fin m) k)) (x : Matrix (Fin n) (Fin m) k) :
    om 1 g h Φ x = (omChar (Fin m) (Fin n) 1 (g, h) : ℂ) * Φ (act x (g, h)) := by
  have := congrFun (omega_eq_om 1 g h ⟨Φ, hΦ⟩) x
  rw [inv_one] at this
  exact this.symm

theorem layer_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} → ∀ (ρ t : ℕ) (h : ρ + t = m),
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (τ : Representation ℂ (GlobalTheory.SmGL.Levi k (GlobalTheory.SmGL.Two (Fin ρ) (Fin t))) W),
      GlobalTheory.PRep.IsSmooth τ ∧ GlobalTheory.SmGL.HasFiniteLength τ ∧
      ∃ f : GlobalTheory.SmGL.IndSpLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ →ₗ[ℂ] (Matrix (Fin n) (Fin m) k → ℂ),
        (∀ (g : GL (Fin m) k) (v : GlobalTheory.SmGL.IndSpLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ),
          f (GlobalTheory.SmGL.parIndLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ g v) -
              GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) k) (f v) ∈
            GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1)) ∧
        GlobalTheory.ThetaGLRank.rkSub k n m ρ ≤
          GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1) ⊔ LinearMap.range f := by
  intro k _ _ _ _ n m χ hχ ρ t h
  let ψ : GL (Fin n) k →* ℂˣ := (omChar (Fin m) (Fin n) 1).comp (MonoidHom.inr _ _) * χ⁻¹
  have hψ : IsSmoothChar ψ :=
    ((isSmoothChar_omChar isSmoothChar_one).comp _ (continuous_const.prodMk continuous_id)).mul
      (IsSmoothChar.inv hχ)
  have hρ : ρ = Fintype.card (Fin ρ) := (Fintype.card_fin ρ).symm
  obtain ⟨W, _, _, τ, hτ, hτ', q, hq, hqg, hq0⟩ := exists_coinvMap (stdSum h) hρ hψ
  refine ⟨W, _, _, τ, hτ, hτ', ?_⟩
  set C := aug m χ ⊔ rkSub k n m (ρ + 1)
  have hker : ∀ Φ : rkSub k n m ρ, q (res k n m ρ Φ) = 0 → Φ.1 ∈ C := by
    intro Φ hΦ
    have h1 : res k n m ρ Φ ∈ (C.comap (rkSub k n m ρ).subtype).map (res k n m ρ) := by
      refine Submodule.span_le.2 ?_ (hq0 _ hΦ)
      rintro w ⟨γ, Ψ, hw⟩
      obtain ⟨Ψ, rfl⟩ := res_surjective ρ Ψ
      have h2 : om 1 (1 : GL (Fin m) k) γ Ψ.1 ∈ rkSub k n m ρ :=
        ⟨Model.om_mem_SB 1 1 γ Ψ.2.1, fun x hx => by
          rw [om_apply _ _ Ψ.2.1, Ψ.2.2 _ (by rwa [rank_act]), mul_zero]⟩
      refine ⟨((χ γ)⁻¹ : ℂˣ).val • (⟨_, h2⟩ - (χ γ : ℂ) • Ψ), ?_, Subtype.ext (funext fun x => ?_)⟩
      · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, Ψ.1, Ψ.2.1, rfl⟩))
      · rw [hw]
        show ((χ γ)⁻¹ : ℂˣ).val * (om 1 (1 : GL (Fin m) k) γ Ψ.1 x.1 - (χ γ : ℂ) * Ψ.1 x.1) =
          ((omChar (Fin m) (Fin n) 1 (1, γ) * (χ γ)⁻¹ : ℂˣ) : ℂ) * Ψ.1 (act x.1 (1, γ)) - Ψ.1 x.1
        rw [om_apply _ _ Ψ.2.1, mul_sub, Units.inv_mul_cancel_left, Units.val_mul]
        ring
    obtain ⟨Ψ, hΨ, e⟩ := h1
    have h3 : (Φ - Ψ).1 ∈ rkSub k n m (ρ + 1) := mem_of_res_eq_zero (by rw [map_sub, e, sub_self])
    simpa using C.add_mem (Submodule.mem_sup_right h3) hΨ
  obtain ⟨S, hS⟩ := LinearMap.exists_rightInverse_of_surjective (q ∘ₗ res k n m ρ)
    (LinearMap.range_eq_top.2 (hq.comp (res_surjective ρ)))
  have hS' : ∀ v, q (res k n m ρ (S v)) = v := fun v => LinearMap.congr_fun hS v
  refine ⟨(rkSub k n m ρ).subtype ∘ₗ S, fun g v => ?_, fun Φ hΦ => ?_⟩
  · refine hker (S (parIndLower _ _ g v) - ⟨_, om_mem_rkSub ρ g (S v).2⟩) ?_
    rw [map_sub, map_sub, hS', hqg g (res k n m ρ (S v)) _ fun x => om_apply g 1 (S v).2.1 x.1, hS', sub_self]
  · have h1 := hker (⟨Φ, hΦ⟩ - S (q (res k n m ρ ⟨Φ, hΦ⟩))) (by rw [map_sub, map_sub, hS', sub_self])
    simpa using Submodule.add_mem_sup h1 (LinearMap.mem_range_self ((rkSub k n m ρ).subtype ∘ₗ S)
      (q (res k n m ρ ⟨Φ, hΦ⟩)))

end Main

end GlobalTheory.ThetaGLCover
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_length_levi_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} → ∀ (ρ t : ℕ) (h : ρ + t = m),
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (τ : Representation ℂ (GlobalTheory.SmGL.Levi k (GlobalTheory.SmGL.Two (Fin ρ) (Fin t))) W),
      GlobalTheory.PRep.IsSmooth τ ∧ GlobalTheory.SmGL.HasFiniteLength τ ∧
      ∃ f : GlobalTheory.SmGL.IndSpLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ →ₗ[ℂ] (Matrix (Fin n) (Fin m) k → ℂ),
        (∀ (g : GL (Fin m) k) (v : GlobalTheory.SmGL.IndSpLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ),
          f (GlobalTheory.SmGL.parIndLower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) τ g v) -
              GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) k) (f v) ∈
            GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1)) ∧
        GlobalTheory.ThetaGLRank.rkSub k n m ρ ≤
          GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1) ⊔ LinearMap.range f := by
  atlas_forward_decl GlobalTheory.ThetaGLCover.layer_cover
end

section
section
noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.ThetaGLSub GlobalTheory.ThetaGLRank GlobalTheory.SmGL

namespace GlobalTheory.ThetaGLLayer

theorem exists_chain_bound {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    ∃ L : ℕ, ∀ (r : ℕ) (s : Fin r → Submodule R M), StrictMono s → r ≤ L := by
  refine ⟨(Module.length R M).toNat + 1, fun r s hs => ?_⟩
  rcases r with _ | r
  · exact Nat.zero_le _
  let p : LTSeries (Submodule R M) := ⟨r, s, fun i => hs Fin.castSucc_lt_succ⟩
  have h1 : (r : ℕ∞) ≤ Module.length R M := by
    rw [Module.length_eq_height]
    exact (Order.length_le_height_last (p := p)).trans (Order.height_mono le_top)
  have h2 : Module.length R M ≠ ⊤ := Module.length_ne_top_iff.2 h
  have h3 : r ≤ (Module.length R M).toNat := by
    rw [← ENat.coe_le_coe, ENat.coe_toNat h2]; exact h1
  omega

theorem exists_subrep_chain_bound {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (h : HasFiniteLength π) :
    ∃ L : ℕ, ∀ (r : ℕ) (s : Fin r → Subrepresentation π), StrictMono s → r ≤ L := by
  obtain ⟨L, hL⟩ := exists_chain_bound h
  exact ⟨L, fun r s hs => hL r _ (Subrepresentation.subrepresentationSubmoduleOrderIso.strictMono.comp hs)⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

theorem layer_bound_of_cover (χ : GL (Fin n) k →* ℂˣ) (ρ : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin m) k) V) (hπ : HasFiniteLength π)
    (f : V →ₗ[ℂ] (Matrix (Fin n) (Fin m) k → ℂ))
    (hf : ∀ (g : GL (Fin m) k) (v : V),
      f (π g v) - om 1 g (1 : GL (Fin n) k) (f v) ∈ aug m χ ⊔ rkSub k n m (ρ + 1))
    (hs : rkSub k n m ρ ≤ aug m χ ⊔ rkSub k n m (ρ + 1) ⊔ LinearMap.range f) :
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, IsSub χ (N i) ∧
        aug m χ ⊔ rkSub k n m (ρ + 1) ≤ N i ∧ N i ≤ aug m χ ⊔ rkSub k n m ρ) → r ≤ L := by
  obtain ⟨L, hL⟩ := exists_subrep_chain_bound hπ
  refine ⟨L, fun r N hN hNi => ?_⟩
  set C1 := aug m χ ⊔ rkSub k n m (ρ + 1) with hC1

  have key : ∀ i, N i = C1 ⊔ ((N i).comap f).map f := by
    intro i
    have hle : N i ≤ C1 ⊔ LinearMap.range f := by
      refine (hNi i).2.2.trans (sup_le ?_ ?_)
      · exact (le_sup_left : aug m χ ≤ C1).trans (le_sup_left : C1 ≤ C1 ⊔ LinearMap.range f)
      · exact hs
    rw [Submodule.map_comap_eq, ← sup_inf_assoc_of_le _ (hNi i).2.1]
    exact (inf_eq_left.2 hle).symm.trans (inf_comm _ _)
  let S : Fin r → Subrepresentation π := fun i =>
    ⟨(N i).comap f, fun g v hv => by
      show f (π g v) ∈ N i
      have h1 := (hNi i).1.2.2 g (f v) hv
      have h2 : f (π g v) - om 1 g (1 : GL (Fin n) k) (f v) ∈ N i := (hNi i).2.1 (hf g v)
      simpa using Submodule.add_mem _ h2 h1⟩
  have hS : StrictMono S := by
    intro i j hij
    have hle : S i ≤ S j := fun v hv => (hN hij).le hv
    refine lt_of_le_of_ne hle fun he => (hN hij).ne ?_
    have he' : (N i).comap f = (N j).comap f := congrArg Subrepresentation.toSubmodule he
    rw [key i, key j, he']
  exact hL r S hS

end GlobalTheory.ThetaGLLayer

namespace GlobalTheory.ThetaGLLayer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

theorem rkSub_eq_bot_of_lt {ρ : ℕ} (h : m < ρ) : rkSub k n m ρ = ⊥ := by
  refine eq_bot_iff.2 fun Φ hΦ => ?_
  refine funext fun x => hΦ.2 x ?_
  have : x.rank ≤ m := by simpa using Matrix.rank_le_width x
  omega

theorem om_zero (g : GL (Fin m) k) :
    om (1 : kˣ →* ℂˣ) g (1 : GL (Fin n) k) (0 : Matrix (Fin n) (Fin m) k → ℂ) = 0 :=
  funext fun x => by simp [om]

end GlobalTheory.ThetaGLLayer

open GlobalTheory.ThetaGLLayer in

theorem GlobalTheory.ThetaGLLayer.layer_bound : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} → ∀ ρ : ℕ,
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i) ∧
        GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1) ≤ N i ∧
        N i ≤ GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m ρ) → r ≤ L := by
  intro hP k _ _ _ _ n m χ hχ ρ
  by_cases hρ : ρ ≤ m
  · have h : ρ + (m - ρ) = m := Nat.add_sub_cancel' hρ
    obtain ⟨W, _, _, τ, hτs, hτl, f, hf, hs⟩ := GlobalTheory.T.exists_finite_length_levi_quotient k n m χ hχ ρ (m - ρ) h
    have hπ := ((hP.bernsteinZelevinskyFiniteness k).2.2.1).lower (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) hτs hτl
    exact layer_bound_of_cover χ ρ _ hπ f hf hs
  · have hπ : GlobalTheory.SmGL.HasFiniteLength (GlobalTheory.SmGL.ofChar (1 : GL (Fin m) k →* ℂˣ)) :=
      GlobalTheory.SmGL.hasFiniteLength_of_isIrreducible (GlobalTheory.SmGL.isIrreducible_ofChar _)
    refine layer_bound_of_cover χ ρ _ hπ 0 (fun g v => ?_) ?_
    · simp [om_zero]
    · rw [rkSub_eq_bot_of_lt (by omega)]; exact bot_le
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_rank_submodule_chain_bounded : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} → ∀ ρ : ℕ,
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i) ∧
        GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1) ≤ N i ∧
        N i ≤ GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m ρ) → r ≤ L := by
  atlas_forward_decl GlobalTheory.ThetaGLLayer.layer_bound
end

section
section
noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.ThetaGLSub GlobalTheory.ThetaGLRank

namespace GlobalTheory.ThetaGLRank

theorem boundedChains_thetaGL : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} →
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i)) → r ≤ L := by
  intro P k _ _ _ _ n m χ hχ
  have key : ∀ d : ℕ, ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, IsSub χ (N i) ∧ N i ≤ aug m χ ⊔ rkSub k n m (n + 1 - d)) → r ≤ L := by
    intro d
    induction d with
    | zero =>
      refine ⟨1, fun r N hN hQ => ?_⟩
      by_contra h
      push_neg at h
      have e : ∀ i, N i = aug m χ := fun i =>
        le_antisymm (by simpa [rkSub_succ_n] using (hQ i).2) (hQ i).1.1
      have hlt : (⟨0, by omega⟩ : Fin r) < ⟨1, h⟩ := by simp [Fin.lt_def]
      exact (hN hlt).ne (by rw [e, e])
    | succ d ih =>
      obtain ⟨L1, h1⟩ := ih
      by_cases hd : d ≤ n
      · obtain ⟨L2, h2⟩ := GlobalTheory.T.theta_rank_submodule_chain_bounded P k n m χ hχ (n - d)
        have e1 : n + 1 - d = n - d + 1 := by omega
        have e2 : n + 1 - (d + 1) = n - d := by omega
        refine ⟨L1 + L2, GlobalTheory.T.chain_length_bound_of_sup_inf (aug m χ ⊔ rkSub k n m (n + 1 - d))
          (fun x => IsSub χ x ∧ x ≤ aug m χ ⊔ rkSub k n m (n + 1 - (d + 1)))
          (fun x => IsSub χ x ∧ x ≤ aug m χ ⊔ rkSub k n m (n + 1 - d))
          (fun x => IsSub χ x ∧ aug m χ ⊔ rkSub k n m (n - d + 1) ≤ x ∧ x ≤ aug m χ ⊔ rkSub k n m (n - d))
          L1 L2 ?_ ?_ h1 (fun r N hN hQ => h2 r N hN hQ)⟩
        · intro x hx
          exact ⟨GlobalTheory.ThetaGLRank.IsSub.inf hx.1 (isSub_aug_sup χ _), inf_le_right⟩
        · intro x hx
          refine ⟨GlobalTheory.ThetaGLSub.IsSub.sup hx.1 (isSub_aug_sup χ _), ?_, ?_⟩
          · rw [← e1]; exact le_sup_right
          · refine sup_le (e2 ▸ hx.2) ?_
            rw [e1]
            exact sup_le_sup_left (rkSub_succ_le _) _
      · refine ⟨L1, fun r N hN hQ => h1 r N hN fun i => ⟨(hQ i).1, ?_⟩⟩
        have : n + 1 - (d + 1) = n + 1 - d := by omega
        rw [← this]; exact (hQ i).2
  obtain ⟨L, hL⟩ := key (n + 1)
  refine ⟨L, fun r N hN hQ => hL r N hN fun i => ⟨hQ i, ?_⟩⟩
  rw [Nat.sub_self, rkSub_zero]
  exact le_sup_of_le_right (hQ i).2.1

end GlobalTheory.ThetaGLRank
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_submodule_chain_bounded : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} →
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i)) → r ≤ L := by
  atlas_forward_decl GlobalTheory.ThetaGLRank.boundedChains_thetaGL
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.ThetaGLSub
open scoped TensorProduct

namespace GlobalTheory.ThetaGLSub.SumProper

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

variable (k n m) in

def rhoS : Representation ℂ (GL (Fin m) k) (SB (Matrix (Fin n) (Fin m) k)) where
  toFun g :=
    { toFun := fun Φ => ⟨om 1 g (1 : GL (Fin n) k) Φ, Model.om_mem_SB 1 g 1 Φ.2⟩
      map_add' := fun Φ Ψ => Subtype.ext (by exact om_add 1 g 1 (Φ : Matrix (Fin n) (Fin m) k → ℂ) Ψ)
      map_smul' := fun c Φ => Subtype.ext (by exact om_smul 1 g 1 c (Φ : Matrix (Fin n) (Fin m) k → ℂ)) }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (Model.om_one 1 Φ.1)
  map_mul' a b := LinearMap.ext fun Φ => Subtype.ext (by
    have := Model.om_mul (1 : kˣ →* ℂˣ) a b (1 : GL (Fin n) k) 1 Φ.1
    rw [mul_one] at this
    exact this)

@[simp] theorem rhoS_apply (g : GL (Fin m) k) (Φ : SB (Matrix (Fin n) (Fin m) k)) :
    ((rhoS k n m g Φ : SB (Matrix (Fin n) (Fin m) k)) : Matrix (Fin n) (Fin m) k → ℂ) =
      om 1 g (1 : GL (Fin n) k) Φ := rfl

def res (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) : Submodule ℂ (SB (Matrix (Fin n) (Fin m) k)) :=
  M.comap (SB _).subtype

theorem mem_res {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} {Φ : SB (Matrix (Fin n) (Fin m) k)} :
    Φ ∈ res M ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M := Iff.rfl

def rhoQ (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ))
    (hM : ∀ g : GL (Fin m) k, ∀ Φ ∈ M, om 1 g (1 : GL (Fin n) k) Φ ∈ M) :
    Representation ℂ (GL (Fin m) k) (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) where
  toFun g := (res M).mapQ (res M) (rhoS k n m g) (fun Φ hΦ => hM g Φ hΦ)
  map_one' := by
    apply Submodule.linearMap_qext
    ext Φ
    simp
  map_mul' a b := by
    apply Submodule.linearMap_qext
    ext Φ
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, map_mul, Module.End.mul_apply]
    rfl

theorem rhoQ_mk (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ))
    (hM : ∀ g : GL (Fin m) k, ∀ Φ ∈ M, om 1 g (1 : GL (Fin n) k) Φ ∈ M) (g : GL (Fin m) k)
    (Φ : SB (Matrix (Fin n) (Fin m) k)) :
    rhoQ M hM g ((res M).mkQ Φ) = (res M).mkQ (rhoS k n m g Φ) := rfl

variable {χ : GL (Fin n) k →* ℂˣ}

theorem mk_om {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (hM : IsSub χ M) (g : GL (Fin m) k)
    (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin m) k))
    (hΦ : (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 g h Φ) :
    (res M).mkQ Φ' = (χ h : ℂ) • rhoQ M hM.2.2 g ((res M).mkQ Φ) := by
  rw [rhoQ_mk, ← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_res]
  have e1 : om 1 g h (Φ : Matrix (Fin n) (Fin m) k → ℂ) =
      om 1 (1 : GL (Fin m) k) h (om 1 g (1 : GL (Fin n) k) Φ) := by
    have := Model.om_mul (1 : kˣ →* ℂˣ) (1 : GL (Fin m) k) g h 1 (Φ : Matrix (Fin n) (Fin m) k → ℂ)
    rwa [one_mul, mul_one] at this
  have hmem : om 1 (1 : GL (Fin m) k) h (om 1 g (1 : GL (Fin n) k) Φ) -
      (χ h : ℂ) • om 1 g (1 : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ aug m χ :=
    Submodule.subset_span ⟨h, _, Model.om_mem_SB 1 g 1 Φ.2, rfl⟩
  have := hM.1 hmem
  simpa [hΦ, e1] using this

theorem isSmooth_rhoQ (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ))
    (hM : ∀ g : GL (Fin m) k, ∀ Φ ∈ M, om 1 g (1 : GL (Fin n) k) Φ ∈ M) : IsSmooth (rhoQ M hM) := by
  refine isSmooth_of_nhds fun v => ?_
  obtain ⟨Φ, rfl⟩ := Submodule.mkQ_surjective (res M) v
  have h1 : IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ) := by simp
  have hO := (om_isSmoothRepresentation k (Fin m) (Fin n) 1 h1).2.2.2.2 Φ.1 Φ.2
  have hU : IsOpen {g : GL (Fin m) k | om 1 g (1 : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) = Φ} :=
    hO.preimage (continuous_id.prodMk continuous_const)
  refine Filter.mem_of_superset (hU.mem_nhds (Model.om_one 1 _)) fun g hg => ?_
  show rhoQ M hM g ((res M).mkQ Φ) = (res M).mkQ Φ
  rw [rhoQ_mk]
  congr 1
  exact Subtype.ext hg

theorem isIrreducible_rhoQ {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (hM : IsSub χ M)
    (hne : M ≠ SB _) (hmax : ∀ Q, IsSub χ Q → M ≤ Q → Q = M ∨ Q = SB _) :
    (rhoQ M hM.2.2).IsIrreducible := by
  have key : ∀ U : Subrepresentation (rhoQ M hM.2.2),
      IsSub χ ((U.toSubmodule.comap (res M).mkQ).map (SB _).subtype) ∧
        M ≤ (U.toSubmodule.comap (res M).mkQ).map (SB _).subtype := by
    intro U
    have hin : ∀ Φ ∈ M, Φ ∈ (U.toSubmodule.comap (res M).mkQ).map (SB _).subtype := by
      intro Φ hΦ
      refine ⟨⟨Φ, hM.2.1 hΦ⟩, ?_, rfl⟩
      have h0 : (res M).mkQ ⟨Φ, hM.2.1 hΦ⟩ = 0 := (Submodule.Quotient.mk_eq_zero (res M)).2 hΦ
      change (res M).mkQ _ ∈ U.toSubmodule
      rw [h0]; exact U.toSubmodule.zero_mem
    refine ⟨⟨fun z hz => hin z (hM.1 hz), Submodule.map_subtype_le _ _, ?_⟩, hin⟩
    rintro g _ ⟨Ψ, hΨ, rfl⟩
    refine ⟨rhoS k n m g Ψ, ?_, rfl⟩
    change (res M).mkQ Ψ ∈ U.toSubmodule at hΨ
    change (res M).mkQ (rhoS k n m g Ψ) ∈ U.toSubmodule
    rw [← rhoQ_mk M hM.2.2]
    exact U.apply_mem_toSubmodule g hΨ
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hne ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · refine le_antisymm hM.2.1 fun Φ hΦ => ?_
    have h1 : (res M).mkQ ⟨Φ, hΦ⟩ ∈ (⊤ : Subrepresentation (rhoQ M hM.2.2)) := trivial
    rw [← h] at h1
    have h2 : (res M).mkQ ⟨Φ, hΦ⟩ = 0 := h1
    exact (Submodule.Quotient.mk_eq_zero (res M)).1 h2
  · obtain ⟨hQ, hMQ⟩ := key U
    rcases hmax _ hQ hMQ with h | h
    · left
      refine SetLike.ext fun v => ⟨fun hv => ?_, fun hv => ?_⟩
      · obtain ⟨Φ, rfl⟩ := Submodule.mkQ_surjective (res M) v
        have h3 : (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ (U.toSubmodule.comap (res M).mkQ).map (SB _).subtype :=
          ⟨Φ, hv, rfl⟩
        rw [h] at h3
        show (res M).mkQ Φ = 0
        exact (Submodule.Quotient.mk_eq_zero (res M)).2 h3
      · have h4 : v = 0 := hv
        rw [h4]
        exact U.toSubmodule.zero_mem
    · right
      refine SetLike.ext fun v => ⟨fun _ => trivial, fun _ => ?_⟩
      obtain ⟨Φ, rfl⟩ := Submodule.mkQ_surjective (res M) v
      have h3 : (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ (U.toSubmodule.comap (res M).mkQ).map (SB _).subtype := by
        rw [h]; exact Φ.2
      obtain ⟨Ψ, hΨ, hΨΦ⟩ := h3
      have : Ψ = Φ := Subtype.ext hΨΦ
      rw [← this]
      exact hΨ

def tmap (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) →ₗ[ℂ] V) : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] V ⊗[ℂ] ℂ :=
  (TensorProduct.mk ℂ V ℂ).flip 1 ∘ₗ e ∘ₗ (res M).mkQ

theorem tmap_apply (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) →ₗ[ℂ] V) (Φ : SB (Matrix (Fin n) (Fin m) k)) :
    tmap M e Φ = e ((res M).mkQ Φ) ⊗ₜ[ℂ] (1 : ℂ) := rfl

theorem tmap_eq_zero_iff (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) {V : Type} [AddCommGroup V]
    [Module ℂ V] (e : (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) →ₗ[ℂ] V) (he : Function.Injective e)
    (Φ : SB (Matrix (Fin n) (Fin m) k)) : tmap M e Φ = 0 ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M := by
  rw [tmap_apply]
  constructor
  · intro h
    have h1 := congrArg (TensorProduct.rid ℂ V) h
    rw [TensorProduct.rid_tmul, one_smul, map_zero] at h1
    have h2 : (res M).mkQ Φ = 0 := he (h1.trans (map_zero e).symm)
    exact (Submodule.Quotient.mk_eq_zero (res M)).1 h2
  · intro h
    have h2 : (res M).mkQ Φ = 0 := (Submodule.Quotient.mk_eq_zero (res M)).2 h
    rw [h2, map_zero, TensorProduct.zero_tmul]

theorem tmap_equivariant {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (hM : IsSub χ M) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL (Fin m) k) V)
    (e : (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) →ₗ[ℂ] V)
    (he : ∀ g x, e (rhoQ M hM.2.2 g x) = π' g (e x)) (g : GL (Fin m) k) (h : GL (Fin n) k)
    (Φ Φ' : SB (Matrix (Fin n) (Fin m) k)) (hΦ : (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 g h Φ) :
    tmap M e Φ' = TensorProduct.map (π' g) (ofChar χ h) (tmap M e Φ) := by
  rw [tmap_apply, tmap_apply, mk_om hM g h Φ Φ' hΦ, map_smul, he, TensorProduct.map_tmul, ofChar_apply,
    TensorProduct.smul_tmul, smul_eq_mul]

theorem exists_max {L : ℕ} (hL : ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, IsSub χ (N i)) → r ≤ L)
    {N : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (hN : IsSub χ N) (hne : N ≠ SB _) :
    ∃ M, IsSub χ M ∧ M ≠ SB _ ∧ N ≤ M ∧ ∀ Q, IsSub χ Q → M ≤ Q → Q = M ∨ Q = SB _ := by
  by_contra H
  push_neg at H
  let T := {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ) // IsSub χ M ∧ M ≠ SB _ ∧ N ≤ M}
  have hstep : ∀ M : T, ∃ Q : T, M.1 < Q.1 := by
    intro M
    obtain ⟨Q, hQ, hMQ, h1, h2⟩ := H M.1 M.2.1 M.2.2.1 M.2.2.2
    exact ⟨⟨Q, hQ, h2, M.2.2.2.trans hMQ⟩, lt_of_le_of_ne hMQ (Ne.symm h1)⟩
  choose step hstep using hstep
  let seq : ℕ → T := fun i => step^[i] ⟨N, hN, hne, le_rfl⟩
  have hmono : StrictMono fun i => (seq i).1 := strictMono_nat_of_lt_succ fun i => by
    simp only [seq, Function.iterate_succ_apply']
    exact hstep _
  have := hL (L + 1) (fun i => (seq i).1) (hmono.comp Fin.val_strictMono) (fun i => (seq i).2.1)
  omega

end GlobalTheory.ThetaGLSub.SumProper

namespace GlobalTheory.ThetaGLSub.SumProper

theorem main : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n m : ℕ), 1 ≤ n → 1 ≤ m →
    ∀ χ : GL (Fin n) k →* ℂˣ, IsOpen {g | χ g = 1} →
    ∀ N N' : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ), GlobalTheory.ThetaGLSub.IsSub χ N → GlobalTheory.ThetaGLSub.IsSub χ N' →
      N ≠ GlobalTheory.SplitWeil.SB _ → N' ≠ GlobalTheory.SplitWeil.SB _ → N ⊔ N' ≠ GlobalTheory.SplitWeil.SB _ := by
  intro hP hMin k _ _ _ _ n m hn hm χ hχ N N' hN hN' hne hne' hsup
  obtain ⟨L, hL⟩ := GlobalTheory.T.theta_submodule_chain_bounded hP k n m χ hχ
  obtain ⟨M, hM, hMne, hNM, hMmax⟩ := exists_max hL hN hne
  obtain ⟨M', hM', hM'ne, hNM', hM'max⟩ := exists_max hL hN' hne'
  have hout : ∀ {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)}, IsSub χ M → M ≠ SB _ →
      ∃ Φ : SB (Matrix (Fin n) (Fin m) k), (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∉ M := by
    intro M hM hMne
    by_contra H
    push_neg at H
    exact hMne (le_antisymm hM.2.1 fun φ hφ => H ⟨φ, hφ⟩)
  have hsm : IsSmooth (ofChar χ) := (isSmooth_ofChar_iff χ).2 hχ
  obtain ⟨Φ₀, hΦ₀⟩ := hout hM hMne
  obtain ⟨Φ₁, hΦ₁⟩ := hout hM' hM'ne
  have hx : (res M).mkQ Φ₀ ≠ 0 := fun h => hΦ₀ ((Submodule.Quotient.mk_eq_zero (res M)).1 h)
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
  have hyp : ∃ f : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] ℂ, f ≠ 0 ∧
      ∀ (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin m) k)),
        (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 (1 : GL (Fin m) k) h Φ → f Φ' = ofChar χ h (f Φ) := by
    refine ⟨ℓ ∘ₗ (res M).mkQ, fun h0 => hℓ (LinearMap.congr_fun h0 Φ₀), fun h Φ Φ' hΦ => ?_⟩
    simp only [LinearMap.comp_apply, ofChar_apply]
    rw [mk_om hM 1 h Φ Φ' hΦ, map_one, Module.End.one_apply, map_smul, smul_eq_mul]
  obtain ⟨V₀, _, _, π', -, -, -, hU, hprop⟩ := hMin k n m hn hm ℂ (ofChar χ) hsm (isIrreducible_ofChar χ) hyp
  have omq : ∀ {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (hM : IsSub χ M), M ≠ SB _ →
      OmQuot 1 (rhoQ M hM.2.2) (ofChar χ) := by
    intro M hM hMne
    obtain ⟨Φ, hΦ⟩ := hout hM hMne
    refine ⟨tmap M LinearMap.id, fun h0 => hΦ ((tmap_eq_zero_iff M LinearMap.id Function.injective_id Φ).1
      (LinearMap.congr_fun h0 Φ)), tmap_equivariant hM (rhoQ M hM.2.2) LinearMap.id (fun _ _ => rfl)⟩
  obtain ⟨e⟩ := hU _ (rhoQ M hM.2.2) (isSmooth_rhoQ M hM.2.2) (isIrreducible_rhoQ hM hMne hMmax) (omq hM hMne)
  obtain ⟨e'⟩ := hU _ (rhoQ M' hM'.2.2) (isSmooth_rhoQ M' hM'.2.2) (isIrreducible_rhoQ hM' hM'ne hM'max)
    (omq hM' hM'ne)
  let F := tmap M e.toIntertwiningMap.toLinearMap
  let F' := tmap M' e'.toIntertwiningMap.toLinearMap
  have hF0 : ∀ Φ, F Φ = 0 ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M :=
    tmap_eq_zero_iff M _ (fun a b h => e.toLinearEquiv.injective h)
  have hF0' : ∀ Φ, F' Φ = 0 ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M' :=
    tmap_eq_zero_iff M' _ (fun a b h => e'.toLinearEquiv.injective h)
  have hFe := tmap_equivariant hM π' e.toIntertwiningMap.toLinearMap
    (fun g x => LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x)
  have hFe' := tmap_equivariant hM' π' e'.toIntertwiningMap.toLinearMap
    (fun g x => LinearMap.congr_fun (e'.toIntertwiningMap.isIntertwining' g) x)
  have hFne : F ≠ 0 := fun h0 => hΦ₀ ((hF0 Φ₀).1 (LinearMap.congr_fun h0 Φ₀))
  obtain ⟨c, hc⟩ := hprop F F' (by rintro X (rfl | rfl); exacts [hFe, hFe']) hFne
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hΦ₁ ((hF0' Φ₁).1 (LinearMap.congr_fun hc Φ₁))
  have hker : ∀ Φ : SB (Matrix (Fin n) (Fin m) k),
      (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M' := by
    intro Φ
    rw [← hF0, ← hF0', hc, LinearMap.smul_apply, smul_eq_zero, or_iff_right hc0]
  have hMM' : M' ≤ M := fun φ hφ => (hker ⟨φ, hM'.2.1 hφ⟩).2 hφ
  apply hMne
  refine le_antisymm hM.2.1 ?_
  rw [← hsup]
  exact sup_le hNM (hNM'.trans hMM')

end GlobalTheory.ThetaGLSub.SumProper
end
end
