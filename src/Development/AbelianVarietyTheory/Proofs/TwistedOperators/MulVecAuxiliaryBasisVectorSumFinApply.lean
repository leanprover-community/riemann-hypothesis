import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqActStdLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeChainLatAndComap

section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem isLattice_stdLat_and_act : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι], Submodule.IsLattice k (stdLat k ι) ∧ ∀ (g : GL ι k) (L : Submodule 𝒪[k] (ι → k)), Submodule.IsLattice k L → Submodule.IsLattice k (act g L) := by
  intro k _ _ _ _ ι _ _
  refine ⟨⟨?_, ?_⟩, fun g L hL => ⟨?_, ?_⟩⟩
  · unfold stdLat
    refine Submodule.fg_pi fun _ => ?_
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i (1 : k) : ι → k) := by
      ext j
      simp [Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine mem_stdLat.2 fun j => ?_
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact hL.fg.map _
  · have himg : ((act g L : Submodule 𝒪[k] (ι → k)) : Set (ι → k))
        = (g : Matrix ι ι k).mulVecLin '' (L : Set (ι → k)) := by
      ext v
      exact mem_act
    rw [himg, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    intro w
    refine ⟨((g⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ w, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

end GlobalTheory.RootEx.UnfoldShape
end

section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.LatOpen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}

theorem eventually_smul_mem (L : Submodule 𝒪[k] (ι → k))
    (hL : Submodule.span k (L : Set (ι → k)) = ⊤) (x : ι → k) :
    ∀ᶠ t in nhds (0 : k), t • x ∈ L := by
  have hx : x ∈ Submodule.span k (L : Set (ι → k)) := by rw [hL]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have h : (𝒪[k] : Set k) ∈ nhds (0 : k) := (isOpen_int k).mem_nhds (zero_mem 𝒪[k])
    filter_upwards [h] with t ht
    exact L.smul_mem (⟨t, ht⟩ : 𝒪[k]) hy
  | zero => exact Filter.Eventually.of_forall fun t => by simp
  | add y z _ _ hy hz =>
    filter_upwards [hy, hz] with t h1 h2
    rw [smul_add]
    exact L.add_mem h1 h2
  | smul a y _ hy =>
    have ht : Filter.Tendsto (fun t : k => t * a) (nhds 0) (nhds 0) := by
      have h : Continuous (fun t : k => t * a) := continuous_id.mul continuous_const
      simpa using h.tendsto 0
    filter_upwards [ht.eventually hy] with t h
    rwa [smul_smul]

theorem isOpen_of_span_eq_top [Fintype ι] [DecidableEq ι] (L : Submodule 𝒪[k] (ι → k))
    (hL : Submodule.span k (L : Set (ι → k)) = ⊤) : IsOpen (L : Set (ι → k)) := by
  refine AddSubgroup.isOpen_of_mem_nhds L.toAddSubgroup (g := 0) ?_
  have h : ∀ᶠ x in nhds (0 : ι → k), ∀ i, x i • (Pi.single i (1 : k) : ι → k) ∈ L := by
    refine Filter.eventually_all.2 fun i => ?_
    have ht : Filter.Tendsto (fun x : ι → k => x i) (nhds 0) (nhds 0) :=
      (continuous_apply i).tendsto (0 : ι → k)
    exact ht.eventually (eventually_smul_mem L hL _)
  filter_upwards [h] with x hx
  have e : x = ∑ i, x i • (Pi.single i (1 : k) : ι → k) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  change x ∈ L
  rw [e]
  exact L.sum_mem fun i _ => hx i

theorem isCompact_stdLat : IsCompact (stdLat k ι : Set (ι → k)) := by
  have e : (stdLat k ι : Set (ι → k)) = Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    ext v
    simp only [SetLike.mem_coe, mem_stdLat, Set.mem_pi, Set.mem_univ, true_imp_iff]
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_int k

theorem isOpen_and_relIndex_ne_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (L : Submodule 𝒪[k] (ι → k)) (hL : Submodule.IsLattice k L) :
    IsOpen (L : Set (ι → k)) ∧ L.toAddSubgroup.relIndex (stdLat k ι).toAddSubgroup ≠ 0 := by
  have ho := isOpen_of_span_eq_top L hL.span_eq_top
  refine ⟨ho, ?_⟩
  haveI : CompactSpace (stdLat k ι).toAddSubgroup :=
    isCompact_iff_compactSpace.1 (isCompact_stdLat (k := k) (ι := ι))
  haveI : Finite ((stdLat k ι).toAddSubgroup ⧸
      L.toAddSubgroup.addSubgroupOf (stdLat k ι).toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen _ (ho.preimage continuous_subtype_val)
  exact AddSubgroup.index_ne_zero_of_finite

end GlobalTheory.RootEx.LatOpen
end

section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem exists_isReps_of_fg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (hϖ : Irreducible ϖ) (M : Submodule 𝒪[k] (ι → k)) (hM : M.FG) :
    ∃ T : Finset (ι → k), IsReps ϖ M T := by
  classical
  have h1 : Finite (𝒪[k] ⧸ Ideal.span {ϖ}) := by
    rw [← hϖ.maximalIdeal_eq]
    exact (inferInstance : Finite 𝓀[k])
  have hfin : Module.Finite 𝒪[k] M := Module.Finite.iff_fg.mpr hM
  set N : Submodule 𝒪[k] M := Ideal.span {ϖ} • ⊤ with hN
  have h2 : Finite (M ⧸ N) := by
    have : Finite (M ⧸ (⊤ : Submodule 𝒪[k] M)) := by
      have : Subsingleton (M ⧸ (⊤ : Submodule 𝒪[k] M)) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      infer_instance
    exact Submodule.finite_quotient_smul _ Module.Finite.fg_top
  have hmem : ∀ x : M, x ∈ N ↔ (x : ι → k) ∈ ϖ • M := by
    intro x
    rw [hN, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, h⟩
      exact ⟨⟨b, hb⟩, trivial, Subtype.ext h⟩
  have := Fintype.ofFinite (M ⧸ N)
  choose s hs using Submodule.Quotient.mk_surjective N
  refine ⟨Finset.univ.image fun q => (s q : ι → k), ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (s q).2
  · intro v hv
    have key : ∀ q, v - (s q : ι → k) ∈ ϖ • M ↔ Submodule.Quotient.mk (⟨v, hv⟩ : M) = q := by
      intro q
      conv_rhs => rw [← hs q, Submodule.Quotient.eq, hmem]
      rfl
    refine ⟨s (Submodule.Quotient.mk ⟨v, hv⟩), ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
      (key _).mpr rfl⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    rw [(key q).mp h]

end GlobalTheory.RootEx.UnfoldShape
end

section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem stabiliser_finite_cosets_mod (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (M : Submodule 𝒪[k] (ι → k)) (S : Finset (ι → k)) (hM : M.FG) (hS : IsReps ϖ M S) :
    ∃ T : Finset (GL ι k), (∀ t ∈ T, act t M = M) ∧ ∀ t : GL ι k, act t M = M →
      ∃ t₀ ∈ T, ∃ j : GL ι k, act j M = M ∧ MapsInto (j.val - 1) M (ϖ • M) ∧ t = t₀ * j := by
  classical
  obtain ⟨s, hs⟩ := hM
  have hmem : ∀ t : GL ι k, act t M = M → ∀ x ∈ M, t.val *ᵥ x ∈ M := fun t ht x hx => by
    have h : t.val *ᵥ x ∈ act t M := mem_act.2 ⟨x, hx, rfl⟩
    rwa [ht] at h
  have hsM : ∀ x : s, x.1 ∈ M := fun x => hs ▸ Submodule.subset_span x.2
  have hex : ∀ (t : {t : GL ι k // act t M = M}) (x : s), ∃ r : S, t.1.val *ᵥ x.1 - r.1 ∈ ϖ • M := by
    intro t x
    obtain ⟨r, hr, -⟩ := hS.2 _ (hmem t.1 t.2 x.1 (hsM x))
    exact ⟨⟨r, hr.1⟩, hr.2⟩
  choose f hf using hex
  have hsec : ∀ y : Set.range f, ∃ t, f t = y.1 := fun y => y.2
  choose g hg using hsec
  have : Fintype (Set.range f) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun y => (g y).1, ?_, fun t ht => ?_⟩
  · intro t ht
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ht
    exact (g y).2
  · set t₀ := g ⟨f ⟨t, ht⟩, ⟨_, rfl⟩⟩ with ht₀
    have hft : f t₀ = f ⟨t, ht⟩ := hg _
    have hinv : act (t₀.1)⁻¹ M = M := by
      have h := act_mul (t₀.1)⁻¹ t₀.1 M
      rw [inv_mul_cancel, act_one, t₀.2] at h
      exact h.symm
    refine ⟨t₀.1, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (t₀.1)⁻¹ * t, ?_, ?_, ?_⟩
    · rw [act_mul, ht, hinv]
    · intro v hv
      rw [← hs] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        have h1 := hf ⟨t, ht⟩ ⟨x, hx⟩
        have h2 := hf t₀ ⟨x, hx⟩
        rw [hft] at h2
        have h3 := sub_mem h1 h2
        rw [sub_sub_sub_cancel_right] at h3
        obtain ⟨w, hw, hw'⟩ := mem_smul_iff.1 h3
        refine mem_smul_iff.2 ⟨_, hmem _ hinv w hw, ?_⟩
        rw [← Matrix.mulVec_smul, hw', Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, Units.inv_mul, Units.val_mul]
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ a hx
    · rw [mul_inv_cancel_left]

end GlobalTheory.RootEx.UnfoldShape
end

section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

noncomputable section
namespace GlobalTheory.RootEx.UnfoldFlag

variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def flagMat (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  Matrix.of fun r s =>
    Sum.elim (fun s => (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inl s)) (fun i => y i r) s

theorem flagMat_mulVec (y : Fin c → (n ⊕ Fin c → k)) (v : n ⊕ Fin c → k) :
    flagMat y *ᵥ v = inX k n c (fun r => v (Sum.inl r)) + ∑ i, v (Sum.inr i) • y i := by
  funext r
  rw [inX_apply]
  simp only [mulVec, dotProduct, flagMat, of_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · rcases r with r | l
    · simp [one_apply]
    · simp [one_apply]
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem flagMat_uni {y : Fin c → (n ⊕ Fin c → k)} (hY : ∀ i, y i ∈ Yle k n c (i.val + 1))
    (h1 : ∀ i, y i (Sum.inr i) = 1) (h0 : ∀ i : Fin c, i.val = 0 → ∀ r, y i (Sum.inl r) = 0) :
    Radical.Uni (lev 1) (flagMat y) := by
  intro r s hrs
  rcases s with s | i
  · simp [flagMat]
  · simp only [flagMat, of_apply, Sum.elim_inr]
    rcases r with r | l
    · have hi : i.val = 0 := by
        simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
        omega
      rw [h0 i hi r, one_apply_ne (by simp)]
    · simp only [lev, Sum.elim_inr] at hrs
      rcases Nat.lt_or_eq_of_le hrs with h | h
      · rw [(mem_Yle.mp (hY i)) l h,
          one_apply_ne (fun e => by simp only [Sum.inr.injEq] at e; subst e; omega)]
      · have e : i = l := Fin.ext (by omega)
        subst e
        rw [h1, one_apply_eq]

theorem exists_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (hc : 1 ≤ c) (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), (∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) = Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)}) → (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ → ∃ u ∈ N k n c 1, act u Λ = chainLat ϖ c (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c hc ϖ hϖ Λ hΛ hfirst
  have hpow : ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) ≠ 0 := fun i => pow_ne_zero _ hϖ

  have hpick : ∀ i : Fin c, ∃ w : n ⊕ Fin c → k, w ∈ Λ ∧ w ∈ Yle k n c (i.val + 1) ∧
      w (Sum.inr i) = (ϖ : k) ^ (i.val + 1) ∧ (i.val = 0 → ∀ r, w (Sum.inl r) = 0) := by
    intro i
    by_cases hi : i.val = 0
    · have e : i = ⟨0, hc⟩ := Fin.ext hi
      subst e
      refine ⟨(ϖ : k) • aux k n (⟨0, hc⟩ : Fin c), hfirst, ?_, ?_, fun _ r => ?_⟩
      · rw [mem_Yle]
        intro l hl
        have hl0 : l ≠ ⟨0, hc⟩ := fun e => by subst e; simp at hl
        simp [aux, hl0]
      · simp [aux]
      · simp [aux]
    · have hmem : (ϖ : k) ^ (i.val + 1) ∈
          (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (R := 𝒪[k]) (Sum.inr i)) := by
        rw [hΛ i]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨w, hw, hwi⟩ := Submodule.mem_map.1 hmem
      exact ⟨w, (Submodule.mem_inf.1 hw).1, (Submodule.mem_inf.1 hw).2, hwi, fun h => absurd h hi⟩
  choose w hwΛ hwY hw1 hw0 using hpick

  obtain ⟨y, hy⟩ : ∃ y : Fin c → (n ⊕ Fin c → k), ∀ i, y i = ((ϖ : k) ^ (i.val + 1))⁻¹ • w i :=
    ⟨_, fun _ => rfl⟩
  have hyY : ∀ i, y i ∈ Yle k n c (i.val + 1) := by
    intro i
    rw [mem_Yle]
    intro l hl
    rw [hy, Pi.smul_apply, (mem_Yle.mp (hwY i)) l hl, smul_zero]
  have hy1 : ∀ i, y i (Sum.inr i) = 1 := by
    intro i
    rw [hy, Pi.smul_apply, hw1, smul_eq_mul, inv_mul_cancel₀ (hpow i)]
  have hy0 : ∀ i : Fin c, i.val = 0 → ∀ r, y i (Sum.inl r) = 0 := by
    intro i hi r
    rw [hy, Pi.smul_apply, hw0 i hi r, smul_zero]
  have hyw : ∀ i, (ϖ : k) ^ (i.val + 1) • y i = w i := by
    intro i
    rw [hy, smul_smul, mul_inv_cancel₀ (hpow i), one_smul]
  have hU := flagMat_uni hyY hy1 hy0
  have hdet : IsUnit (flagMat y).det := by
    rw [hU.det]
    exact isUnit_one
  obtain ⟨g, hg⟩ : ∃ g : GL (n ⊕ Fin c) k, g.val = flagMat y := ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩

  have himg : act g (chainLat ϖ c (Λ.comap (inX k n c))) = Λ := by
    apply le_antisymm
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := mem_act.1 hv
      obtain ⟨huL, hua⟩ := mem_chainLat.1 hu
      rw [hg, flagMat_mulVec]
      refine Λ.add_mem (Submodule.mem_comap.1 huL) (Λ.sum_mem fun i _ => ?_)
      obtain ⟨a, ha⟩ := hua i
      rw [ha, mul_smul, hyw i]
      exact Λ.smul_mem a (hwΛ i)
    · have hX : ∀ x ∈ Λ.comap (inX k n c),
          inX k n c x ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro x hx
        refine mem_act.2 ⟨inX k n c x, inX_mem_chainLat.2 hx, ?_⟩
        rw [hg, flagMat_mulVec]
        simp [inX_apply]
      have hW : ∀ i, w i ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro i
        refine mem_act.2 ⟨(ϖ : k) ^ (i.val + 1) • aux k n i, scaled_basis_mem_chainLattice ϖ _ i, ?_⟩
        rw [hg, mulVec_smul, ← hyw i]
        congr 1
        rw [aux, mulVec_single_one]
        rfl

      have key : ∀ j, j ≤ c → ∀ v ∈ Λ, v ∈ Yle k n c j →
          v ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro j
        induction j with
        | zero =>
          intro _ v hv hv0
          have e : v = inX k n c (fun r => v (Sum.inl r)) := by
            funext r
            rcases r with r | l
            · simp [inX_apply]
            · simp [inX_apply, (mem_Yle.mp hv0) l (by omega)]
          rw [e]
          apply hX
          rw [Submodule.mem_comap, ← e]
          exact hv
        | succ j ih =>
          intro hj v hv hvY
          obtain ⟨i, hi⟩ : ∃ i : Fin c, i.val = j := ⟨⟨j, by omega⟩, rfl⟩
          subst hi
          have hmem : v (Sum.inr i) ∈ Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)} := by
            rw [← hΛ i]
            exact Submodule.mem_map_of_mem (Submodule.mem_inf.2 ⟨hv, hvY⟩)
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
          have hrest : v - a • w i ∈ Yle k n c i.val := by
            rw [mem_Yle]
            intro l hl
            rcases eq_or_ne l i with rfl | hne
            · rw [Pi.sub_apply, Pi.smul_apply, hw1, ha, sub_self]
            · have hne' : l.val ≠ i.val := fun h => hne (Fin.ext h)
              have hl' : i.val + 1 < l.val + 1 := by omega
              rw [Pi.sub_apply, Pi.smul_apply, (mem_Yle.mp hvY) l hl', (mem_Yle.mp (hwY i)) l hl',
                smul_zero, sub_zero]
          have h1 := ih (by omega) (v - a • w i) (Λ.sub_mem hv (Λ.smul_mem a (hwΛ i))) hrest
          have h2 := Submodule.add_mem _ h1 (Submodule.smul_mem _ a (hW i))
          rwa [sub_add_cancel] at h2
      intro v hv
      exact key c le_rfl v hv (mem_Yle.2 fun l hl => absurd hl (by have := l.isLt; omega))
  refine ⟨g⁻¹, (Radical.mem_N_iff g⁻¹).2 ?_, ?_⟩
  · exact Radical.Uni.inv (g := g) (by rw [hg]; exact hU)
  · conv_lhs => rw [← himg]
    rw [← act_mul, inv_mul_cancel, act_one]

end GlobalTheory.RootEx.UnfoldFlag
end
end

section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem integral_periodic_eq_measure_mul_sum_cosets :
    ∀ (V : Type) [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (H : AddSubgroup V), MeasurableSet (H : Set V) → μ H ≠ ⊤ → ∀ (F : V → ℂ) (ι : Type) (T : Finset ι) (t : ι → V), (∀ x, ∀ h ∈ H, F (x + h) = F x) → (∀ x, F x ≠ 0 → ∃ w ∈ T, x - t w ∈ H) → (∀ w ∈ T, ∀ w' ∈ T, t w - t w' ∈ H → w = w') → ∫ x, F x ∂μ = (μ.real H : ℂ) * ∑ w ∈ T, F (t w) := by
  intro V _ _ _ μ _ H hH hμ F ι T t hper hsupp hinj
  set S : ι → Set V := fun w => (fun x => -t w + x) ⁻¹' (H : Set V) with hS
  have hmem : ∀ w x, x ∈ S w ↔ x - t w ∈ H := by
    intro w x
    simp only [hS, Set.mem_preimage, SetLike.mem_coe]
    rw [neg_add_eq_sub]
  have hSm : ∀ w, MeasurableSet (S w) := fun w => (measurable_const_add (-t w)) hH
  have hSμ : ∀ w, μ (S w) = μ H := fun w => measure_preimage_add μ (-t w) _
  have hval : ∀ w x, x - t w ∈ H → F x = F (t w) := by
    intro w x hx
    have := hper (t w) _ hx
    rwa [add_sub_cancel] at this
  have hF : F = fun x => ∑ w ∈ T, (S w).indicator (fun _ => F (t w)) x := by
    funext x
    by_cases hx : ∃ w ∈ T, x - t w ∈ H
    · obtain ⟨w, hw, hxw⟩ := hx
      rw [Finset.sum_eq_single w]
      · rw [Set.indicator_of_mem ((hmem w x).2 hxw)]
        exact hval w x hxw
      · intro w' hw' hne
        apply Set.indicator_of_notMem
        intro h
        apply hne
        apply hinj w' hw' w hw
        have := H.sub_mem hxw ((hmem w' x).1 h)
        rwa [sub_sub_sub_cancel_left] at this
      · intro h; exact absurd hw h
    · have h0 : F x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      rw [h0]
      symm
      apply Finset.sum_eq_zero
      intro w hw
      apply Set.indicator_of_notMem
      intro h
      exact hx ⟨w, hw, (hmem w x).1 h⟩
  have h1 : ∫ x, F x ∂μ = ∫ x, ∑ w ∈ T, (S w).indicator (fun _ => F (t w)) x ∂μ := by
    conv_lhs => rw [hF]
  rw [h1, integral_finset_sum, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro w _
    rw [integral_indicator_const _ (hSm w), Measure.real, hSμ w, Complex.real_smul]
    rfl
  · intro w _
    rw [integrable_indicator_iff (hSm w)]
    exact integrableOn_const (by rw [hSμ w]; exact hμ)

end GlobalTheory.RootEx.UnfoldShape
end

section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

def boxExp {n n' : Type} {c : ℕ} : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → ℕ
  | (_, Sum.inl _) => 0
  | (Sum.inl _, Sum.inr j) => j.val
  | (Sum.inr l, Sum.inr j) => j.val - (l.val + 1)

theorem boxExp_eq_zero {n n' : Type} {c : ℕ} (rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))
    (h : ¬ Free 1 rs) : boxExp rs = 0 := by
  rcases rs with ⟨r | l, s | j⟩ <;> simp only [Free, boxExp] at h ⊢ <;> omega

theorem sum_fin_sub (c j : ℕ) (hj : j ≤ c) :
    ∑ l : Fin c, (j - (l.val + 1)) = j * (j - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun l => j - (l + 1)) c]
  have h1 : ∑ l ∈ Finset.range c, (j - (l + 1)) = ∑ l ∈ Finset.range j, (j - (l + 1)) := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 hj) ?_
    intro x _ hx
    simp only [Finset.mem_range] at hx
    omega
  rw [h1, ← Finset.sum_range_id, ← Finset.sum_range_reflect (fun i => i) j]
  refine Finset.sum_congr rfl fun x _ => by omega

theorem sum_boxExp (n n' : Type) [Fintype n] [Fintype n'] (c : ℕ) :
    ∑ rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)), boxExp rs = expo c (Fintype.card n) := by
  rw [Fintype.sum_prod_type_right, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, boxExp, Finset.sum_const_zero, zero_add,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h : ∀ j : Fin (c + 1), Fintype.card n * j.val + ∑ l : Fin c, (j.val - (l.val + 1))
      = j.val * Fintype.card n + j.val * (j.val - 1) / 2 := by
    intro j
    rw [sum_fin_sub c j (by omega), mul_comm]
  rw [Finset.sum_congr rfl fun j _ => h j,
    Fin.sum_univ_eq_sum_range (fun j => j * Fintype.card n + j * (j - 1) / 2) (c + 1), expo]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_range] at hx hx'
    obtain rfl : x = 0 := by omega
    simp

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem measure_pow_mul_mem [MeasurableSpace k] [BorelSpace k] {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ)
    (ν : Measure k) (hν : IsUnitVol ν) (m : ℕ) :
    ν {x | (ϖ : k) ^ m * x ∈ 𝒪[k]} = (resCard k : ENNReal) ^ m := by
  have := hν.1
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  set u : kˣ := Units.mk0 (ϖ : k) h0 with hu
  have hset : {x | (ϖ : k) ^ m * x ∈ 𝒪[k]} = cball (u⁻¹ ^ m) := by
    ext x
    have hv : 0 < valuation k (ϖ : k) ^ m := pow_pos ((Valuation.pos_iff _).2 h0) m
    simp only [Set.mem_ofPred_eq, cball, Valuation.mem_integer_iff, map_mul, map_pow, hu,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, inv_pow]
    rw [← one_div, le_div_iff₀ hv, mul_comm]
  have h1 : distribHaarChar k u⁻¹ = (resCard k : NNReal) := by
    have := nabs_uniformiser hϖ (x := u) rfl
    rw [map_inv]
    apply NNReal.coe_injective
    rw [NNReal.coe_inv]
    simp only [nabs] at this
    rw [this]
    simp
  rw [hset, measure_cball, hν.2, mul_one, map_pow, h1]
  simp

theorem perLat_stdLat_eq {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} {ϖ : 𝒪[k]} (h0 : (ϖ : k) ≠ 0) :
    ((perLat ϖ n' c (stdLat k n) : AddSubgroup _) :
      Set ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k)) =
      Set.univ.pi fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} =>
        {x | (ϖ : k) ^ boxExp rs.1 * x ∈ 𝒪[k]} := by
  have key : ∀ (i l : ℕ) (x : k), l ≤ i →
      ((∃ a : 𝒪[k], (ϖ : k) ^ (i + 1) * x = a * (ϖ : k) ^ (l + 1)) ↔
        (ϖ : k) ^ (i + 1 - (l + 1)) * x ∈ 𝒪[k]) := by
    intro i l x hl
    have hp : (ϖ : k) ^ (i + 1) = (ϖ : k) ^ (i + 1 - (l + 1)) * (ϖ : k) ^ (l + 1) := by
      rw [← pow_add]; congr 1; omega
    constructor
    · rintro ⟨a, ha⟩
      have : (ϖ : k) ^ (i + 1 - (l + 1)) * x = a := by
        apply mul_right_cancel₀ (pow_ne_zero (l + 1) h0)
        rw [← ha, hp]; ring
      rw [this]; exact a.2
    · intro h
      exact ⟨⟨_, h⟩, by rw [hp]; ring⟩
  ext e
  simp only [SetLike.mem_coe, mem_perLat, mem_chainLat, mem_stdLat, Set.mem_pi, Set.mem_univ,
    Set.mem_ofPred_eq, forall_true_left, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro h ⟨⟨r, s | j⟩, hf⟩
    · rcases r with r | l <;> simp [Free] at hf
    · have hj : j ≠ 0 := by
        rintro rfl
        rcases r with r | l <;> simp [Free] at hf
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hj
      rcases r with r | l
      · have := (h i).1 r
        simp only [UnfoldShape.col, dif_pos hf] at this
        exact this
      · have := (h i).2 l
        simp only [UnfoldShape.col, dif_pos hf] at this
        have hl : l.val ≤ i.val := by
          simp only [Free, Fin.val_succ] at hf; omega
        exact (key _ _ _ hl).1 this
  · intro h i
    refine ⟨fun r => ?_, fun l => ?_⟩
    · have hf : Free 1 ((Sum.inl r, Sum.inr i.succ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) := by
        simp [Free]
      simp only [UnfoldShape.col, dif_pos hf]
      exact h ⟨_, hf⟩
    · by_cases hf : Free 1 ((Sum.inr l, Sum.inr i.succ) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))
      · simp only [UnfoldShape.col, dif_pos hf]
        have hl : l.val ≤ i.val := by
          simp only [Free, Fin.val_succ] at hf; omega
        exact (key _ _ _ hl).2 (h ⟨_, hf⟩)
      · simp only [UnfoldShape.col, dif_neg hf]
        exact ⟨0, by simp⟩

end

theorem volFree_perLat_stdLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n]
    [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (c : ℕ) (ϖ : 𝒪[k])
    (hϖ : Irreducible ϖ) (ν : Measure k) (hν : IsUnitVol ν) :
    volFree ν n n' c (perLat ϖ n' c (stdLat k n))
      = (resCard k : ENNReal) ^ expo c (Fintype.card n) := by
  classical
  have := hν.1
  have := secondCountable k
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  rw [perLat_stdLat_eq h0, volFree, Measure.pi_pi]
  simp only [measure_pow_mul_mem hϖ ν hν]
  rw [Finset.prod_pow_eq_pow_sum, ← sum_boxExp n n' c]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter fun rs => Free 1 rs) (by simp) boxExp]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => boxExp_eq_zero x ?_
  simpa using hx

end GlobalTheory.RootEx.UnfoldShape
end

section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.PerIndex

variable {k : Type} [Field k] [ValuativeRel k] {n : Type}

theorem col_add (n' : Type) {c : ℕ}
    (e f : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) :
    UnfoldShape.col (n' := n') (e + f) i
      = UnfoldShape.col (n' := n') e i + UnfoldShape.col (n' := n') f i := by
  funext r
  simp only [UnfoldShape.col, Pi.add_apply]
  split_ifs <;> simp

theorem relIndex_perLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type)
    [Fintype n'] [DecidableEq n'] (c : ℕ) (ϖ : 𝒪[k]) (hϖ : (ϖ : k) ≠ 0)
    (L : Submodule 𝒪[k] (n → k)) :
    (perLat ϖ n' c L).relIndex (perLat ϖ n' c (stdLat k n))
      = (L.toAddSubgroup.relIndex (stdLat k n).toAddSubgroup) ^ c := by
  classical
  let φ : perLat ϖ n' c (stdLat k n) →+ (Fin c → (stdLat k n).toAddSubgroup) :=
    AddMonoidHom.mk' (fun e i => ⟨fun r => ((ϖ : k) ^ ((i : ℕ) + 1) •
      UnfoldShape.col (n' := n') e.1 i) (Sum.inl r), (mem_chainLat.1 (mem_perLat.1 e.2 i)).1⟩)
      (by
        intro e f
        funext i
        apply Subtype.ext
        funext r
        simp only [AddSubgroup.coe_add, Pi.add_apply, col_add, smul_add])
  have hφ : Function.Surjective φ := by
    intro v
    have hY : ∀ i : Fin c, ((ϖ : k) ^ ((i : ℕ) + 1))⁻¹ • inX k n c (v i).1
        ∈ Yle k n c ((i : ℕ) + 1) := by
      intro i
      rw [mem_Yle]
      intro l _
      simp [inX_apply]
    have hc := col_uncol (n' := n') hY
    have hs : ∀ i : Fin c, (ϖ : k) ^ ((i : ℕ) + 1) • UnfoldShape.col (n' := n')
        (uncol n' fun i : Fin c => ((ϖ : k) ^ ((i : ℕ) + 1))⁻¹ • inX k n c (v i).1) i
        = inX k n c (v i).1 := by
      intro i
      rw [hc, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hϖ), one_smul]
    refine ⟨⟨uncol n' fun i : Fin c => ((ϖ : k) ^ ((i : ℕ) + 1))⁻¹ • inX k n c (v i).1, ?_⟩, ?_⟩
    · rw [mem_perLat]
      intro i
      rw [hs, mem_chainLat]
      refine ⟨?_, fun l => ⟨0, ?_⟩⟩
      · simpa [inX_apply] using (v i).2
      · simp [inX_apply]
    · funext i
      apply Subtype.ext
      funext r
      exact congrFun (hs i) (Sum.inl r)
  have hcomap : (perLat ϖ n' c L).addSubgroupOf (perLat ϖ n' c (stdLat k n))
      = (AddSubgroup.pi Set.univ fun _ : Fin c =>
          L.toAddSubgroup.addSubgroupOf (stdLat k n).toAddSubgroup).comap φ := by
    ext e
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_pi, mem_perLat]
    constructor
    · intro h i _
      exact (mem_chainLat.1 (h i)).1
    · intro h i
      exact mem_chainLat.2 ⟨h i trivial, (mem_chainLat.1 (mem_perLat.1 e.2 i)).2⟩
  rw [AddSubgroup.relIndex, hcomap, AddSubgroup.index_comap_of_surjective _ hφ,
    AddSubgroup.index_pi]
  simp [AddSubgroup.relIndex]

end GlobalTheory.RootEx.PerIndex
end

section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms

@[to_additive relIndex_mul_addVol
]
theorem relIndex_mul_mulVol {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact L.mul_mem a.val.2 (hHL hh)
    · intro hx
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨x, hx⟩
      refine ⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩
      have := congrArg Subtype.val hbh
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩
    apply hab
    have hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh1
    have hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh2
    have e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩ := Subtype.ext he.symm
    have := (hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ ((a.val : L) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, (a.val : L) • (H : Set G)) :=
        (measure_iUnion hdisj fun a => hH.const_smul _).symm
    _ = μ L := by rw [hU]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

set_option linter.unusedSectionVars false

theorem coe_ne_zero {ϖ : 𝒪[k]} (h : Irreducible ϖ) : (ϖ : k) ≠ 0 := fun h0 => h.ne_zero (Subtype.ext h0)

theorem psi_int {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {s : k} (hs : s ∈ 𝒪[k]) : ψ s = 1 :=
  hψ.eq_one (by simpa [cball, Valuation.mem_integer_iff] using hs)

theorem mem_int_of_psi {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {s : k}
    (hs : ∀ a : 𝒪[k], ψ (-(a * s)) = 1) : s ∈ 𝒪[k] := by
  rcases eq_or_ne s 0 with rfl | h0
  · exact zero_mem _
  have := (hψ s).1 fun y hy => by
    have ha : -(y / s) ∈ 𝒪[k] := by
      refine neg_mem ?_
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hy zero_le
    have := hs ⟨_, ha⟩
    simpa [h0] using this
  simpa [Valuation.mem_integer_iff] using this

theorem smul_mem_Yle {i : ℕ} (a : k) {v : n ⊕ Fin c → k} (hv : v ∈ Yle k n c i) : a • v ∈ Yle k n c i :=
  fun l hl => by simp [hv l hl]

theorem smul_inX (a : k) (v : n → k) : a • inX k n c v = inX k n c (a • v) := by
  ext (r | r) <;> simp [inX_apply]

theorem colMat_eq_zero {y : Fin c → (n ⊕ Fin c → k)} (hy : ∀ i, y i ∈ Yle k n c (i.val + 1))
    (l : Fin c) (j : Fin (c + 1)) (h : j.val ≤ l.val) : colMat n' y (Sum.inr l) (Sum.inr j) = 0 := by
  revert h
  refine Fin.cases (fun _ => ?_) (fun i h => ?_) j
  · simp [colMat]
  · simp only [Fin.val_succ] at h
    simpa [colMat] using hy i l (by omega)

theorem mulVec_auxiliaryBasisVectorSumFin_apply (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (j : Fin (c + 1)) (r) :
    (x *ᵥ aux k n' j) r = x r (Sum.inr j) := by
  simp [aux]

theorem act_embX (ϖ : 𝒪[k]) (g : GL n k) (L : Submodule 𝒪[k] (n → k)) :
    act (embX c g) (chainLat ϖ c L) = chainLat ϖ c (act g L) := by
  ext v
  rw [mem_act_iff_inv, ← map_inv, Radical.embX_val, fromBlocks_mulVec, mem_chainLat, mem_chainLat,
    mem_act_iff_inv]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mulVec, add_zero, zero_add, one_mulVec, Function.comp]
  rfl

variable [MeasurableSpace k] [BorelSpace k]

theorem oneClass (hc : 1 ≤ c) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) (L' : Submodule 𝒪[k] (n' → k)) : OneClass ϖ ψ ν n hc L' := by
  intro Λ hΛ Ψ _ hS hP hE
  have := hν.1
  have h0 := coe_ne_zero hϖ
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE ψ ν 1 Ψ x₀ ≠ 0 := Function.ne_iff.1 hE
  obtain ⟨y, hy, hΨ⟩ := exists_pt_ne_zero hx₀
  have hmap := hS _ hΨ
  have h1 : ∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) =
      Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)} := by
    intro i
    apply le_antisymm
    · have key : ∀ v ∈ Λ ⊓ Yle k n c (i.val + 1), ψ (-(v (Sum.inr i) / (ϖ : k) ^ (i.val + 1))) = 1 := by
        intro v hv
        let z : Fin c → (n ⊕ Fin c → k) := Pi.single i (((ϖ : k) ^ (i.val + 2))⁻¹ • v)
        have hz : ∀ j, (ϖ : k) ^ (j.val + 2) • z j ∈ Λ := by
          intro j
          rcases eq_or_ne j i with rfl | hj
          · simp only [z, Pi.single_eq_same]
            rw [smul_inv_smul₀ (pow_ne_zero _ h0)]
            exact hv.1
          · simp [z, hj]
        have hz' : ∀ j, ((ϖ : k) • z) j ∈ Yle k n c (j.val + 1) := by
          intro j
          rcases eq_or_ne j i with rfl | hj
          · simp only [z, Pi.smul_apply, Pi.single_eq_same]
            exact smul_mem_Yle _ (smul_mem_Yle _ hv.2)
          · simp [z, hj]
        have := opE_translate ψ ν hz' (fun x => by
          rw [colMat_smul]; exact hP x _ (mapsInto_colMat hz)) x₀
        have h2 : (ψ (-∑ j, ((ϖ : k) • z) j (Sum.inr j)) : ℂ) = 1 :=
          mul_right_cancel₀ hx₀ (by rw [one_mul]; exact this.symm)
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [z, hj]) (by simp)] at h2
        rw [← Circle.coe_eq_one, ← h2]
        congr 3
        simp only [z, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
        field_simp
        ring
      rintro _ ⟨v, hv, rfl⟩
      have := mem_int_of_psi hψ (s := v (Sum.inr i) / (ϖ : k) ^ (i.val + 1)) fun a => by
        have := key _ (Submodule.smul_mem _ a hv)
        rw [← this]
        congr 2
        simp [Subring.smul_def, mul_div_assoc]
      refine Submodule.mem_span_singleton.2 ⟨⟨_, this⟩, ?_⟩
      simp [Subring.smul_def, h0]
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨_, ⟨hmap _ (scaled_basis_mem_chainLattice ϖ L' i.castSucc), fun l hl => ?_⟩, ?_⟩
      · rw [Matrix.mulVec_smul, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply, pt_eq, Matrix.add_apply,
          colMat_eq_zero hy _ _ (by simp; omega)]
        have : l.val ≠ i.val := by omega
        simp [basePt, this]
      · rw [LinearMap.proj_apply, Matrix.mulVec_smul, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply, pt_eq, Matrix.add_apply,
          colMat_eq_zero hy _ _ (by simp)]
        simp [basePt]
  have h2 : (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ := by
    have := hmap _ (scaled_basis_mem_chainLattice ϖ L' 0)
    convert this using 1
    ext r
    rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply]
    rcases r with r | r
    · simp [pt_eq, basePt, colMat, aux]
    · simp only [pt_eq, basePt, colMat, aux, Pi.single_apply, Fin.ext_iff]
      by_cases hr : r.val = 0 <;> simp [hr, Fin.ext_iff]
  obtain ⟨u, hu, huΛ⟩ := GlobalTheory.RootEx.UnfoldFlag.exists_unipotent k n c hc ϖ h0 Λ h1 h2
  refine ⟨h1, h2, ⟨u, hu, huΛ⟩, ?_⟩
  obtain ⟨g, hg⟩ := GlobalTheory.RootEx.UnfoldShape.exists_eq_act_stdLat k n _ ((GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap k n c).2 Λ hΛ)
  refine ⟨u⁻¹ * embX c g, mul_mem (inv_mem (Subgroup.mem_sup_right hu)) (Subgroup.mem_sup_left ⟨g, rfl⟩), ?_⟩
  rw [act_mul, act_embX, ← hg, ← huΛ, ← act_mul, inv_mul_cancel, act_one]

theorem oneCoset (hc : 1 ≤ c) {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) (L' : Submodule 𝒪[k] (n' → k)) : OneCoset ϖ ψ ν n c L' := by
  have h0 := coe_ne_zero hϖ
  have hlat : Submodule.IsLattice k (chainLat ϖ c (stdLat k n)) :=
    (GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap k n c).1 ϖ h0 _ (GlobalTheory.RootEx.UnfoldShape.isLattice_stdLat_and_act k n).1
  constructor
  · intro μ Φ hΦ hS hP h' h hh' hE
    have key := oneClass hc hϖ hψ hν L' _ ((GlobalTheory.RootEx.UnfoldShape.isLattice_stdLat_and_act k _).2 h _ hlat) _
      (om_mem_SB μ h' h hΦ) ?_ ?_ hE
    · obtain ⟨r, hr, e⟩ := key.2.2.2
      refine ⟨r, hr, r⁻¹ * h, ?_, by group⟩
      rw [act_mul, e, ← act_mul, inv_mul_cancel, act_one]
    · intro x hx v hv
      rw [← hh'] at hv
      obtain ⟨w, hw, rfl⟩ := mem_act.1 hv
      have := hS _ (right_ne_zero_of_mul hx) w hw
      rw [mem_act_iff_inv]
      simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using this
    · intro x y hy
      have : MapsInto ((h⁻¹).val * y * h'.val) (chainLat ϖ (c + 1) L') (chainLat ϖ c (stdLat k n)) := by
        intro w hw
        have h1 : h'.val *ᵥ w ∈ chainLat ϖ (c + 1) L' := by
          rw [← hh']; exact mem_act.2 ⟨w, hw, rfl⟩
        have := mem_act_iff_inv.1 (hy _ h1)
        simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using this
      simp only [om]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hP _ _ this]
  · intro J hJ hJ'
    obtain ⟨S, hS⟩ := GlobalTheory.RootEx.UnfoldShape.exists_isReps_of_fg k _ ϖ hϖ _ hlat.fg
    obtain ⟨T, hT, hT'⟩ := GlobalTheory.RootEx.UnfoldShape.stabiliser_finite_cosets_mod k _ ϖ _ S hlat.fg hS
    refine ⟨T, hT, fun h => ⟨?_, ?_⟩⟩
    · rintro ⟨r, hr, t, ht, rfl⟩
      obtain ⟨t₀, ht₀, j, hj, hj', rfl⟩ := hT' t ht
      exact ⟨r, hr, t₀, ht₀, j, hJ' j hj hj', (mul_assoc _ _ _).symm⟩
    · rintro ⟨r, hr, t, ht, j, hj, rfl⟩
      exact ⟨r, hr, t * j, by rw [act_mul, hJ j hj, hT t ht], mul_assoc _ _ _⟩

theorem suppIn_opE {ϖ : 𝒪[k]} (ψ : AddChar k Circle) (ν : Measure k) {L' : Submodule 𝒪[k] (n' → k)}
    {L : Submodule 𝒪[k] (n → k)} {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hS : SuppIn Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L)) : SuppIn (opE ψ ν 1 Ψ) L' L := by
  intro x₀ hx v hv
  obtain ⟨y, -, hy⟩ := exists_pt_ne_zero hx
  have := hS _ hy _ (inX_mem_chainLat.2 hv)
  rwa [pt_mulVec_inX, inX_mem_chainLat] at this

theorem periodicMod_opE {ϖ : 𝒪[k]} (ψ : AddChar k Circle) (ν : Measure k) {L' : Submodule 𝒪[k] (n' → k)}
    {L : Submodule 𝒪[k] (n → k)} {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hP : PeriodicMod ϖ Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L)) : PeriodicMod ϖ (opE ψ ν 1 Ψ) L' L := by
  intro x₀ x₁ hx
  have h1 : MapsInto (fromBlocks x₁ 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
      (chainLat ϖ (c + 1) L') (chainLat ϖ c L) := by
    intro v hv
    rw [fromBlocks_mulVec, mem_chainLat]
    refine ⟨?_, fun i => ⟨0, by simp⟩⟩
    simpa [Function.comp_def] using hx _ (mem_chainLat.1 hv).1
  have h2 : (fromBlocks ((ϖ : k) • x₁) 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) =
      (ϖ : k) • fromBlocks x₁ 0 0 0 := by simp [fromBlocks_smul]
  simp only [opE_one_eq_volFree, pt_add_base, h2, hP _ _ h1]

theorem injSupp {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) (ψ : AddChar k Circle) (ν : Measure k)
    (L' : Submodule 𝒪[k] (n' → k)) : InjSupp ϖ ψ ν n c L' := by
  intro L _ Ψ _ hS _ hI x₀ hx
  have h0 := coe_ne_zero hϖ
  refine ⟨suppIn_opE ψ ν hS x₀ hx, fun v hv hxv => ?_⟩
  obtain ⟨y, -, hy⟩ := exists_pt_ne_zero hx
  have := (hI _ hy).2 _ (inX_mem_chainLat.2 hv) (by
    rw [pt_mulVec_inX, mem_smul_iff_inv h0, smul_inX, inX_mem_chainLat]
    exact (mem_smul_iff_inv h0).1 hxv)
  rw [mem_smul_iff_inv h0, smul_inX, inX_mem_chainLat] at this
  exact (mem_smul_iff_inv h0).2 this

theorem continuous_col (i : Fin c) :
    Continuous fun e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k => col e i := by
  refine continuous_pi fun r => ?_
  simp only [col]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem measurableSet_perLat {ϖ : 𝒪[k]} (h0 : (ϖ : k) ≠ 0) {L : Submodule 𝒪[k] (n → k)}
    (hL : Submodule.IsLattice k L) :
    MeasurableSet (perLat ϖ n' c L : Set ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k)) := by
  have := secondCountable k
  have ho := (GlobalTheory.RootEx.LatOpen.isOpen_and_relIndex_ne_zero k _ _ ((GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap k n c).1 ϖ h0 L hL)).1
  have : (perLat ϖ n' c L : Set ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k)) = ⋂ i : Fin c,
      (fun e => (ϖ : k) ^ (i.val + 1) • col (n' := n') e i) ⁻¹' (chainLat ϖ c L : Set (n ⊕ Fin c → k)) := by
    ext e
    simp only [SetLike.mem_coe, mem_perLat, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact (isOpen_iInter_of_finite fun i => ho.preimage ((continuous_col (n := n) (n' := n') i).const_smul ((ϖ : k) ^ (i.val + 1)))).measurableSet

theorem volFree_invariant (ν : Measure k) [ν.IsAddHaarMeasure] : (volFree ν n n' c).IsAddLeftInvariant := by
  have := secondCountable k
  unfold volFree
  infer_instance

theorem vol_perLat {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ν : Measure k} (hν : IsUnitVol ν)
    {L : Submodule 𝒪[k] (n → k)} (hL : Submodule.IsLattice k L) (hle : L ≤ stdLat k n) :
    volFree ν n n' c (perLat ϖ n' c L) ≠ ⊤ ∧ (((volFree ν n n' c).real (perLat ϖ n' c L) : ℝ) : ℂ) =
      (resCard k : ℂ) ^ expo c (Fintype.card n) /
        (L.toAddSubgroup.relIndex (stdLat k n).toAddSubgroup : ℂ) ^ c := by
  have := hν.1
  have := secondCountable k
  have := volFree_invariant (n := n) (n' := n') (c := c) ν
  have h0 := coe_ne_zero hϖ
  have hi := (GlobalTheory.RootEx.LatOpen.isOpen_and_relIndex_ne_zero k n L hL).2
  have hidx := GlobalTheory.RootEx.PerIndex.relIndex_perLat k n n' c ϖ h0 L
  have hbox := GlobalTheory.RootEx.UnfoldShape.volFree_perLat_stdLat k n n' c ϖ hϖ ν hν
  have hHL : perLat ϖ n' c L ≤ perLat ϖ n' c (stdLat k n) := fun e he i =>
    mem_chainLat.2 ⟨hle (mem_chainLat.1 (he i)).1, (mem_chainLat.1 (he i)).2⟩
  have : ((perLat ϖ n' c L).addSubgroupOf (perLat ϖ n' c (stdLat k n))).FiniteIndex :=
    ⟨by rw [← AddSubgroup.relIndex, hidx]; exact pow_ne_zero _ hi⟩
  have h := relIndex_mul_addVol _ _ hHL (measurableSet_perLat h0 hL) (volFree ν n n' c)
  refine ⟨ne_top_of_le_ne_top (by rw [hbox]; simp) (measure_mono hHL), ?_⟩
  rw [hbox, hidx] at h
  have h2 := congrArg (fun x : ENNReal => (x.toReal : ℂ)) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, Nat.cast_pow] at h2
  push_cast at h2
  rw [eq_div_iff (pow_ne_zero _ (Nat.cast_ne_zero.2 hi)), ← h2, mul_comm]
  rfl

theorem col_sub (e e' : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) :
    col (e - e') = col e - col e' := by
  rw [eq_sub_iff_add_eq, ← col_add, sub_add_cancel]

theorem formula {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) {L' : Submodule 𝒪[k] (n' → k)}
    {L : Submodule 𝒪[k] (n → k)} (hL : Submodule.IsLattice k L) (hle : L ≤ stdLat k n)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hS : SuppIn Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L))
    (hP : PeriodicMod ϖ Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L))
    (T : Fin c → Finset (n ⊕ Fin c → k))
    (hT : ∀ i, IsReps ϖ (chainLat ϖ c L ⊓ Yle k n c (i.val + 1)) (T i))
    (x₀ : Matrix n n' k) (hx : MapsInto x₀ L' L) :
    opE ψ ν 1 Ψ x₀ = (resCard k : ℂ) ^ expo c (Fintype.card n) /
        (L.toAddSubgroup.relIndex (stdLat k n).toAddSubgroup : ℂ) ^ c *
      ∑ w ∈ Fintype.piFinset T, term ϖ ψ Ψ x₀ w := by
  have := hν.1
  have := secondCountable k
  have := volFree_invariant (n := n) (n' := n') (c := c) ν
  have h0 := coe_ne_zero hϖ
  obtain ⟨hfin, hvol⟩ := vol_perLat (n' := n') (c := c) hϖ hν hL hle
  have hcol : ∀ w ∈ Fintype.piFinset T, col (uncol n' fun i => ((ϖ : k) ^ (i.val + 2))⁻¹ • w i) =
      fun i => ((ϖ : k) ^ (i.val + 2))⁻¹ • w i := fun w hw =>
    col_uncol fun i => smul_mem_Yle _ ((hT i).1 _ (Fintype.mem_piFinset.1 hw i)).2
  have hsc : ∀ (i : Fin c) (v : n ⊕ Fin c → k),
      (ϖ : k) ^ (i.val + 1) • ((ϖ : k) ^ (i.val + 2))⁻¹ • v = (ϖ : k)⁻¹ • v := by
    intro i v
    rw [smul_smul]
    congr 1
    field_simp
    ring
  rw [opE_one_eq_volFree, GlobalTheory.RootEx.UnfoldShape.integral_periodic_eq_measure_mul_sum_cosets _ (volFree ν n n' c) (perLat ϖ n' c L) (measurableSet_perLat h0 hL) hfin _ _
    (Fintype.piFinset T) (fun w => uncol n' fun i => ((ϖ : k) ^ (i.val + 2))⁻¹ • w i), hvol]
  · congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hcol w hw, term, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, Finset.sum_div]
    congr 4
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · intro e h hh
    have h1 : colMat n' (col h) = (ϖ : k) • colMat n' ((ϖ : k)⁻¹ • col h) := by
      rw [← colMat_smul, smul_inv_smul₀ h0]
    have h2 : MapsInto (colMat n' ((ϖ : k)⁻¹ • col h)) (chainLat ϖ (c + 1) L') (chainLat ϖ c L) := by
      refine mapsInto_colMat fun i => ?_
      rw [Pi.smul_apply, smul_smul, pow_succ, mul_inv_cancel_right₀ h0]
      exact hh i
    have h3 : ψ (-∑ i, col h i (Sum.inr i)) = 1 := by
      refine psi_int hψ (neg_mem (sum_mem fun i _ => ?_))
      obtain ⟨a, ha⟩ := (mem_chainLat.1 (hh i)).2 i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm] at ha
      rw [mul_right_cancel₀ (pow_ne_zero _ h0) ha]
      exact a.2
    simp only [col_add, pt_add, Pi.add_apply, Finset.sum_add_distrib, neg_add, AddChar.map_add_eq_mul, h3,
      mul_one]
    rw [h1, hP _ _ h2]
  · intro e he
    have hm := hS _ (left_ne_zero_of_mul he)
    have h1 : ∀ i : Fin c, (ϖ : k) ^ (i.val + 2) • col e i ∈ chainLat ϖ c L ⊓ Yle k n c (i.val + 1) := by
      intro i
      refine ⟨?_, smul_mem_Yle _ (col_mem_Yle e i)⟩
      have ha := scaled_basis_mem_chainLattice ϖ L' i.succ
      have := sub_mem (hm _ ha) (mapsInto_basePt hx _ ha)
      rw [pt_eq, Matrix.add_mulVec, add_sub_cancel_left] at this
      have e1 : colMat n' (col e) *ᵥ ((ϖ : k) ^ (i.succ.val + 1) • aux k n' i.succ) =
          (ϖ : k) ^ (i.val + 2) • col e i := by
        ext r
        rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, mulVec_auxiliaryBasisVectorSumFin_apply]
        simp [colMat]
      rwa [e1] at this
    choose w hw using fun i => ((hT i).2 _ (h1 i)).exists
    have hw' : w ∈ Fintype.piFinset T := Fintype.mem_piFinset.2 fun i => (hw i).1
    refine ⟨w, hw', fun i => ?_⟩
    have := ((mem_smul_iff_inv h0).1 (hw i).2).1
    rw [← hsc i, smul_sub ((ϖ : k) ^ (i.val + 2))⁻¹, inv_smul_smul₀ (pow_ne_zero _ h0)] at this
    rw [col_sub, hcol w hw']
    exact this
  · intro w hw w' hw' h
    funext i
    have hi := (hT i).1 _ (Fintype.mem_piFinset.1 hw i)
    have hi' := (hT i).1 _ (Fintype.mem_piFinset.1 hw' i)
    have h1 := h i
    rw [col_sub, hcol w hw, hcol w' hw', Pi.sub_apply, ← smul_sub, hsc] at h1
    refine ((hT i).2 _ hi).unique ⟨Fintype.mem_piFinset.1 hw i, by rw [sub_self]; exact zero_mem _⟩
      ⟨Fintype.mem_piFinset.1 hw' i, (mem_smul_iff_inv h0).2 ⟨h1, smul_mem_Yle _ (sub_mem hi.2 hi'.2)⟩⟩

theorem psi_pow_ringChar {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {s : k} (hs : s ∈ 𝒪[k]) : ψ (s / ϖ) ^ ringChar 𝓀[k] = 1 := by
  have h0 := coe_ne_zero hϖ
  have h1 : ((ringChar 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact (ringChar.spec _ _).2 dvd_rfl
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨a, ha⟩ := h1
  have h2 : (a : k) * ϖ = (ringChar 𝓀[k] : ℕ) := by exact_mod_cast congrArg Subtype.val ha
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ← h2]
  refine psi_int hψ ?_
  rw [mul_assoc, mul_div_cancel₀ _ h0]
  exact mul_mem a.2 hs

theorem funMod {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) (L' : Submodule 𝒪[k] (n' → k)) : FunMod ϖ ψ ν n c L' := by
  classical
  intro L hL Ψ _ hS hP
  have h0 := coe_ne_zero hϖ
  have hT : ∃ T : Fin c → Finset (n ⊕ Fin c → k),
      ∀ i, IsReps ϖ (chainLat ϖ c L ⊓ Yle k n c (i.val + 1)) (T i) := by
    have := fun i : Fin c => GlobalTheory.RootEx.UnfoldShape.exists_isReps_of_fg k _ ϖ hϖ (chainLat ϖ c L ⊓ Yle k n c (i.val + 1))
      (Submodule.FG.of_le ((GlobalTheory.RootEx.ChainLattice.isLattice_chainLat_and_comap k n c).1 ϖ h0 L hL).fg inf_le_left)
    choose T hT using this
    exact ⟨T, hT⟩
  refine ⟨suppIn_opE ψ ν hS, periodicMod_opE ψ ν hP, hT, fun hle =>
    ⟨fun T hT x₀ hx => formula hϖ hψ hν hL hle hS hP T hT x₀ hx, fun x₀ => ?_⟩⟩
  by_cases hx : MapsInto x₀ L' L
  · obtain ⟨T, hT⟩ := hT
    refine ⟨_, sum_mem fun w hw => ?_, formula hϖ hψ hν hL hle hS hP T hT x₀ hx⟩
    refine mul_mem (Subring.subset_closure (Or.inr ⟨_, rfl⟩)) (Subring.subset_closure (Or.inl ?_))
    rw [Set.mem_setOf_eq, ← map_pow, ← Circle.coe_pow, psi_pow_ringChar hϖ hψ, Circle.coe_one, map_one]
    refine sum_mem fun i _ => ?_
    obtain ⟨a, ha⟩ := (mem_chainLat.1 ((hT i).1 _ (Fintype.mem_piFinset.1 hw i)).1).2 i
    rw [ha, mul_div_cancel_right₀ _ (pow_ne_zero _ h0)]
    exact a.2
  · refine ⟨0, zero_mem _, ?_⟩
    rw [mul_zero]
    by_contra h
    exact hx (suppIn_opE ψ ν hS x₀ h)

theorem shape : GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.Shape :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc _ hϖ ψ hψ ν hν L' _ =>
    ⟨oneClass hc hϖ hψ hν L', oneCoset hc hϖ hψ hν L', funMod hϖ hψ hν L', injSupp hϖ ψ ν L'⟩

end GlobalTheory.RootEx.UnfoldShape
end
end
