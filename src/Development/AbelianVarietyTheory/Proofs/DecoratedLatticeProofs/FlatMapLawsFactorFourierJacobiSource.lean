import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatCompAffineMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionIntegrateEntryOfTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateShearHaarLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.PartRed

theorem sb_mul_addChar_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] (f : Matrix R Q k →ₗ[k] k) (z : k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => (ψ (f x + z) : ℂ) * Φ x) ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ ψ hψ R Q _ _ f z Φ hΦ
  classical
  obtain ⟨h1, h2⟩ := hΦ
  have hexp : ∀ x : Matrix R Q k, f x = ∑ i, ∑ j, x i j * f (Matrix.single i j 1) := by
    intro x
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← LinearMap.map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hf : Continuous f := by
    have : (f : Matrix R Q k → k) = fun x => ∑ i, ∑ j, x i j * f (Matrix.single i j 1) := funext hexp
    rw [this]
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_id.matrix_elem i j).mul continuous_const
  refine ⟨?_, ?_⟩
  · exact ((OpenKernel.isLocallyConstant_coe_addChar ψ hψ).comp_continuous
      (hf.add continuous_const)).mul h1
  · exact h2.mul_left

end GlobalTheory.PartRed
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_mul_addChar_linearForm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] (f : Matrix R Q k →ₗ[k] k) (z : k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => (ψ (f x + z) : ℂ) * Φ x) ∈ SB (Matrix R Q k) := by
  atlas_forward_decl GlobalTheory.PartRed.sb_mul_addChar_linear
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology

noncomputable section
namespace GlobalTheory.PartRedEval
open GlobalTheory.PartRed

section Alg
variable {k : Type} [Field k] {R Q : Type} [DecidableEq R] [DecidableEq Q]

theorem fillAt_apply_of_notMem (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (y : I → k) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by
  simp [fillAt, hE, hI]

theorem fillAt_add_single (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (u : k) (y : I → k) :
    fillAt β E I (x + Matrix.single e.1 e.2 u) y = fillAt β E I x y + Matrix.single e.1 e.2 u := by
  ext r q
  by_cases h : e = (r, q)
  · subst h
    simp [fillAt, hE, hI]
  · have h0 : Matrix.single e.1 e.2 u r q = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h (Prod.ext h'.1 h'.2))
    simp [fillAt, h0]

theorem fillAt_insert (β : Matrix R Q k) {E I : Finset (R × Q)} {e : R × Q} (hE : e ∉ E) (hI : e ∉ I)
    (x : Matrix R Q k) (y : I → k) :
    fillAt β (insert e E) I x y = fillAt β E I (x + Matrix.single e.1 e.2 (β e.1 e.2 - x e.1 e.2)) y := by
  ext r q
  by_cases h : e = (r, q)
  · subst h
    simp [fillAt, hE, hI]
  · have h0 : Matrix.single e.1 e.2 (β e.1 e.2 - x e.1 e.2) r q = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h' => h (Prod.ext h'.1 h'.2))
    have h1 : (r, q) ≠ e := fun h' => h h'.symm
    simp [fillAt, h0, h1]

end Alg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]

theorem continuous_form (w : Matrix R Q k →ₗ[k] k) : Continuous w := by
  have h : (w : Matrix R Q k → k) = fun m => ∑ i, ∑ j, m i j * w (Matrix.single i j 1) := by
    funext m
    conv_lhs => rw [Matrix.matrix_eq_sum_single m]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_id.matrix_elem i j).mul continuous_const

omit [Fintype R] [Fintype Q] in

theorem exists_cball_single {f : Matrix R Q k → ℂ} (hf : f ∈ SB (Matrix R Q k)) (e : R × Q) :
    ∃ s : kˣ, ∀ t ∈ cball s, ∀ x, f (x + Matrix.single e.1 e.2 t) = f x := by
  have hc : Continuous fun t : k => (Matrix.single e.1 e.2 t : Matrix R Q k) := by
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.single, Matrix.of_apply]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  have h1 : ∀ᶠ t in 𝓝 (0 : k), ∀ x ∈ tsupport f, f (x + Matrix.single e.1 e.2 t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : k × Matrix R Q k => (f (q.2 + Matrix.single e.1 e.2 q.1), f q.2) :=
      (hf.1.comp_continuous (continuous_snd.add (hc.comp continuous_fst))).prodMk
        (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, Matrix.single_zero, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  refine ⟨s, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hs ht x hx
  by_cases hx' : x + Matrix.single e.1 e.2 t ∈ tsupport f
  · have := hs (neg_mem_cball ht) _ hx'
    rw [← this, add_assoc, ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

def ballGrp (s : kˣ) : AddSubgroup k where
  carrier := cball s
  add_mem' := add_mem_cball
  zero_mem' := by simp [cball]
  neg_mem' := neg_mem_cball

theorem isLocallyConstant_mk (s : kˣ) : IsLocallyConstant (QuotientAddGroup.mk : k → k ⧸ ballGrp s) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have : (fun z => -x + z) ⁻¹' cball s ∈ 𝓝 x :=
    ((isOpen_cball s).preimage (by fun_prop)).mem_nhds (by simp [cball])
  filter_upwards [this] with z hz
  exact (QuotientAddGroup.eq.mpr hz).symm

theorem exists_sep {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) (s : kˣ) {d : k} (hd : d ∉ cball s) :
    ∃ b : k, ψ (b * d) ≠ 1 ∧ ∀ u ∈ cball s, ψ (b * u) = 1 := by
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one (c * s⁻¹) (x := d) (by
    rwa [show c * (c * s⁻¹)⁻¹ = s by rw [_root_.mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]])
  refine ⟨t, hne, fun u hu => h.eq_one ?_⟩
  have h1 : valuation k t ≤ valuation k ((c * s⁻¹ : kˣ) : k) := ht
  have h2 : valuation k u ≤ valuation k (s : k) := hu
  show valuation k (t * u) ≤ valuation k (c : k)
  have h3 : (c : k) = ((c * s⁻¹ : kˣ) : k) * s := by simp
  rw [h3, map_mul, map_mul]
  exact mul_le_mul' h1 h2

variable [MeasurableSpace k] [BorelSpace k]

theorem integrable_red {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure]
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) {Φ : Matrix R Q k → ℂ}
    (hΦ : Φ ∈ SB (Matrix R Q k)) (x : Matrix R Q k) :
    Integrable (fun y : I → k => Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ))
      (Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  haveI := t2Space k
  have hf : Continuous (fillAt β E I x) := by
    refine continuous_matrix fun r q => ?_
    simp only [fillAt, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
    · exact continuous_const
  have hp : Continuous fun (m : Matrix R Q k) (i : I) => m i.1.1 i.1.2 :=
    continuous_pi fun i => continuous_id.matrix_elem _ _
  have h1 : HasCompactSupport fun y : I → k => Φ (fillAt β E I x y) := by
    refine HasCompactSupport.intro (IsCompact.image hΦ.2 hp) fun y hy => ?_
    refine image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, ?_⟩
    funext i
    simp [fillAt]
  refine Continuous.integrable_of_hasCompactSupport ?_ h1.mul_right
  exact (hΦ.1.continuous.comp hf).mul
    (continuous_subtype_val.comp (hψ.comp ((continuous_form w).comp hf).neg))

theorem kills_insert_of_evalLaw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ I → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.EvalLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β (insert e E) I := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν R Q _ _ _ _ M _ _ L w β E I e hI hK hL
  classical
  by_cases hE : e ∈ E
  · rwa [Finset.insert_eq_of_mem hE]
  intro Φ hΦ
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hψ1
  obtain ⟨s₁, hs₁⟩ := exists_cball_single Φ.2 e
  have hn : (fun u : k => u * w (Matrix.single e.1 e.2 1)) ⁻¹' cball c ∈ 𝓝 (0 : k) :=
    ((isOpen_cball c).preimage (by fun_prop)).mem_nhds (by simp [cball])
  obtain ⟨s, hs⟩ := exists_cball_subset (Filter.inter_mem (cball_mem_nhds s₁) hn)

  have hinv : ∀ u ∈ cball s, ∀ x, red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ.1 x := by
    intro u hu x
    unfold red
    congr 1
    funext y
    have h1 : w (Matrix.single e.1 e.2 u) = u * w (Matrix.single e.1 e.2 1) := by
      rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [fillAt_add_single β hE hI, hs₁ u (hs hu).1, map_add, neg_add, AddChar.map_add_eq_mul, h1,
      hc.eq_one (neg_mem_cball (hs hu).2), mul_one]
  let p : Matrix R Q k → k ⧸ ballGrp s := fun x => QuotientAddGroup.mk (x e.1 e.2)
  have hp : IsLocallyConstant p := (isLocallyConstant_mk s).comp_continuous (continuous_id.matrix_elem _ _)
  let P : k ⧸ ballGrp s → SB (Matrix R Q k) := fun q =>
    ⟨fun x => (if p x = q then 1 else 0) * Φ.1 x,
      (hp.comp fun a => if a = q then (1 : ℂ) else 0).mul Φ.2.1, Φ.2.2.mul_left⟩
  have hred : ∀ q x, red ψ ν w β E I (P q).1 x = (if p x = q then 1 else 0) * red ψ ν w β E I Φ.1 x := by
    intro q x
    unfold red
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [P, p, fillAt_apply_of_notMem β hE hI, mul_assoc]
  have hP : ∀ q, L (P q) = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with | H a => ?_
    by_cases ha : a - β e.1 e.2 ∈ cball s
    · refine hK _ (funext fun x => ?_)
      rw [hred]
      split_ifs with hx
      · have h1 : -x e.1 e.2 + a ∈ cball s := QuotientAddGroup.eq.mp hx
        have h2 : β e.1 e.2 - x e.1 e.2 ∈ cball s := by
          have := add_mem_cball h1 (neg_mem_cball ha)
          convert this using 1
          ring
        have h3 := congrFun hΦ x
        rw [← hinv _ h2, one_mul]
        simpa only [red, fillAt_insert β hE hI] using h3
      · simp
    · obtain ⟨b, hb, hb'⟩ := exists_sep hc s ha
      obtain ⟨Φ', h1, h2⟩ := hL b (P a)
      set z : ℂ := (ψ (b * (a - β e.1 e.2)) : ℂ) with hz
      have h3 : L (Φ' - z • P a) = 0 := by
        refine hK _ (funext fun x => ?_)
        have h4 : red ψ ν w β E I (Φ' - z • P a).1 x =
            red ψ ν w β E I Φ'.1 x - z * red ψ ν w β E I (P a).1 x := by
          unfold red
          rw [← integral_const_mul, ← integral_sub (integrable_red hψ ν w β E I Φ'.2 x)
            ((integrable_red hψ ν w β E I (P a).2 x).const_mul z)]
          congr 1
          funext y
          simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [h4, h2, hred]
        split_ifs with hx
        · have h5 : -a + x e.1 e.2 ∈ cball s := QuotientAddGroup.eq.mp hx.symm
          have h6 : b * (x e.1 e.2 - β e.1 e.2) = b * (a - β e.1 e.2) + b * (-a + x e.1 e.2) := by ring
          rw [h6, AddChar.map_add_eq_mul, hb' _ h5, mul_one, hz]
          simp
        · simp
      rw [map_sub, map_smul, h1] at h3
      have h7 : (1 - z) ≠ 0 := fun h => hb (Circle.ext (by rw [← hz, Circle.coe_one]; exact (sub_eq_zero.mp h).symm))
      have h8 : (1 - z) • L (P a) = 0 := by rw [sub_smul, one_smul, h3]
      exact (smul_eq_zero.mp h8).resolve_left h7
  have hfin : (p '' tsupport Φ.1).Finite := by
    letI : TopologicalSpace (k ⧸ ballGrp s) := ⊥
    haveI : DiscreteTopology (k ⧸ ballGrp s) := ⟨rfl⟩
    exact (IsCompact.image Φ.2.2 hp.continuous).finite_of_discrete
  have hsum : Φ = ∑ q ∈ hfin.toFinset, P q := by
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, P, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Set.Finite.mem_toFinset]
    split_ifs with hx
    · rfl
    · exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨x, h, rfl⟩
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun q _ => hP q

end GlobalTheory.PartRedEval
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_evaluate_entry_of_mul_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ I → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.EvalLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β (insert e E) I := by
  atlas_forward_decl GlobalTheory.PartRedEval.kills_insert_of_evalLaw
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.PartRed.LowLaw

section Alg
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n'] [DecidableEq n'] in

theorem rowAdd_mul_apply (r l : Fin c) (a : k) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (p : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)) :
    ((fromBlocks 1 0 0 (transvection r l a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) p q =
      t p q + if p = Sum.inr r then a * t (Sum.inr l) q else 0 := by
  rw [mul_apply]
  rcases p with p | p
  · simp [Fintype.sum_sum_type, one_apply]
  · simp [Fintype.sum_sum_type, transvection, add_mul, Finset.sum_add_distrib, one_apply, single_apply,
      ite_and, eq_comm]

theorem mem_trans {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ transSet ρ ↔ Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val := by simp [transSet]

theorem mem_fix {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ fixSet ρ ↔ (∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨
      (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s) := by simp [fixSet]

theorem mem_low {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ lowSet ρ ↔ ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val := by simp [lowSet]

theorem fill_row_zero (ρ : ℕ) (l r : Fin c) (i : Fin (c + 1)) (hi : ρ < i.val) (hil : i.val ≤ l.val)
    (hr : r.val + 1 = i.val) (E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (hfix : fixSet ρ ⊆ E)
    (hlow : (lowSet ρ).filter (fun e => colIx e < i.val) ⊆ E)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : (transSet (n := n) (n' := n') (c := c) ρ) → k)
    (q : n' ⊕ Fin (c + 1)) (hq : (Sum.inr r, q) ∉ transSet (n := n) (n' := n') (c := c) ρ) :
    fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) q = 0 := by
  simp only [fillAt, of_apply]
  rcases q with s | j
  · have h1 : (Sum.inr l, Sum.inl s) ∉ transSet (n := n) (n' := n') (c := c) ρ := by
      rw [mem_trans]; simp [Free]; omega
    have h2 : (Sum.inr l, Sum.inl s) ∈ E := hfix (by rw [mem_fix]; right; exact ⟨l, s, rfl, by omega, rfl⟩)
    rw [dif_neg h1, if_pos h2]
    simp [basePt]
  · rw [mem_trans] at hq
    simp [Free] at hq
    have hj : j.val ≤ r.val := by omega
    have h1 : (Sum.inr l, Sum.inr j) ∉ transSet (n := n) (n' := n') (c := c) ρ := by
      rw [mem_trans]; simp [Free]; omega
    have h2 : (Sum.inr l, Sum.inr j) ∈ E := by
      by_cases hjρ : j.val ≤ ρ
      · exact hfix (by rw [mem_fix]; left; exact ⟨j, rfl, hjρ, by simp [Free]; omega⟩)
      · exact hlow (by
          rw [Finset.mem_filter, mem_low]
          exact ⟨⟨l, j, rfl, by omega, by omega⟩, by simp [colIx]; omega⟩)
    have hlj : l.val ≠ j.val := by omega
    rw [dif_neg h1, if_pos h2]
    simp [basePt, hlj]

theorem rowAdd_fill (ρ : ℕ) (l r : Fin c) (i : Fin (c + 1)) (hi : ρ < i.val) (hil : i.val ≤ l.val)
    (hr : r.val + 1 = i.val) (E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (hfix : fixSet ρ ⊆ E)
    (hlow : (lowSet ρ).filter (fun e => colIx e < i.val) ⊆ E) (b : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : (transSet (n := n) (n' := n') (c := c) ρ) → k) :
    (fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *
        fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y =
      fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x (y + fun j => if j.1.1 = Sum.inr r then
        b * fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) j.1.2 else 0) := by
  ext p q
  rw [rowAdd_mul_apply]
  by_cases hpq : (p, q) ∈ transSet (n := n) (n' := n') (c := c) ρ
  · conv_rhs => rw [fillAt, of_apply, dif_pos hpq]
    conv_lhs => rw [fillAt, of_apply, dif_pos hpq]
    rfl
  · have h0 : (if p = Sum.inr r then
        b * fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) q else 0) = 0 := by
      split_ifs with hp
      · subst hp
        rw [fill_row_zero ρ l r i hi hil hr E hfix hlow x y q hpq, mul_zero]
      · rfl
    rw [h0, add_zero]
    simp only [fillAt, of_apply, dif_neg hpq]

omit [Fintype n'] [DecidableEq n'] in
theorem ch_rowAdd (l r : Fin c) (i : Fin (c + 1)) (hr : r.val + 1 = i.val) (b : k)
    (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch ((fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) =
      ch t + b * t (Sum.inr l) (Sum.inr i) := by
  have hsi : r.succ = i := Fin.ext (by simp [hr])
  simp [ch, rowAdd_mul_apply, Finset.sum_add_distrib, hsi]

def elem (r l : Fin c) (h : r ≠ l) (a : k) : GL (Fin c) k :=
  ⟨transvection r l a, transvection r l (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem embA_elem_val (r l : Fin c) (h : r ≠ l) (a : k) :
    (embA n (elem r l h a)).val = fromBlocks 1 0 0 (transvection r l a) := rfl

theorem embA_elem_inv_val (r l : Fin c) (h : r ≠ l) (a : k) :
    ((embA n (elem r l h a))⁻¹).val = fromBlocks 1 0 0 (transvection r l (-a)) := rfl

theorem embA_elem_mem (r l : Fin c) (h : r ≠ l) (hrl : r.val < l.val) (a : k) (p : ℕ) :
    embA n (elem r l h a) ∈ N k n c p := by
  apply Subgroup.subset_closure
  show InN p _
  intro r' s hrs
  rw [embA_elem_val]
  rcases r' with r' | r' <;> rcases s with s | s
  · simp [one_apply]
  · simp [one_apply]
  · simp [one_apply]
  · simp only [lev, Sum.elim_inr] at hrs
    simp only [fromBlocks_apply₂₂, transvection, Matrix.add_apply, single_apply, one_apply, Sum.inr.injEq]
    have : ¬ (r = r' ∧ l = s) := by
      rintro ⟨rfl, rfl⟩
      omega
    rw [if_neg this, add_zero]

theorem simpleSum_elem (r l : Fin c) (h : r ≠ l) (a : k) :
    simpleSum (embA n (elem r l h a)) = if l.val = r.val + 1 then a else 0 := by
  rw [simpleSum, embA_elem_val]
  have key : ∀ i j : Fin c, (if j.val = i.val + 1 then
      (fromBlocks 1 0 0 (transvection r l a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr j) else 0) =
      if j = l then (if i = r then (if l.val = r.val + 1 then a else 0) else 0) else 0 := by
    intro i j
    simp only [fromBlocks_apply₂₂, transvection, Matrix.add_apply, single_apply]
    by_cases hij : j.val = i.val + 1
    · have hne : i ≠ j := fun h => by rw [h] at hij; omega
      rw [if_pos hij, one_apply_ne hne, zero_add]
      by_cases hi : i = r
      · subst hi
        by_cases hj : j = l
        · subst hj; simp [hij]
        · simp [hj, Ne.symm hj]
      · simp [hi, Ne.symm hi]
    · rw [if_neg hij]
      by_cases hi : i = r
      · subst hi
        by_cases hj : j = l
        · subst hj; simp [hij]
        · simp [hj]
      · simp [hi]
  simp only [key]
  simp

end Alg

theorem evalLaw_low : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∀ (l : Fin c) (i : Fin (c + 1)), ρ < i.val → i.val ≤ l.val → ∀ E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), GlobalTheory.PartRed.fixSet ρ ⊆ E → (GlobalTheory.PartRed.lowSet ρ).filter (fun e => GlobalTheory.PartRed.colIx e < i.val) ⊆ E → E ⊆ GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ → (Sum.inr l, Sum.inr i) ∉ E → GlobalTheory.PartRed.EvalLaw L ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) E (GlobalTheory.PartRed.transSet ρ) (Sum.inr l, Sum.inr i) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c ρ M _ _ L hc hL l i hi hil E hfix hlow hEsub hlE
  unfold GlobalTheory.PartRed.EvalLaw
  intro b Φ
  have hlc := l.isLt
  let r : Fin c := ⟨i.val - 1, by omega⟩
  have hr : r.val + 1 = i.val := by show i.val - 1 + 1 = i.val; omega
  have hrl' : r.val < l.val := by show i.val - 1 < l.val; omega
  have hrl : r ≠ l := fun h => by rw [h] at hrl'; exact lt_irrefl _ hrl'
  set β := basePt c (0 : Matrix n n' k) with hβ
  set T := GlobalTheory.PartRed.transSet (n := n) (n' := n') (c := c) ρ with hT
  set u := elem (k := k) r l hrl (-b) with hu
  have hgN : embA n u ∈ N k n c (ρ + 1) := embA_elem_mem r l hrl hrl' (-b) (ρ + 1)
  have hmem := GlobalTheory.T.schwartzBruhat_comp_affine_matrix k (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) (embA n u)⁻¹ 0 Φ.1 Φ.2
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := ⟨_, hmem⟩
  have hΦ₁ : ∀ t, Φ₁.1 t = Φ.1 (((embA n u)⁻¹).val * t) := fun t => by simp [Φ₁]
  have hL1 := hL u hgN Φ Φ₁ hΦ₁
  have hinv : ((embA n u)⁻¹).val = fromBlocks 1 0 0 (transvection r l b) := by
    rw [hu, embA_elem_inv_val, neg_neg]
  have hβli : β (Sum.inr l) (Sum.inr i) = if l.val = i.val then 1 else 0 := by
    simp [hβ, basePt]
  have hss : simpleSum (embA n u) = -(b * β (Sum.inr l) (Sum.inr i)) := by
    rw [hu, simpleSum_elem, hβli]
    by_cases h : l.val = i.val
    · rw [if_pos (by omega), if_pos h]; ring
    · rw [if_neg (by omega), if_neg h]; ring
  have hxli : ∀ x y, GlobalTheory.PartRed.fillAt β E T x y (Sum.inr l) (Sum.inr i) = x (Sum.inr l) (Sum.inr i) := by
    intro x y
    have h1 : (Sum.inr l, Sum.inr i) ∉ T := by rw [hT, mem_trans]; simp [Free]; omega
    simp only [GlobalTheory.PartRed.fillAt, of_apply, dif_neg h1, if_neg hlE]
  refine ⟨(ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) • Φ₁, ?_, ?_⟩
  · rw [map_smul, hL1, smul_smul, hss, neg_neg, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
  · intro x
    dsimp only
    let s : (T → k) → (T → k) := fun y j =>
      if j.1.1 = Sum.inr r then b * GlobalTheory.PartRed.fillAt β E T x y (Sum.inr l) j.1.2 else 0
    have hfill : ∀ y, (fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *
        GlobalTheory.PartRed.fillAt β E T x y = GlobalTheory.PartRed.fillAt β E T x (y + s y) :=
      fun y => rowAdd_fill ρ l r i hi hil hr E hfix hlow b x y
    have hch : ∀ y, ch (GlobalTheory.PartRed.fillAt β E T x (y + s y)) =
        ch (GlobalTheory.PartRed.fillAt β E T x y) + b * x (Sum.inr l) (Sum.inr i) := fun y => by
      rw [← hfill, ch_rowAdd l r i hr b, hxli]
    have hone : (ψ (b * x (Sum.inr l) (Sum.inr i)) : ℂ) * ψ (-(b * x (Sum.inr l) (Sum.inr i))) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
    let G : (T → k) → ℂ := fun y => Φ.1 (GlobalTheory.PartRed.fillAt β E T x y) *
      (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ)
    have key : ∀ y, Φ₁.1 (GlobalTheory.PartRed.fillAt β E T x y) * (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ) =
        (ψ (b * x (Sum.inr l) (Sum.inr i)) : ℂ) * G (y + s y) := by
      intro y
      simp only [G]
      rw [hΦ₁, hinv, hfill, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      linear_combination (-(Φ.1 (GlobalTheory.PartRed.fillAt β E T x (y + s y)) *
        (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ))) * hone
    let S : Finset T := Finset.univ.filter fun j => j.1.1 = Sum.inr r
    have hs_cont : Continuous s := by
      refine continuous_pi fun j => ?_
      simp only [s]
      split_ifs
      · refine continuous_const.mul ?_
        simp only [GlobalTheory.PartRed.fillAt, of_apply]
        split_ifs <;> first | exact continuous_apply _ | exact continuous_const
      · exact continuous_const
    have hs_dep : ∀ y y' : T → k, (∀ j, j ∉ S → y j = y' j) → s y = s y' := by
      intro y y' h
      funext j
      simp only [s]
      split_ifs
      · congr 1
        simp only [GlobalTheory.PartRed.fillAt, of_apply]
        split_ifs <;> first | rfl | exact h _ (by simp [S]; exact Ne.symm hrl)
      · rfl
    have hs_supp : ∀ (y : T → k) j, j ∉ S → s y j = 0 := by
      intro y j hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [s, if_neg hj]
    have hchg := GlobalTheory.T.integral_coordinate_shear_haar_localField k ν hν T S s hs_cont hs_dep hs_supp G
    simp only [GlobalTheory.PartRed.red, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, GlobalTheory.PartRed.chL_apply]
    calc ∫ y : T → k, (ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * Φ₁.1 (GlobalTheory.PartRed.fillAt β E T x y) *
          (ψ (-ch (GlobalTheory.PartRed.fillAt β E T x y)) : ℂ) ∂(Measure.pi fun _ => ν)
        = ∫ y : T → k, ((ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * ψ (b * x (Sum.inr l) (Sum.inr i))) *
          G (y + s y) ∂(Measure.pi fun _ => ν) := by
          congr 1; funext y; rw [mul_assoc, key, mul_assoc]
      _ = ((ψ (-(b * β (Sum.inr l) (Sum.inr i))) : ℂ) * ψ (b * x (Sum.inr l) (Sum.inr i))) *
          ∫ y : T → k, G y ∂(Measure.pi fun _ => ν) := by rw [integral_const_mul, hchg]
      _ = _ := by
          rw [show b * (x (Sum.inr l) (Sum.inr i) - β (Sum.inr l) (Sum.inr i)) =
            -(b * β (Sum.inr l) (Sum.inr i)) + b * x (Sum.inr l) (Sum.inr i) by ring,
            AddChar.map_add_eq_mul, Circle.coe_mul]

end GlobalTheory.PartRed.LowLaw
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_lower_entry_multiplication_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∀ (l : Fin c) (i : Fin (c + 1)), ρ < i.val → i.val ≤ l.val → ∀ E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), GlobalTheory.PartRed.fixSet ρ ⊆ E → (GlobalTheory.PartRed.lowSet ρ).filter (fun e => GlobalTheory.PartRed.colIx e < i.val) ⊆ E → E ⊆ GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ → (Sum.inr l, Sum.inr i) ∉ E → GlobalTheory.PartRed.EvalLaw L ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) E (GlobalTheory.PartRed.transSet ρ) (Sum.inr l, Sum.inr i) := by
  atlas_forward_decl GlobalTheory.PartRed.LowLaw.evalLaw_low
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.PartRed.UpperLaw
open GlobalTheory.PartRed

section Alg
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def elem (l m : Fin c) (h : l ≠ m) (a : k) : GL (Fin c) k :=
  ⟨transvection l m a, transvection l m (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem embA_elem_apply (l m : Fin c) (h : l ≠ m) (a : k) (r s : n ⊕ Fin c) :
    (embA n (elem l m h a)).val r s
      = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s + if r = Sum.inr l ∧ s = Sum.inr m then a else 0 := by
  have : (embA n (elem l m h a)).val = fromBlocks 1 0 0 (transvection l m a) := rfl
  rw [this]
  rcases r with r | r <;> rcases s with s | s <;>
    simp [transvection, Matrix.one_apply, Matrix.single_apply, eq_comm]

theorem elem_inv (l m : Fin c) (h : l ≠ m) (a : k) : (elem l m h (-a))⁻¹ = elem l m h a := by
  ext1
  show transvection l m (- -a) = transvection l m a
  rw [neg_neg]

theorem embA_elem_mul {Q : Type} (l m : Fin c) (h : l ≠ m) (a : k) (t : Matrix (n ⊕ Fin c) Q k) (r : n ⊕ Fin c) (q : Q) :
    ((embA n (elem l m h a)).val * t) r q = t r q + if r = Sum.inr l then a * t (Sum.inr m) q else 0 := by
  simp only [Matrix.mul_apply, embA_elem_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [Matrix.one_apply]
  · by_cases hr : r = Sum.inr l
    · simp [hr]
    · simp [hr]

theorem simpleSum_elem (l m : Fin c) (h : l ≠ m) (a : k) :
    simpleSum (embA n (elem l m h a)) = if m.val = l.val + 1 then a else 0 := by
  unfold simpleSum
  have : ∀ i j : Fin c, (if j.val = i.val + 1 then (embA n (elem l m h a)).val (Sum.inr i) (Sum.inr j) else 0)
      = if i = l then (if j = m then (if m.val = l.val + 1 then a else 0) else 0) else 0 := by
    intro i j
    rw [embA_elem_apply]
    by_cases h1 : j.val = i.val + 1
    · have : i ≠ j := by intro e; subst e; omega
      by_cases h2 : i = l <;> by_cases h3 : j = m <;> simp_all [Matrix.one_apply]
    · by_cases h2 : i = l <;> by_cases h3 : j = m <;> simp_all
  simp [this]

theorem elem_mem_N (ρ : ℕ) (l m : Fin c) (h : l ≠ m) (hlm : l.val < m.val) (hm : m.val ≤ ρ) (a : k) :
    embA n (elem l m h a) ∈ N k n c (ρ + 1) := by
  apply Subgroup.subset_closure
  intro r s hrs
  rw [embA_elem_apply, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  simp only [lev, Sum.elim_inr] at hrs
  omega

variable {ρ : ℕ} {I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))}

theorem free_of_mem (hI : I ⊆ transSet ρ ∪ upSet ρ) {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} (he : e ∈ I) :
    Free (ρ + 1) e := by
  rcases Finset.mem_union.1 (hI he) with h | h
  · simp only [transSet, Finset.mem_filter] at h
    exact h.2.1
  · simp only [upSet, Finset.mem_filter] at h
    obtain ⟨-, l, i, rfl, h1, -⟩ := h
    exact h1

theorem fill_low (hI : I ⊆ transSet ρ ∪ upSet ρ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k)
    (m : Fin c) (j : Fin (c + 1)) (hj : j.val ≤ m.val) (hm : j.val ≤ ρ) :
    fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y (Sum.inr m) (Sum.inr j)
      = if m.val = j.val then 1 else 0 := by
  have hf : ¬ Free (ρ + 1) ((Sum.inr m, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) := by
    show ¬ (m.val < j.val)
    omega
  have h1 : (Sum.inr m, Sum.inr j) ∉ I := fun h => hf (free_of_mem hI h)
  have h2 : ((Sum.inr m, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) ∈ fixSet ρ ∪ lowSet ρ := by
    apply Finset.mem_union_left
    simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨j, rfl, hm, hf⟩
  simp only [fillAt, Matrix.of_apply, dif_neg h1, if_pos h2]
  simp [basePt]

def shear (ρ : ℕ) (I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (l m : Fin c) (a : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k) : I → k :=
  fun e => if e.1.1 = Sum.inr l then
    a * fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y (Sum.inr m) e.1.2 else 0

theorem elem_mul_fill (l m : Fin c) (i : Fin (c + 1)) (h : l ≠ m) (hmi : m.val = i.val) (hl : l.val < i.val)
    (hi : i.val ≤ ρ) (h1 : transSet ρ ⊆ I) (h2 : (upSet ρ).filter (fun e => i.val < colIx e) ⊆ I)
    (hI : I ⊆ transSet ρ ∪ upSet ρ) (hli : (Sum.inr l, Sum.inr i) ∉ I) (a : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k) :
    (embA n (elem l m h a)).val * fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y
      = fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I (x + Matrix.single (Sum.inr l) (Sum.inr i) a)
          (y + shear ρ I l m a x y) := by
  ext r q
  rw [embA_elem_mul]
  by_cases hr : (r, q) ∈ I
  · conv_rhs => rw [fillAt, Matrix.of_apply, dif_pos hr]
    conv_lhs => enter [1]; rw [fillAt, Matrix.of_apply, dif_pos hr]
    rfl
  · conv_rhs => rw [fillAt, Matrix.of_apply, dif_neg hr]
    conv_lhs => enter [1]; rw [fillAt, Matrix.of_apply, dif_neg hr]
    by_cases hrl : r = Sum.inr l
    · subst hrl
      rw [if_pos rfl]
      have hT : ∀ q : n' ⊕ Fin (c + 1), Free (ρ + 1) ((Sum.inr l, q) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) →
          (∀ j, q = Sum.inr j → ρ < j.val) → (Sum.inr l, q) ∈ I := by
        intro q hq hq'
        apply h1
        simp only [transSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hq, hq'⟩
      rcases q with s | j
      · exact absurd (hT (Sum.inl s) (show l.val + 1 < ρ + 1 by omega) (by simp)) hr
      · have hj : j.val ≤ i.val := by
          by_contra hj
          apply hr
          by_cases hρ : ρ < j.val
          · refine hT _ (show l.val < j.val by omega) ?_
            intro j' e
            cases e
            exact hρ
          · apply h2
            simp only [upSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨l, j, rfl, by omega, by omega⟩, by simp only [colIx, Sum.elim_inr]; omega⟩
        rw [fill_low hI x y m j (by omega) (by omega)]
        by_cases hE : ((Sum.inr l, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) ∈ fixSet ρ ∪ lowSet ρ
        · rw [if_pos hE, if_pos hE]
          have : j.val ≤ l.val := by
            rcases Finset.mem_union.1 hE with h | h
            · simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
              rcases h with ⟨j', e, -, hf⟩ | ⟨_, _, -, -, e⟩
              · have : ¬ (l.val < j.val) := hf
                omega
              · cases e
            · simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
              obtain ⟨l', j', e, -, hf⟩ := h
              cases e
              exact hf
          rw [if_neg (by omega)]
          simp
        · rw [if_neg hE, if_neg hE, Matrix.add_apply]
          congr 1
          by_cases hij : i = j
          · subst hij
            simp [hmi]
          · have : ¬ m.val = j.val := fun e => hij (Fin.ext (by omega))
            simp [this, hij]
    · rw [if_neg hrl, add_zero, Matrix.add_apply, Matrix.single_apply_of_ne _ _ _ _ _ (fun e => hrl e.1.symm), add_zero]

theorem ch_elem_mul (l m : Fin c) (h : l ≠ m) (a : k) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch ((embA n (elem l m h a)).val * t) = ch t + a * t (Sum.inr m) (Sum.inr l.succ) := by
  simp [ch, embA_elem_mul, Finset.sum_add_distrib]

end Alg

theorem intLaw_up : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∀ (l : Fin c) (i : Fin (c + 1)), l.val < i.val → i.val ≤ ρ → ∀ I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), GlobalTheory.PartRed.transSet ρ ⊆ I → (GlobalTheory.PartRed.upSet ρ).filter (fun e => i.val < GlobalTheory.PartRed.colIx e) ⊆ I → I ⊆ GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ → (Sum.inr l, Sum.inr i) ∉ I → GlobalTheory.PartRed.IntLaw L ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) I (Sum.inr l, Sum.inr i) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c ρ M _ _ L hc hL l i hl hi I h1 h2 hI hli a Φ
  let m : Fin c := ⟨i.val, by omega⟩
  have hmi : m.val = i.val := rfl
  have h : l ≠ m := by intro e; rw [e] at hl; omega
  let d : k := if m.val = l.val + 1 then a else 0
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun x => Φ.1 ((embA n (elem l m h a)).val * x + 0), GlobalTheory.T.schwartzBruhat_comp_affine_matrix k _ _ _ 0 Φ.1 Φ.2⟩
  have hΦ₁ : ∀ x, Φ₁.1 x = Φ.1 ((embA n (elem l m h a)).val * x) := fun x => by simp only [Φ₁, add_zero]
  have hL₁ : L Φ₁ = (ψ d : ℂ) • L Φ := by
    have := hL (elem l m h (-a)) (elem_mem_N ρ l m h (by omega) (by omega) _) Φ Φ₁ (fun t => by
      rw [hΦ₁, ← map_inv, elem_inv])
    rw [this, simpleSum_elem]
    congr 3
    simp only [d]
    split_ifs <;> simp
  refine ⟨(ψ (-d) : ℂ) • Φ₁, ?_, fun x => ?_⟩
  · rw [map_smul, hL₁, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    simp
  · unfold red
    rw [← GlobalTheory.T.integral_coordinate_shear_haar_localField k ν hν I (Finset.univ.filter fun e : I => e.1.1 = Sum.inr l) (shear ρ I l m a x) ?_ ?_ ?_
      (fun y => Φ.1 (fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I
        (x + Matrix.single (Sum.inr l) (Sum.inr i) a) y) *
        (ψ (-chL (fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I
          (x + Matrix.single (Sum.inr l) (Sum.inr i) a) y)) : ℂ))]
    · congr 1
      funext y
      rw [← elem_mul_fill l m i h hmi hl hi h1 h2 hI hli a x y, chL_apply, chL_apply, ch_elem_mul,
        fill_low hI x y m l.succ (by rw [Fin.val_succ]; omega) (by rw [Fin.val_succ]; omega)]
      have hd : (a * if m.val = l.succ.val then 1 else 0) = d := by
        simp only [d, Fin.val_succ]
        split_ifs <;> simp
      rw [hd, Submodule.coe_smul, Pi.smul_apply, hΦ₁, smul_eq_mul, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    · refine continuous_pi fun e => ?_
      unfold shear
      split_ifs
      · refine continuous_const.mul ?_
        simp only [fillAt, Matrix.of_apply]
        split_ifs
        · exact continuous_apply _
        · exact continuous_const
        · exact continuous_const
      · exact continuous_const
    · intro y y' hy
      funext e
      unfold shear
      split_ifs
      · congr 1
        simp only [fillAt, Matrix.of_apply]
        split_ifs with he
        · apply hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro e
          exact h (Sum.inr_injective e).symm
        · rfl
        · rfl
      · rfl
    · intro y j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [shear, if_neg hj]

end GlobalTheory.PartRed.UpperLaw
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_upper_free_entry_translation_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∀ (l : Fin c) (i : Fin (c + 1)), l.val < i.val → i.val ≤ ρ → ∀ I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), GlobalTheory.PartRed.transSet ρ ⊆ I → (GlobalTheory.PartRed.upSet ρ).filter (fun e => i.val < GlobalTheory.PartRed.colIx e) ⊆ I → I ⊆ GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ → (Sum.inr l, Sum.inr i) ∉ I → GlobalTheory.PartRed.IntLaw L ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) I (Sum.inr l, Sum.inr i) := by
  atlas_forward_decl GlobalTheory.PartRed.UpperLaw.intLaw_up
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.RedFlatRow
open GlobalTheory.PartRed GlobalTheory.LocFlat

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_transSet_union_upSet (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) ↔ Free (ρ + 1) e := by
  rcases e with ⟨r | l, s | i⟩ <;> simp only [transSet, upSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] <;> simp [Free] <;> omega

def freeEquiv (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) :
    {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} ≃
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} :=
  Equiv.subtypeEquivRight (mem_transSet_union_upSet ρ)

theorem fill_eq (ρ : ℕ) (lρ : Fin c) (hl : lρ.val = ρ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) (transSet ρ ∪ upSet ρ) x y =
      affPt (ρ + 1) (fun r s => x (Sum.inl r) (Sum.inl s)) (fun rs => y ((freeEquiv n n' c ρ).symm rs)) +
        rowAt n c (ρ + 1) (fun s => x (Sum.inr lρ) (Sum.inl s)) := by
  ext r q
  simp only [fillAt, affPt, Matrix.add_apply, Matrix.of_apply]
  by_cases hI : (r, q) ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))
  · have hF : Free (ρ + 1) (r, q) := (mem_transSet_union_upSet ρ _).1 hI
    rw [dif_pos hI, dif_pos hF]
    have h1 : (freeEquiv n n' c ρ).symm ⟨(r, q), hF⟩ = ⟨(r, q), hI⟩ := rfl
    rw [h1]
    rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state
  · have hF : ¬ Free (ρ + 1) (r, q) := fun hF => hI ((mem_transSet_union_upSet ρ _).2 hF)
    rw [dif_neg hI, dif_neg hF]
    by_cases hE : (r, q) ∈ (fixSet ρ ∪ lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))
    · rw [if_pos hE]
      simp only [fixSet, lowSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hE
      rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF hE ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state
    · rw [if_neg hE]
      simp only [fixSet, lowSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hE
      rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF hE ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state

theorem ch_add_rowAt (p : ℕ) (A : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (u : n' → k) :
    ch (A + rowAt n c p u) = ch A := by
  simp [ch, rowAt, Matrix.fromBlocks]

theorem piCongrLeft_freeEquiv [MeasurableSpace k] (ρ : ℕ)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    MeasurableEquiv.piCongrLeft (fun _ => k) (freeEquiv n n' c ρ) y =
      fun rs => y ((freeEquiv n n' c ρ).symm rs) := by
  funext rs
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

end GlobalTheory.RedFlatRow

open GlobalTheory.RedFlatRow in

theorem GlobalTheory.RedFlatRow.red_eq_flRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ + 1 → ∀ (lρ : Fin c), lρ.val = ρ → ∀ (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.PartRed.red ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) (GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ) Φ x = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ (Matrix.of fun r s => Sum.elim (fun r => x (Sum.inl r) (Sum.inl s)) (fun _ => x (Sum.inr lρ) (Sum.inl s)) r) := by
  intro k _ _ _ _ _ _ ψ ν hν n n' _ _ _ _ c ρ _ lρ hl Φ x
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  have hmp := MeasureTheory.measurePreserving_piCongrLeft (α := fun _ => k)
    (fun _ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} => ν) (freeEquiv n n' c ρ)
  simp only [GlobalTheory.PartRed.red, GlobalTheory.LocFlat.flRow, opE]
  refine Eq.trans ?_ (hmp.integral_comp' _)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [piCongrLeft_freeEquiv, fill_eq ρ lρ hl x y, GlobalTheory.PartRed.chL_apply, ch_add_rowAt]
  rfl
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_eq_flatMapFourierJacobiRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ + 1 → ∀ (lρ : Fin c), lρ.val = ρ → ∀ (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.PartRed.red ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) (GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ) Φ x = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ (Matrix.of fun r s => Sum.elim (fun r => x (Sum.inl r) (Sum.inl s)) (fun _ => x (Sum.inr lρ) (Sum.inl s)) r) := by
  atlas_forward_decl GlobalTheory.RedFlatRow.red_eq_flRow
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LocFlat

theorem add_right_mem_SB {m m' k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
    {Φ : Matrix m m' k → ℂ} (hΦ : Φ ∈ SB (Matrix m m' k)) (a : Matrix m m' k) :
    (fun z => Φ (z + a)) ∈ SB (Matrix m m' k) :=
  ⟨hΦ.1.comp_continuous (continuous_add_right a), hΦ.2.comp_homeomorph (Homeomorph.addRight a)⟩

theorem flRow_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → GlobalTheory.LocFlat.flRow ψ ν p (Φ₁ + Φ₂) = GlobalTheory.LocFlat.flRow ψ ν p Φ₁ + GlobalTheory.LocFlat.flRow ψ ν p Φ₂ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p Φ₁ Φ₂ h₁ h₂
  funext x
  have H := opE_smul_add p hψ ν (1 : ℂ)
    (add_right_mem_SB h₁ (rowAt n c p (x (Sum.inr ()))))
    (add_right_mem_SB h₂ (rowAt n c p (x (Sum.inr ()))))
  have H' := congrFun H x.toRows₁
  simp only [one_smul, Pi.add_apply] at H'
  simp only [flRow, Pi.add_apply]
  rw [← H']
  rfl

end GlobalTheory.LocFlat
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMapFourierJacobiRow_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → GlobalTheory.LocFlat.flRow ψ ν p (Φ₁ + Φ₂) = GlobalTheory.LocFlat.flRow ψ ν p Φ₁ + GlobalTheory.LocFlat.flRow ψ ν p Φ₂ := by
  atlas_forward_decl GlobalTheory.LocFlat.flRow_add
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

section Glue
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] {M : Type} [AddCommGroup M]
  [Module ℂ M]

theorem fillAt_entry (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by
  obtain ⟨r, q⟩ := e
  simp [fillAt, hI, hE]

theorem red_mul_entry (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E) (g : k → ℂ) (Φ : Matrix R Q k → ℂ)
    (x : Matrix R Q k) :
    red ψ ν w β E I (fun t => g (t e.1 e.2) * Φ t) x = g (x e.1 e.2) * red ψ ν w β E I Φ x := by
  unfold red
  simp_rw [fillAt_entry β E I x _ e hI hE, mul_assoc]
  exact integral_const_mul _ _

theorem fillAt_add_single (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) (a : k) :
    fillAt β E I x y + Matrix.single e.1 e.2 a = fillAt β E I (x + Matrix.single e.1 e.2 a) y := by
  obtain ⟨r₀, q₀⟩ := e
  ext r q
  by_cases h1 : (r, q) ∈ I
  · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hI h1
    simp [fillAt, h1, Matrix.single_apply, this]
  · by_cases h2 : (r, q) ∈ E
    · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hE h2
      simp [fillAt, h1, h2, Matrix.single_apply, this]
    · simp [fillAt, h1, h2]

theorem circle_neg_mul (ψ : AddChar k Circle) (z : k) : (ψ (-z) : ℂ) * (ψ z : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem evalLaw_direct (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E)
    (h : ∀ (b : k) (Φ Φ' : SB (Matrix R Q k)), (∀ t, Φ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Φ.1 t) →
      L Φ' = L Φ) :
    EvalLaw L ψ ν w β E I e := by
  intro b Φ
  let f : Matrix R Q k →ₗ[k] k :=
    { toFun := fun t => b * t e.1 e.2
      map_add' := fun s t => by simp [mul_add]
      map_smul' := fun a t => by simp; ring }
  have hmem : (fun t => (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Φ.1 t) ∈ SB (Matrix R Q k) := by
    have := GlobalTheory.T.schwartzBruhat_mul_addChar_linearForm k ψ hψ R Q f (-(b * β e.1 e.2)) Φ.1 Φ.2
    convert this using 3 with t
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk]
    ring_nf
  refine ⟨⟨_, hmem⟩, h b Φ ⟨_, hmem⟩ (fun t => rfl), fun x => ?_⟩
  exact red_mul_entry ψ ν w β E I e hI hE (fun s => (ψ (b * (s - β e.1 e.2)) : ℂ)) Φ.1 x

theorem intLaw_direct (ψ : AddChar k Circle) (ν : Measure k) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E)
    (h : ∀ (a : k) (Φ Φ' : SB (Matrix R Q k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single e.1 e.2 a)) →
      L Φ' = (ψ (w (Matrix.single e.1 e.2 a)) : ℂ) • L Φ) :
    IntLaw L ψ ν w β E I e := by
  intro a Φ
  have hmem1 : (fun t => Φ.1 (t + Matrix.single e.1 e.2 a)) ∈ SB (Matrix R Q k) := by
    have := GlobalTheory.T.schwartzBruhat_comp_affine_matrix k R Q 1 (Matrix.single e.1 e.2 a) Φ.1 Φ.2
    simpa using this
  let Φa : SB (Matrix R Q k) := ⟨_, hmem1⟩
  refine ⟨(ψ (-w (Matrix.single e.1 e.2 a)) : ℂ) • Φa, ?_, fun x => ?_⟩
  · rw [map_smul, h a Φ Φa (fun t => rfl), smul_smul, circle_neg_mul, one_smul]
  · unfold red
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Φa]
    congr 1
    funext y
    rw [← fillAt_add_single β E I x y e hI hE a, map_add, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring

theorem kills_empty (ψ : AddChar k Circle) (ν : Measure k) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) : Kills L ψ ν w β ∅ ∅ := by
  intro Φ hΦ
  have h0 : Φ = 0 := by
    apply Subtype.ext
    funext x
    have hx := congrFun hΦ x
    unfold red at hx
    have hf : ∀ y : (∅ : Finset (R × Q)) → k, fillAt β ∅ ∅ x y = x := fun y => by ext r q; simp [fillAt]
    simp only [hf] at hx
    rw [integral_const] at hx
    have hv : (Measure.pi fun _ : (∅ : Finset (R × Q)) => ν) Set.univ = 1 := by
      rw [Measure.pi_of_empty]; simp
    have hv' : (Measure.pi fun _ : (∅ : Finset (R × Q)) => ν).real Set.univ = 1 := by
      simp [Measure.real, hv]
    rw [hv', one_smul, Pi.zero_apply] at hx
    rw [Submodule.coe_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp hx).resolve_right (Circle.coe_ne_zero _)
  rw [h0, map_zero]

end Glue
end GlobalTheory.PartRed

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

section Glue2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] {M : Type} [AddCommGroup M]
  [Module ℂ M]

theorem kills_evals (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hν : ν.IsAddHaarMeasure) (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (I : Finset (R × Q)) (S : Finset (R × Q)) : ∀ E : Finset (R × Q), Disjoint S I → Kills L ψ ν w β E I →
    (∀ e ∈ S, ∀ E' : Finset (R × Q), E ⊆ E' → E' ⊆ E ∪ S → e ∉ E' → EvalLaw L ψ ν w β E' I e) →
    Kills L ψ ν w β (E ∪ S) I := by
  induction S using Finset.induction_on with
  | empty => intro E _ hK _; simpa using hK
  | insert a S ha ih =>
    intro E hdisj hK hlaw
    have hdisj' : Disjoint S I := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisj
    have h1 : Kills L ψ ν w β (E ∪ S) I := ih E hdisj' hK fun e he E' h1 h2 h3 =>
      hlaw e (Finset.mem_insert_of_mem he) E' h1
        (h2.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))) h3
    have haI : a ∉ I := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self _ _)
    have heq : E ∪ insert a S = insert a (E ∪ S) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [heq]
    by_cases haE : a ∈ E ∪ S
    · rwa [Finset.insert_eq_of_mem haE]
    · refine GlobalTheory.T.partialReduction_evaluate_entry_of_mul_law k ψ ν hψ hψ1 hν R Q M L w β (E ∪ S) I a haI h1 ?_
      refine hlaw a (Finset.mem_insert_self _ _) (E ∪ S) Finset.subset_union_left ?_ haE
      exact Finset.union_subset_union_right (Finset.subset_insert _ _)

theorem kills_ints (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ)
    (hν : ν.IsAddHaarMeasure) (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E : Finset (R × Q)) (S : Finset (R × Q)) : ∀ I : Finset (R × Q), Disjoint S E → Kills L ψ ν w β E I →
    (∀ e ∈ S, ∀ I' : Finset (R × Q), I ⊆ I' → I' ⊆ I ∪ S → e ∉ I' → IntLaw L ψ ν w β E I' e) →
    Kills L ψ ν w β E (I ∪ S) := by
  induction S using Finset.induction_on with
  | empty => intro I _ hK _; simpa using hK
  | insert a S ha ih =>
    intro I hdisj hK hlaw
    have hdisj' : Disjoint S E := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisj
    have h1 : Kills L ψ ν w β E (I ∪ S) := ih I hdisj' hK fun e he I' h1 h2 h3 =>
      hlaw e (Finset.mem_insert_of_mem he) I' h1
        (h2.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))) h3
    have haE : a ∉ E := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self _ _)
    have heq : I ∪ insert a S = insert a (I ∪ S) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [heq]
    by_cases haI : a ∈ I ∪ S
    · rwa [Finset.insert_eq_of_mem haI]
    · refine GlobalTheory.T.partialReduction_integrate_entry_of_translation k ψ ν hψ hν R Q M L w β E (I ∪ S) a haE h1 ?_
      refine hlaw a (Finset.mem_insert_self _ _) (I ∪ S) Finset.subset_union_left ?_ haI
      exact Finset.union_subset_union_right (Finset.subset_insert _ _)

end Glue2
end GlobalTheory.PartRed

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

section Sets
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_fixSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ fixSet ρ ↔
    ((∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨ (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s)) := by
  simp [fixSet]

theorem mem_transSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ transSet ρ ↔
    (Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val) := by
  simp [transSet]

theorem mem_lowSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ lowSet ρ ↔
    ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val := by
  simp [lowSet]

theorem mem_upSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ upSet ρ ↔
    ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ l.val < i.val ∧ i.val ≤ ρ := by
  simp [upSet]

theorem disj_trans_fix (ρ : ℕ) :
    Disjoint (transSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (fixSet ρ) := by
  rw [Finset.disjoint_left]
  rintro ⟨r, q⟩ h1 h2
  rw [mem_transSet] at h1
  rw [mem_fixSet] at h2
  rcases h2 with ⟨i, hq, hi, hnf⟩ | ⟨l, s, hr, hl, hq⟩
  · exact hnf h1.1
  · dsimp only at hr hq
    subst hr hq
    have := h1.1
    simp only [Free] at this
    omega

theorem disj_low_trans (ρ : ℕ) :
    Disjoint (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (transSet ρ) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨l, i, rfl, -, hil⟩ := mem_lowSet.mp h1
  have := (mem_transSet.mp h2).1
  simp only [Free] at this
  omega

theorem disj_up_fixlow (ρ : ℕ) :
    Disjoint (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (fixSet ρ ∪ lowSet ρ) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨l, i, rfl, hli, hiρ⟩ := mem_upSet.mp h1
  rcases Finset.mem_union.mp h2 with h | h
  · rcases mem_fixSet.mp h with ⟨i', hq, -, hnf⟩ | ⟨l', s, -, -, hq⟩
    · exact hnf (by simp only [Free]; exact hli)
    · simp at hq
  · obtain ⟨l', i', he, -, hil⟩ := mem_lowSet.mp h
    simp only [Prod.mk.injEq, Sum.inr.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    omega

end Sets

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
  {M : Type} [AddCommGroup M] [Module ℂ M]

theorem kills_low (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hν : ν.IsAddHaarMeasure) (ρ : ℕ) (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hc : c = 2 * ρ + 1)
    (H4 : ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ)
    (K : Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ) (transSet ρ)) :
    ∀ j : ℕ, Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ (lowSet ρ).filter (fun e => colIx e < j))
      (transSet ρ) := by
  intro j
  induction j with
  | zero => simpa using K
  | succ j ih =>
    have hsplit : (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => colIx e < j + 1) =
        (lowSet ρ).filter (fun e => colIx e < j) ∪ (lowSet ρ).filter (fun e => colIx e = j) := by
      ext e
      by_cases h : e ∈ (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) <;> simp [h] <;> omega
    rw [hsplit, ← Finset.union_assoc]
    refine kills_evals ψ ν hψ hψ1 hν L chL _ (transSet ρ) _ _
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (disj_low_trans ρ)) ih ?_
    intro e he E' h1 h2 h3
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨l, i, rfl, hρi, hil⟩ := mem_lowSet.mp he1
    simp only [colIx, Sum.elim_inr] at he2
    refine GlobalTheory.T.partialReduction_lower_entry_multiplication_law k ψ ν hψ hν n n' c ρ M L hc H4 l i hρi hil E'
      (Finset.subset_union_left.trans h1) ?_ ?_ h3
    · intro x hx
      apply h1
      refine Finset.mem_union_right _ ?_
      simpa [he2] using hx
    · refine h2.trans ?_
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter] at hx ⊢
      tauto

theorem kills_up (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ)
    (hν : ν.IsAddHaarMeasure) (ρ : ℕ) (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hc : c = 2 * ρ + 1)
    (H4 : ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ)
    (K : Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) (transSet ρ)) :
    ∀ d j : ℕ, j + d = c + 1 → Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ)
      (transSet ρ ∪ (upSet ρ).filter (fun e => j ≤ colIx e)) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hemp : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => j ≤ colIx e) = ∅ := by
      apply Finset.filter_false_of_mem
      intro e he
      obtain ⟨l, i, rfl, -, -⟩ := mem_upSet.mp he
      simp only [colIx, Sum.elim_inr]
      have := i.isLt
      omega
    rw [hemp, Finset.union_empty]
    exact K
  | succ d ih =>
    intro j hj
    have hsplit : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => j ≤ colIx e) =
        (upSet ρ).filter (fun e => j + 1 ≤ colIx e) ∪ (upSet ρ).filter (fun e => colIx e = j) := by
      ext e
      by_cases h : e ∈ (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) <;> simp [h] <;> omega
    rw [hsplit, ← Finset.union_assoc]
    refine kills_ints ψ ν hψ hν L chL _ (fixSet ρ ∪ lowSet ρ) _ _
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (disj_up_fixlow ρ)) (ih (j + 1) (by omega)) ?_
    intro e he I' h1 h2 h3
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨l, i, rfl, hli, hiρ⟩ := mem_upSet.mp he1
    simp only [colIx, Sum.elim_inr] at he2
    refine GlobalTheory.T.partialReduction_upper_free_entry_translation_law k ψ ν hψ hν n n' c ρ M L hc H4 l i hli hiρ I'
      (Finset.subset_union_left.trans h1) ?_ ?_ h3
    · intro x hx
      apply h1
      refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    · refine h2.trans ?_
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter] at hx ⊢
      tauto

end Main
end GlobalTheory.PartRed

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

theorem flRow_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s, r = Sum.inr l ∧ ρ < l.val ∧ q = Sum.inl s) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ < i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν n n' _ _ _ _ c ρ M _ _ L hc H1 H2 H3 H4
  have K0 := kills_empty ψ ν L chL (basePt c (0 : Matrix n n' k))
  have K1 := kills_evals ψ ν hψ hψ1 hν L chL (basePt c (0 : Matrix n n' k)) ∅ (fixSet ρ) ∅
    (Finset.disjoint_empty_right _) K0 (by
      intro e he E' _ _ heE'
      refine evalLaw_direct ψ ν hψ L chL _ E' ∅ e (Finset.notMem_empty _) heE' ?_
      obtain ⟨r, q⟩ := e
      rcases mem_fixSet.mp he with h | h
      · exact H1 r q h
      · exact H2 r q h)
  rw [Finset.empty_union] at K1
  have K2 := kills_ints ψ ν hψ hν L chL (basePt c (0 : Matrix n n' k)) (fixSet ρ) (transSet ρ) ∅
    (disj_trans_fix ρ) K1 (by
      intro e he I' _ _ heI'
      refine intLaw_direct ψ ν L chL _ (fixSet ρ) I' e heI'
        (Finset.disjoint_left.mp (disj_trans_fix ρ) he) ?_
      obtain ⟨r, q⟩ := e
      have h := mem_transSet.mp he
      intro a Φ Φ' hΦ'
      rw [chL_apply]
      exact H3 r q h.1 h.2 a Φ Φ' hΦ')
  rw [Finset.empty_union] at K2
  have K3 := kills_low ψ ν hψ hψ1 hν ρ L hc H4 K2 (c + 1)
  have hlow : (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => colIx e < c + 1) = lowSet ρ := by
    apply Finset.filter_true_of_mem
    intro e he
    obtain ⟨l, i, rfl, -, -⟩ := mem_lowSet.mp he
    simp only [colIx, Sum.elim_inr]
    exact i.isLt
  rw [hlow] at K3
  have K4 := kills_up ψ ν hψ hν ρ L hc H4 K3 (c + 1) 0 (by omega)
  have hup : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => 0 ≤ colIx e) = upSet ρ := by
    apply Finset.filter_true_of_mem
    intro e _
    exact Nat.zero_le _
  rw [hup] at K4
  have hρc : ρ < c := by omega
  let lρ : Fin c := ⟨ρ, hρc⟩
  let F : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (Matrix (n ⊕ Unit) n' k → ℂ) :=
    { toFun := fun Φ => flRow ψ ν (ρ + 1) Φ.1
      map_add' := fun Φ₁ Φ₂ => GlobalTheory.T.flatMapFourierJacobiRow_add k ψ ν hψ hν n n' c (ρ + 1) Φ₁.1 Φ₂.1 Φ₁.2 Φ₂.2
      map_smul' := fun a Φ => by
        funext x
        simp only [flRow, opE, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  have hker : LinearMap.ker F ≤ LinearMap.ker L := by
    intro Φ hΦ
    rw [LinearMap.mem_ker] at hΦ ⊢
    apply K4
    funext x
    rw [GlobalTheory.T.partialReduction_eq_flatMapFourierJacobiRow k ψ ν hν n n' c ρ hc lρ rfl Φ.1 x]
    exact congrFun hΦ _
  let f₀ : LinearMap.range F →ₗ[ℂ] M := (LinearMap.ker F).liftQ L hker ∘ₗ F.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f₀
  refine ⟨g ∘ₗ (SB (Matrix (n ⊕ Unit) n' k)).subtype, fun Φ Ψ hΨ => ?_⟩
  have h1 : g (F Φ) = L Φ := by
    have := LinearMap.congr_fun hg ⟨F Φ, LinearMap.mem_range_self F Φ⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [this]
    simp [f₀, LinearMap.quotKerEquivRange_symm_apply_image]
  rw [LinearMap.comp_apply, Submodule.coe_subtype, hΨ]
  exact h1.symm

end GlobalTheory.PartRed
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_laws_factor_fourierJacobi_source : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s, r = Sum.inr l ∧ ρ < l.val ∧ q = Sum.inl s) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ < i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  atlas_forward_decl GlobalTheory.PartRed.flRow_factor
end
