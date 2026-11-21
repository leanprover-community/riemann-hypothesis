import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensorActionApplyDual
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.IndicatorRholMem
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Transfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquivB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OpEqExp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {MM : Type*} [AddCommGroup MM] [Module ℂ MM]

def wOp (E : Fin n → Fin n → Module.End ℂ M) : (List (Fin n × Fin n) →₀ ℂ) →ₗ[ℂ] Module.End ℂ M :=
  Finsupp.linearCombination ℂ (wordE E)

def lOp (E : Fin n → Fin n → Module.End ℂ M) : (Fin n × Fin n →₀ ℂ) →ₗ[ℂ] Module.End ℂ M :=
  Finsupp.linearCombination ℂ (fun q => E q.1 q.2)

theorem wordE_cons_mul (E : Fin n → Fin n → Module.End ℂ M) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    wordE E (p :: w) = E p.1 p.2 * wordE E w := by
  simp [wordE]

theorem wOp_mapDomain_cons (E : Fin n → Fin n → Module.End ℂ M) (p : Fin n × Fin n)
    (L : List (Fin n × Fin n) →₀ ℂ) :
    wOp E (Finsupp.mapDomain (p :: ·) L) = E p.1 p.2 * wOp E L := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy, mul_add]
  | single w r =>
    rw [Finsupp.mapDomain_single]
    simp [wOp, Finsupp.linearCombination_single, wordE_cons_mul]

theorem wOp_mapDomain_letter (E : Fin n → Fin n → Module.End ℂ M) (w : List (Fin n × Fin n))
    (l : Fin n × Fin n →₀ ℂ) :
    wOp E (Finsupp.mapDomain (· :: w) l) = lOp E l * wordE E w := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy, add_mul]
  | single q r =>
    rw [Finsupp.mapDomain_single]
    simp [wOp, lOp, Finsupp.linearCombination_single, wordE_cons_mul]

theorem lOp_adL (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) (p : Fin n × Fin n) :
    lOp E (adL a b p) = E a b * E p.1 p.2 - E p.1 p.2 * E a b := by
  rw [hE a b p.1 p.2]
  unfold adL
  split_ifs <;> simp [lOp, Finsupp.linearCombination_single]

theorem wOp_adLW (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    ∀ w, wOp E (adLW a b w) = E a b * wordE E w - wordE E w * E a b
  | [] => by simp [adLW, wordE]
  | p :: w => by
    rw [adLW, map_add, wOp_mapDomain_letter, wOp_mapDomain_cons, wOp_adLW E hE a b w, lOp_adL E hE,
      wordE_cons_mul]
    noncomm_ring

section Lift

variable (V : Submodule ℂ M)

def Bc (c : Fin n) (v : V) : (List (Fin n × Fin n) →₀ ℂ) →ₗ[ℂ] KS (n := n) V :=
  Finsupp.linearCombination ℂ (fun w' => Finsupp.single (w', c) v)

theorem Bc_single (c : Fin n) (v : V) (w : List (Fin n × Fin n)) (r : ℂ) :
    Bc V c v (Finsupp.single w r) = Finsupp.single (w, c) (r • v) := by
  simp [Bc, Finsupp.linearCombination_single, Finsupp.smul_single]

theorem sum_eq_Bc (c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    (∑ w' ∈ L.support, L w' • Finsupp.lsingle (R := ℂ) (M := V) (w', c)) v = Bc V c v L := by
  simp [Bc, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]

variable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (hV : IsKStableSub ε E V)

theorem sA_single (a b : Fin n) (w : List (Fin n × Fin n)) (c : Fin n) (v : V) :
    sA ε E V hV a b (Finsupp.single (w, c) v) =
      Bc V c v (adLW a b w) +
      (if h : ε a = ε b then Finsupp.single (w, c) ((E a b).restrict (fun v hv => hV a b h v hv) v) else 0) +
      (if c = b then Finsupp.single (w, a) v else 0) := by
  simp only [sA, Finsupp.lsum_single, LinearMap.add_apply, sum_eq_Bc]
  congr 1
  · congr 1
    split_ifs <;> simp
  · split_ifs <;> simp

theorem sT_Bc (c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    sT E V (Bc V c v L) = Pi.single c (wOp E L v) := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_apply, Pi.single_add]
  | single w r =>
    rw [Bc_single, sT_single]
    simp [wOp, Finsupp.linearCombination_single, Pi.single_smul]

theorem sθ_Bc (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM) (ℓ : V →ₗ[ℂ] ℂ) (c : Fin n) (v : V)
    (L : List (Fin n × Fin n) →₀ ℂ) :
    sθ V EM φ ℓ (Bc V c v L) = Pi.single c (ℓ v • wOp EM L φ) := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_apply, smul_add, Pi.single_add]
  | single w r =>
    rw [Bc_single, sθ_single]
    simp [wOp, Finsupp.linearCombination_single, Pi.single_smul, smul_smul, mul_comm]

theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (d : Fin n) :
    tensV E a b f d = E a b (f d) + if d = a then f b else 0 := by
  simp only [tensV, prj, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_proj, Function.eval]
  split_ifs <;> simp

theorem sT_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b) (x : KS (n := n) V) :
    sT E V (sA ε E V hV a b x) = tensV E a b (sT E V x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [sA_single, dif_pos hab, map_add, map_add, sT_Bc, wOp_adLW E hE, sT_single, sT_single]
    clear hE
    by_cases hcb : c = b
    on_goal 1 => subst hcb; rw [if_pos rfl, sT_single]
    on_goal 2 => rw [if_neg hcb, map_zero, add_zero]
    all_goals
      funext d
      simp only [Pi.add_apply, tensV_apply', LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.coe_restrict_apply, Pi.single_apply]
      split_ifs <;> subst_vars <;> simp_all

theorem sθ_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (EM : Fin n → Fin n → Module.End ℂ MM) (hEM : IsGlRep EM) (φ : MM)
    (ν Λ : Fin n → ℝ) (hφ : ∀ a, EM a a φ = ((ν a : ℝ) : ℂ) • φ) (ℓ : V →ₗ[ℂ] ℂ)
    (hℓ : ∀ (a : Fin n) (v w : V), (w : M) = E a a v → ℓ w = ((Λ a : ℝ) : ℂ) * ℓ v) (a : Fin n)
    (x : KS (n := n) V) :
    sθ V EM φ ℓ (sA ε E V hV a a x) =
      tensV EM a a (sθ V EM φ ℓ x) + ((Λ a - ν a : ℝ) : ℂ) • sθ V EM φ ℓ x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]; abel
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [sA_single, dif_pos rfl, map_add, map_add, sθ_Bc, wOp_adLW EM hEM, sθ_single, sθ_single]
    have hl : ℓ ((E a a).restrict (fun v hv => hV a a rfl v hv) v) = ((Λ a : ℝ) : ℂ) * ℓ v :=
      hℓ a v _ rfl
    rw [hl]
    clear hl hℓ hEM
    by_cases hca : c = a
    on_goal 1 => subst hca; rw [if_pos rfl, sθ_single]
    on_goal 2 => rw [if_neg hca, map_zero, add_zero]
    all_goals
      funext d
      simp only [Pi.add_apply, Pi.smul_apply, tensV_apply', LinearMap.sub_apply, Module.End.mul_apply, hφ,
        map_smul, Pi.single_apply]
      split_ifs <;> subst_vars <;> simp_all <;> module

theorem sES_single (w : List (Fin n × Fin n)) (c : Fin n) (v : V) :
    sES V (Finsupp.single (w, c) v) = ∑ d : Fin n, Finsupp.single ((c, d) :: w, d) v := by
  simp [sES, Finsupp.lsum_single, LinearMap.sum_apply]

theorem sES_Bc (c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    sES V (Bc V c v L) = ∑ d : Fin n, Bc V d v (Finsupp.mapDomain ((c, d) :: ·) L) := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Finsupp.mapDomain_add, Finset.sum_add_distrib]
  | single w r => simp only [Bc_single, sES_single, Finsupp.mapDomain_single]

theorem adLW_cons (a b : Fin n) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    adLW a b (p :: w) = Finsupp.mapDomain (· :: w) (adL a b p) + Finsupp.mapDomain (p :: ·) (adLW a b w) := by
  rw [adLW]

theorem mapDomain_neg' {α β : Type*} (f : α → β) (x : α →₀ ℂ) :
    Finsupp.mapDomain f (-x) = -Finsupp.mapDomain f x := by
  simpa [Finsupp.lmapDomain_apply] using (Finsupp.lmapDomain ℂ ℂ f).map_neg x

theorem Bc_adL (a b c d : Fin n) (v : V) (w : List (Fin n × Fin n)) :
    Bc V d v (Finsupp.mapDomain (· :: w) (adL a b (c, d))) =
      (if b = c then Finsupp.single ((a, d) :: w, d) v else 0) -
        (if d = a then Finsupp.single ((c, b) :: w, d) v else 0) := by
  simp only [adL]
  split_ifs <;> simp [Finsupp.mapDomain_sub, mapDomain_neg', Finsupp.mapDomain_single, Bc_single, map_neg]

theorem sA_comm_sES (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (a b : Fin n) (hab : ε a = ε b) : Commute (sA ε E V hV a b) (sES V) := by
  show sA ε E V hV a b * sES V = sES V * sA ε E V hV a b
  apply Finsupp.lhom_ext
  rintro ⟨w, c⟩ v
  simp only [Module.End.mul_apply]
  rw [sES_single, map_sum, sA_single, dif_pos hab, map_add, map_add, sES_Bc, sES_single]
  simp only [sA_single, dif_pos hab, adLW_cons, map_add, Bc_adL, Finset.sum_add_distrib]
  by_cases hcb : c = b
  · subst hcb
    simp [sES_single, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    abel
  · simp [hcb, Ne.symm hcb, Finset.sum_ite_eq']
    abel

def tL (a b : Fin n) : (Fin n × Fin n →₀ ℂ) →ₗ[ℂ] (Fin n × Fin n →₀ ℂ) :=
  Finsupp.linearCombination ℂ (adL a b)

def TW (a b : Fin n) : (List (Fin n × Fin n) →₀ ℂ) →ₗ[ℂ] (List (Fin n × Fin n) →₀ ℂ) :=
  Finsupp.linearCombination ℂ (adLW a b)

def kap : (Fin n × Fin n →₀ ℂ) →ₗ[ℂ] (List (Fin n × Fin n) →₀ ℂ) →ₗ[ℂ] (List (Fin n × Fin n) →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun p => Finsupp.lmapDomain ℂ ℂ (p :: ·))

theorem tL_single (a b : Fin n) (p : Fin n × Fin n) (r : ℂ) :
    tL a b (Finsupp.single p r) = r • adL a b p := by
  simp [tL, Finsupp.linearCombination_single]

theorem TW_single (a b : Fin n) (w : List (Fin n × Fin n)) (r : ℂ) :
    TW a b (Finsupp.single w r) = r • adLW a b w := by
  simp [TW, Finsupp.linearCombination_single]

theorem kap_single_left (p : Fin n × Fin n) (r : ℂ) (L : List (Fin n × Fin n) →₀ ℂ) :
    kap (Finsupp.single p r) L = r • Finsupp.mapDomain (p :: ·) L := by
  simp [kap, Finsupp.linearCombination_single, Finsupp.lmapDomain_apply]

theorem kap_single_right (l : Fin n × Fin n →₀ ℂ) (w : List (Fin n × Fin n)) :
    kap l (Finsupp.single w 1) = Finsupp.mapDomain (· :: w) l := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, Finsupp.mapDomain_add]
  | single q r => simp [kap_single_left, Finsupp.mapDomain_single]

theorem kap_single_single (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (r s : ℂ) :
    kap (Finsupp.single p r) (Finsupp.single w s) = Finsupp.single (p :: w) (r * s) := by
  simp [kap_single_left, Finsupp.mapDomain_single, Finsupp.smul_single]

theorem adLW_cons' (a b : Fin n) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    adLW a b (p :: w) = kap (adL a b p) (Finsupp.single w 1) + kap (Finsupp.single p 1) (adLW a b w) := by
  rw [adLW_cons, kap_single_right, kap_single_left, one_smul]

theorem TW_kap (a b : Fin n) (l : Fin n × Fin n →₀ ℂ) (L : List (Fin n × Fin n) →₀ ℂ) :
    TW a b (kap l L) = kap (tL a b l) L + kap l (TW a b L) := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]; abel
  | single p r =>
    induction L using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; abel
    | single w s =>
      rw [kap_single_single, TW_single, tL_single, TW_single, adLW_cons', map_smul, LinearMap.smul_apply,
        map_smul]
      rw [← Finsupp.smul_single_one p r, ← Finsupp.smul_single_one w s]
      simp only [map_smul, LinearMap.smul_apply, smul_add, smul_smul]
      rw [mul_comm s r]

theorem tL_rel_one (a b c d : Fin n) (p : Fin n × Fin n) :
    tL a b (adL c d p) - tL c d (adL a b p) =
      (if b = c then adL a d p else 0) - (if d = a then adL c b p else 0) := by
  obtain ⟨p1, p2⟩ := p
  simp only [adL, map_sub, apply_ite (tL a b), apply_ite (tL c d), map_zero, tL_single, one_smul]
  split_ifs <;> subst_vars <;> simp_all <;> abel

theorem tL_rel (a b c d : Fin n) (l : Fin n × Fin n →₀ ℂ) :
    tL a b (tL c d l) - tL c d (tL a b l) =
      (if b = c then tL a d l else 0) - (if d = a then tL c b l else 0) := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add]
    have e : ∀ x1 x2 y1 y2 : Fin n × Fin n →₀ ℂ, x1 + y1 - (x2 + y2) = (x1 - x2) + (y1 - y2) := by
      intros; abel
    rw [e, hx, hy]
    split_ifs <;> abel
  | single p r =>
    simp only [tL_single, map_smul]
    rw [← smul_sub, tL_rel_one]
    split_ifs <;> simp [smul_sub]

theorem TW_rel_word (a b c d : Fin n) : ∀ w : List (Fin n × Fin n),
    TW a b (TW c d (Finsupp.single w 1)) - TW c d (TW a b (Finsupp.single w 1)) =
      (if b = c then TW a d (Finsupp.single w 1) else 0) - (if d = a then TW c b (Finsupp.single w 1) else 0)
  | [] => by simp [TW_single, adLW]
  | p :: w => by
    have hw : Finsupp.single (p :: w) (1 : ℂ) = kap (Finsupp.single p 1) (Finsupp.single w 1) := by
      rw [kap_single_single, mul_one]
    have ih := TW_rel_word a b c d w
    have hl := tL_rel a b c d (Finsupp.single p 1)
    rw [hw]
    simp only [TW_kap, map_add]
    have e : ∀ (l : Fin n × Fin n →₀ ℂ) (L : List (Fin n × Fin n) →₀ ℂ),
        kap (tL a b (tL c d l)) L + kap (tL c d l) (TW a b L) +
            (kap (tL a b l) (TW c d L) + kap l (TW a b (TW c d L))) -
          (kap (tL c d (tL a b l)) L + kap (tL a b l) (TW c d L) +
            (kap (tL c d l) (TW a b L) + kap l (TW c d (TW a b L)))) =
        kap (tL a b (tL c d l) - tL c d (tL a b l)) L + kap l (TW a b (TW c d L) - TW c d (TW a b L)) := by
      intro l L
      simp only [map_sub, LinearMap.sub_apply]
      abel
    rw [e, ih, hl]
    split_ifs <;> simp <;> abel


def Dm (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p =>
    ∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.lsingle (R := ℂ) (M := V) (w', p.2)

def eV (a b : Fin n) : Module.End ℂ V :=
  if h : ε a = ε b then (E a b).restrict (fun v hv => hV a b h v hv) else 0

def Fm (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p => Finsupp.lsingle p ∘ₗ eV V ε E hV a b

def Gm (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p => if p.2 = b then Finsupp.lsingle (R := ℂ) (M := V) (p.1, a) else 0

theorem Dm_single (a b : Fin n) (w : List (Fin n × Fin n)) (c : Fin n) (v : V) :
    Dm V a b (Finsupp.single (w, c) v) = Bc V c v (TW a b (Finsupp.single w 1)) := by
  simp only [Dm, Finsupp.lsum_single, sum_eq_Bc, TW_single, one_smul]

theorem Fm_single (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    Fm V ε E hV a b (Finsupp.single p v) = Finsupp.single p (eV V ε E hV a b v) := by
  simp [Fm, Finsupp.lsum_single]

theorem Gm_single (a b : Fin n) (w : List (Fin n × Fin n)) (c : Fin n) (v : V) :
    Gm V a b (Finsupp.single (w, c) v) = if c = b then Finsupp.single (w, a) v else 0 := by
  simp only [Gm, Finsupp.lsum_single]
  split_ifs <;> simp


theorem Dm_Bc (a b c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    Dm V a b (Bc V c v L) = Bc V c v (TW a b L) := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single w r =>
    rw [Bc_single, ← Finsupp.smul_single, map_smul, Dm_single, ← Finsupp.smul_single_one w r, map_smul,
      map_smul]

theorem Fm_Bc (a b c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    Fm V ε E hV a b (Bc V c v L) = Bc V c (eV V ε E hV a b v) L := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | single w r => simp [Bc_single, Fm_single, map_smul]

theorem Gm_Bc (a b c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    Gm V a b (Bc V c v L) = if c = b then Bc V a v L else 0 := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]; split_ifs <;> simp
  | single w r => rw [Bc_single, Gm_single, Bc_single]

theorem sA_eq (a b : Fin n) : sA ε E V hV a b = Dm V a b + Fm V ε E hV a b + Gm V a b := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c⟩ v
  rw [sA_single, LinearMap.add_apply, LinearMap.add_apply, Dm_single, TW_single, one_smul, Fm_single,
    Gm_single]
  congr 2
  simp only [eV]
  split_ifs <;> simp

theorem eV_coe (a b : Fin n) (v : V) :
    (eV V ε E hV a b v : M) = if ε a = ε b then E a b v else 0 := by
  unfold eV
  split_ifs <;> simp [LinearMap.coe_restrict_apply]

theorem eV_rel (hE : IsGlRep E) (a b c d : Fin n) (hab : ε a = ε b) (hcd : ε c = ε d) :
    eV V ε E hV a b * eV V ε E hV c d - eV V ε E hV c d * eV V ε E hV a b =
      (if b = c then eV V ε E hV a d else 0) - (if d = a then eV V ε E hV c b else 0) := by
  have had : b = c → ε a = ε d := fun h => by rw [hab, h]; exact hcd
  have hcb : d = a → ε c = ε b := fun h => by rw [hcd, h]; exact hab
  refine LinearMap.ext fun v => Subtype.ext ?_
  have kv := LinearMap.congr_fun (hE a b c d) (v : M)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at kv
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, eV_coe, if_pos hab, if_pos hcd]
  rw [kv]
  rcases em (b = c) with h1 | h1 <;> rcases em (d = a) with h2 | h2
  · simp [h1, h2, eV_coe, had h1, hcb h2]
  · simp [h1, h2, eV_coe, had h1]
  · simp [h1, h2, eV_coe, hcb h2]
  · simp [h1, h2]

theorem Dm_rel (a b c d : Fin n) :
    Dm V a b * Dm V c d - Dm V c d * Dm V a b =
      (if b = c then Dm V a d else 0) - (if d = a then Dm V c b else 0) := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c0⟩ v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Dm_single, Dm_Bc, ← map_sub, TW_rel_word]
  split_ifs <;> simp [Dm_single]

theorem Fm_rel (hE : IsGlRep E) (a b c d : Fin n) (hab : ε a = ε b) (hcd : ε c = ε d) :
    Fm V ε E hV a b * Fm V ε E hV c d - Fm V ε E hV c d * Fm V ε E hV a b =
      (if b = c then Fm V ε E hV a d else 0) - (if d = a then Fm V ε E hV c b else 0) := by
  apply Finsupp.lhom_ext
  intro p v
  have key := LinearMap.congr_fun (eV_rel V ε E hV hE a b c d hab hcd) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at key
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Fm_single, ← Finsupp.single_sub, key]
  split_ifs <;> simp [Fm_single]

theorem Gm_rel (a b c d : Fin n) :
    Gm V a b * Gm V c d - Gm V c d * Gm V a b =
      (if b = c then Gm V a d else 0) - (if d = a then Gm V c b else 0) := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c0⟩ v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Gm_single]
  by_cases h1 : c0 = d <;> by_cases h2 : c0 = b <;>
    simp only [h1, h2, if_true, if_false, map_zero, Gm_single] <;> (try split_ifs) <;> subst_vars <;>
    (try simp only [Gm_single, map_zero, sub_zero, zero_sub]) <;> (try split_ifs) <;> subst_vars <;> simp_all

theorem Dm_Fm (a b c d : Fin n) : Dm V a b * Fm V ε E hV c d = Fm V ε E hV c d * Dm V a b := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c0⟩ v
  simp only [Module.End.mul_apply, Fm_single, Dm_single, Fm_Bc]

theorem Dm_Gm (a b c d : Fin n) : Dm V a b * Gm V c d = Gm V c d * Dm V a b := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c0⟩ v
  simp only [Module.End.mul_apply, Gm_single, Dm_single, Gm_Bc]
  split_ifs <;> simp [Dm_single]

theorem Fm_Gm (a b c d : Fin n) : Fm V ε E hV a b * Gm V c d = Gm V c d * Fm V ε E hV a b := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c0⟩ v
  simp only [Module.End.mul_apply, Gm_single, Fm_single]
  split_ifs <;> simp [Fm_single]

theorem sA_isKRel (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) : IsKRel ε (sA ε E V hV) := by
  intro a b c d hab hcd
  simp only [sA_eq]
  have e : ∀ D1 F1 G1 D2 F2 G2 : Module.End ℂ (KS (n := n) V),
      (D1 + F1 + G1) * (D2 + F2 + G2) - (D2 + F2 + G2) * (D1 + F1 + G1) =
        (D1 * D2 - D2 * D1) + (F1 * F2 - F2 * F1) + (G1 * G2 - G2 * G1) + (D1 * F2 - F2 * D1) +
          (D1 * G2 - G2 * D1) + (F1 * G2 - G2 * F1) - (D2 * F1 - F1 * D2) - (D2 * G1 - G1 * D2) -
            (F2 * G1 - G1 * F2) := by
    intros; noncomm_ring
  rw [e, Dm_rel, Fm_rel V ε E hV hE a b c d hab hcd, Gm_rel, Dm_Fm, Dm_Gm, Fm_Gm, Dm_Fm, Dm_Gm, Fm_Gm]
  split_ifs <;> abel

end Lift

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {MM : Type*} [AddCommGroup MM] [Module ℂ MM]

theorem sA_isKRel (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) : IsKRel ε (sA ε E V hV) := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sA_isKRel <;> assumption

theorem sA_comm_sES (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (a b : Fin n) (hab : ε a = ε b) : Commute (sA ε E V hV a b) (sES V) := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sA_comm_sES <;> assumption

theorem sθ_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (EM : Fin n → Fin n → Module.End ℂ MM) (hEM : IsGlRep EM) (φ : MM)
    (ν Λ : Fin n → ℝ) (hφ : ∀ a, EM a a φ = ((ν a : ℝ) : ℂ) • φ) (ℓ : V →ₗ[ℂ] ℂ)
    (hℓ : ∀ (a : Fin n) (v w : V), (w : M) = E a a v → ℓ w = ((Λ a : ℝ) : ℂ) * ℓ v) (a : Fin n)
    (x : KS (n := n) V) :
    sθ V EM φ ℓ (sA ε E V hV a a x) =
      tensV EM a a (sθ V EM φ ℓ x) + ((Λ a - ν a : ℝ) : ℂ) • sθ V EM φ ℓ x := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sθ_sA <;> assumption

theorem sT_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b) (x : KS (n := n) V) :
    sT E V (sA ε E V hV a b x) = tensV E a b (sT E V x) := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sT_sA <;> assumption

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem ode_zero {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (A : Module.End ℂ U)
    (G : ℝ → U →ₗ[ℂ] ℂ) (hG : ∀ s y, HasDerivAt (fun s => G s y) (-(G s (A y))) s) (h0 : G 0 = 0)
    (s : ℝ) : G s = 0 := by
  let b := Module.finBasis ℂ U
  let L : (Fin (Module.finrank ℂ U) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ U) → ℂ) :=
    LinearMap.toContinuousLinearMap
      (LinearMap.pi fun i => -∑ j, b.repr (A (b i)) j • LinearMap.proj j)
  have hg : ∀ t, HasDerivAt (fun s i => G s (b i)) (L fun i => G t (b i)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    refine (hG t (b i)).congr_deriv ?_
    have := congrArg (G t) (b.sum_repr (A (b i)))
    simp only [map_sum, map_smul, smul_eq_mul] at this
    simp [L, this]
  have hz := ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => Set.univ) (K := ‖L‖₊)
    (t₀ := 0) (f := fun s i => G s (b i)) (g := fun _ => 0)
    (fun _ => L.lipschitz.lipschitzOnWith) (fun t => ⟨hg t, trivial⟩)
    (fun t => ⟨by simpa using hasDerivAt_const t (0 : Fin (Module.finrank ℂ U) → ℂ), trivial⟩)
    (by funext i; simp [h0])
  exact b.ext fun i => congrFun (congrFun hz s) i

def ei (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (((-s : ℝ) : ℂ) • X)

def cj (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ei X s * Y * NormedSpace.exp ((s : ℂ) • X)

open scoped Matrix.Norms.Operator in
theorem deriv_entries (X Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (a b : Fin n) :
    HasDerivAt (fun s => ei X s a b) (-((ei X s * X) a b)) s ∧
      HasDerivAt (fun s => cj X s Y a b) (-(cj X s (X * Y - Y * X) a b)) s := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) s
  have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) X s
  have e : ∀ s : ℝ, s • (-X) = ((-s : ℝ) : ℂ) • X := fun s => by
    rw [Complex.coe_smul, smul_neg, neg_smul]
  have e' : ∀ s : ℝ, s • X = (s : ℂ) • X := fun s => (Complex.coe_smul s X).symm
  simp only [e] at h1
  simp only [e'] at h2
  let P := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)
  refine ⟨(P.hasFDerivAt.comp_hasDerivAt s h1).congr_deriv ?_,
    (P.hasFDerivAt.comp_hasDerivAt s ((h1.mul_const Y).mul h2)).congr_deriv ?_⟩
  · show (ei X s * -X) a b = _
    rw [Matrix.mul_neg]; rfl
  · show (ei X s * -X * Y * NormedSpace.exp ((s : ℂ) • X) +
      ei X s * Y * (X * NormedSpace.exp ((s : ℂ) • X))) a b = _
    have e2 : ei X s * -X * Y * NormedSpace.exp ((s : ℂ) • X) +
        ei X s * Y * (X * NormedSpace.exp ((s : ℂ) • X)) = -cj X s (X * Y - Y * X) := by
      simp only [cj]; noncomm_ring
    rw [e2]; rfl

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def actL (E : Fin n → Fin n → Module.End ℂ M) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M where
  toFun := actM E
  map_add' X Y := by simp [actM, add_smul, sum_add_distrib]
  map_smul' c X := by simp [actM, smul_sum, smul_smul]

theorem actM_single (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b 1) = E a b := by
  simp [actM, Matrix.single_apply, ite_smul, ite_and]

def wB (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (w : List (Fin n × Fin n)) : M :=
  (w.map fun p => actM E (cj X s (Matrix.single p.1 p.2 1))).prod φ

def adX (X : Matrix (Fin n) (Fin n) ℂ) (w : List (Fin n × Fin n)) : List (Fin n × Fin n) →₀ ℂ :=
  ∑ a, ∑ b, X a b • adLW a b w

theorem lc_adL (a b : Fin n) (p : Fin n × Fin n) :
    Finsupp.linearCombination ℂ (fun q : Fin n × Fin n => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))
      (adL a b p) = Matrix.single a b 1 * Matrix.single p.1 p.2 1 -
        Matrix.single p.1 p.2 1 * Matrix.single a b 1 := by
  rw [adL, map_sub]
  congr 1
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]

theorem lc_adX_cons (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Finsupp.linearCombination ℂ (wB E φ X s) (adX X (p :: w)) =
      actM E (cj X s (X * Matrix.single p.1 p.2 1 - Matrix.single p.1 p.2 1 * X)) (wB E φ X s w) +
        actM E (cj X s (Matrix.single p.1 p.2 1))
          (Finsupp.linearCombination ℂ (wB E φ X s) (adX X w)) := by
  let C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M :=
    { toFun := fun Y => actM E (cj X s Y) (wB E φ X s w)
      map_add' := fun Y Y' => by
        have := (actL E).map_add (cj X s Y) (cj X s Y')
        simp only [cj, Matrix.mul_add, Matrix.add_mul]
        exact congrArg (fun A : Module.End ℂ M => A (wB E φ X s w)) this
      map_smul' := fun c Y => by
        have := (actL E).map_smul c (cj X s Y)
        simp only [cj, Matrix.mul_smul, Matrix.smul_mul]
        exact congrArg (fun A : Module.End ℂ M => A (wB E φ X s w)) this }
  have h1 : ∀ u : (Fin n × Fin n) →₀ ℂ,
      Finsupp.linearCombination ℂ (wB E φ X s) (u.mapDomain (· :: w)) =
        C (Finsupp.linearCombination ℂ
          (fun q : Fin n × Fin n => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ)) u) := fun u => by
    rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]; rfl
  have h2 : ∀ u : List (Fin n × Fin n) →₀ ℂ,
      Finsupp.linearCombination ℂ (wB E φ X s) (u.mapDomain (p :: ·)) =
        actM E (cj X s (Matrix.single p.1 p.2 1)) (Finsupp.linearCombination ℂ (wB E φ X s) u) :=
    fun u => by rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]; rfl
  have h3 : X * Matrix.single p.1 p.2 1 - Matrix.single p.1 p.2 1 * X =
      ∑ a, ∑ b, X a b • ((Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) * Matrix.single p.1 p.2 1 -
        Matrix.single p.1 p.2 1 * Matrix.single a b 1) := by
    have hX : X = ∑ a, ∑ b, X a b • (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp
    conv_lhs => rw [hX]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_sub,
      sum_sub_distrib]
  show _ = C _ + _
  rw [h3]
  simp only [adX, adLW, map_sum, map_smul, map_add, smul_add, sum_add_distrib, h1, h2, lc_adL]

theorem deriv_word (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (w : List (Fin n × Fin n)) : ∀ l : M →ₗ[ℂ] ℂ, HasDerivAt (fun s => l (wB E φ X s w))
      (-(l (Finsupp.linearCombination ℂ (wB E φ X s) (adX X w)))) s := by
  induction w with
  | nil => intro l; simpa [wB, adX, adLW] using hasDerivAt_const s (l φ)
  | cons p w ih =>
    intro l
    have e : (fun s => l (wB E φ X s (p :: w))) = fun s => ∑ a, ∑ b,
        cj X s (Matrix.single p.1 p.2 1) a b * (l ∘ₗ E a b) (wB E φ X s w) := by
      funext s
      simp [wB, actM, map_sum]
    rw [e]
    refine (HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ =>
      ((deriv_entries X (Matrix.single p.1 p.2 1) s a b).2.mul (ih (l ∘ₗ E a b)))).congr_deriv ?_
    rw [lc_adX_cons]
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_add, map_sum, map_smul,
      smul_eq_mul, LinearMap.comp_apply, neg_add, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

theorem adLW_length (a b : Fin n) : ∀ (w w' : List (Fin n × Fin n)), w' ∈ (adLW a b w).support →
    w'.length = w.length := by
  classical
  intro w
  induction w with
  | nil => intro w' h; simp [adLW] at h
  | cons p w ih =>
    intro w' h
    rcases mem_union.mp (Finsupp.support_add h) with h | h
    · obtain ⟨q, -, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support h); rfl
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support h)
      simp [ih q hq]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
end
end

section
noncomputable section

open Finset Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Coef

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem coef_deriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) (u : H) (m : D) :
    HasDerivAt (fun t : ℝ => ⟪u, σ (g * NormedSpace.exp ((t : ℂ) • X)) (m : H)⟫_ℂ)
      ⟪u, σ g ((actM E X m : D) : H)⟫_ℂ 0 := by
  have h := (((innerSL ℂ u).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hD.deriv X hX m)
  refine HasDerivAt.congr_of_eventuallyEq h (Eventually.of_forall fun t => ?_)
  simp only [hσ.1.2 _ hg _ (exp_smul_mem_UJset hX t)]
  rfl

theorem act_cpart (E : Fin n → Fin n → Module.End ℂ D) (Z : Matrix (Fin n) (Fin n) ℂ) (m : D) :
    actM E Z m = actM E (cpart1 ε Z) m + Complex.I • actM E (cpart2 ε Z) m := by
  have h : actL E Z = actL E (cpart1 ε Z) + Complex.I • actL E (cpart2 ε Z) := by
    rw [← map_smul, ← map_add, ta_cpart_sum]
  exact congrArg (fun A : Module.End ℂ D => A m) h

theorem eq_zero_of_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    {y : D} (hy : y ∈ genSub E V)
    (h : ∀ g ∈ UJset ε, ∀ v' : V, ⟪((v' : D) : H), σ g (y : H)⟫_ℂ = 0) : y = 0 := by
  let N : Set D := {m | ∀ g ∈ UJset ε, ∀ v' : V, ⟪((v' : D) : H), σ g (m : H)⟫_ℂ = 0}
  have hNr : ∀ X, inG ε X → ∀ m ∈ N, actM E X m ∈ N := fun X hX m hm g hg v' => by
    refine (coef_deriv hσ hD hg hX _ m).unique ?_
    have : (fun t : ℝ => ⟪((v' : D) : H), σ (g * NormedSpace.exp ((t : ℂ) • X)) (m : H)⟫_ℂ) =
        fun _ => 0 := funext fun t => hm _ (ta_inUJ_mul_exp ε hg hX t) v'
    rw [this]; exact hasDerivAt_const _ _
  have hN : ∀ a b, ∀ m ∈ N, E a b m ∈ N := fun a b m hm g hg v' => by
    rw [← actM_single E a b, act_cpart (ε := ε), Submodule.coe_add, Submodule.coe_smul, map_add,
      map_smul, inner_add_right, inner_smul_right, hNr _ (ta_inG_cpart1 ε _) m hm g hg v',
      hNr _ (ta_inG_cpart2 ε _) m hm g hg v']
    simp
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  let P : Submodule ℂ D :=
    { carrier := {u | ∀ m ∈ N, ⟪u, m⟫_ℂ = 0}
      add_mem' := fun hu hu' m hm => by rw [inner_add_left, hu m hm, hu' m hm, add_zero]
      zero_mem' := fun m _ => inner_zero_left m
      smul_mem' := fun c u hu m hm => by rw [inner_smul_left, hu m hm, mul_zero] }
  have h1J : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have hle : genSub E V ≤ P := sInf_le ⟨fun v hv m hm => by
      have := hm 1 h1J ⟨v, hv⟩
      rw [hσ.1.1] at this
      exact this,
    fun a b u hu m hm => by rw [hU a b, hu _ (hN b a m hm), mul_zero]⟩
  exact inner_self_eq_zero.mp (hle hy y h)

theorem inner_deriv {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (f : ℝ → (U →L[ℂ] U)) (φ : U → U → ℂ)
    (h : ∀ a b, HasDerivAt (fun t => ⟪a, f t b⟫_ℂ) (φ a b) 0) (a b : U) :
    ⟪a, deriv f 0 b⟫_ℂ = φ a b := by
  let e := stdOrthonormalBasis ℂ U
  have hf : f = fun t => ∑ i, ∑ j, ⟪e i, f t (e j)⟫_ℂ • (innerSL ℂ (e j)).smulRight (e i) := by
    funext t
    ext x
    conv_lhs => rw [← e.sum_repr' (f t x), ← e.sum_repr' x]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right, sum_smul,
      _root_.sum_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [mul_comm]
  have hd : DifferentiableAt ℝ f 0 := by
    rw [hf]
    exact DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ =>
      (h _ _).differentiableAt.smul_const _
  have h2 := (((innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ U b)).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  exact h2.unique (h a b)

theorem rWord_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (ι : V ≃ₗ[ℂ] U) (Ψ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U))
    (hco : ∀ g, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', Ψ g (ι v)⟫_ℂ)
    (L : List (Matrix (Fin n) (Fin n) ℂ)) : ∀ g, inUJ ε g → ∀ v v' : V,
      ⟪ι v', rWord ε L Ψ g (ι v)⟫_ℂ =
        ⟪((v' : D) : H), σ g (((L.map (actM E)).prod (v : D) : D) : H)⟫_ℂ := by
  induction L with
  | nil => intro g hg v v'; exact (hco g hg v v').symm
  | cons Z L ih =>
    intro g hg v v'
    have hR : ∀ X, inG ε X → ⟪ι v', RdV X (rWord ε L Ψ) g (ι v)⟫_ℂ =
        ⟪((v' : D) : H), σ g ((actM E X ((L.map (actM E)).prod (v : D)) : D) : H)⟫_ℂ := by
      intro X hX
      have := inner_deriv (fun t : ℝ => rWord ε L Ψ (g * NormedSpace.exp ((t : ℂ) • X)))
        (fun a b => ⟪((ι.symm a : D) : H),
          σ g ((actM E X ((L.map (actM E)).prod (ι.symm b : D)) : D) : H)⟫_ℂ)
        (fun a b => by
          refine (coef_deriv hσ hD hg hX _ _).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
          have := ih _ (ta_inUJ_mul_exp ε hg hX t) (ι.symm b) (ι.symm a)
          rwa [ι.apply_symm_apply, ι.apply_symm_apply] at this) (ι v') (ι v)
      rwa [ι.symm_apply_apply, ι.symm_apply_apply] at this
    show ⟪ι v', (RdV (cpart1 ε Z) (rWord ε L Ψ) g + Complex.I • RdV (cpart2 ε Z) (rWord ε L Ψ) g) (ι v)⟫_ℂ = _
    rw [_root_.add_apply, _root_.smul_apply, inner_add_right,
      inner_smul_right, hR _ (ta_inG_cpart1 ε Z), hR _ (ta_inG_cpart2 ε Z), List.map_cons,
      List.prod_cons, Module.End.mul_apply, act_cpart (ε := ε) E Z, Submodule.coe_add,
      Submodule.coe_smul, map_add, map_smul, inner_add_right, inner_smul_right]

end Coef

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem omegaP_mem_nhds {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ OmegaP n) : OmegaP n ∈ 𝓝 x :=
  (tb_inv_hasFDerivAt (tb_isUnit_of_omegaP hx)).choose_spec.1.continuousAt.preimage_mem_nhds
    (isOpen_omega.mem_nhds hx)

def evZ (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) : MMT μ →ₗ[ℂ] ℂ :=
  (LinearMap.proj z : (Matrix (Fin n) (Fin n) ℂ → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (cOm n).subtype ∘ₗ (mmSub μ).subtype

theorem evZ_word (μ : Fin n → ℤ) (L : List (Matrix (Fin n) (Fin n) ℂ)) : ∀ z ∈ OmegaP n,
    evZ μ z ((L.map (actM (eMM μ))).prod (phiMM μ)) = hWord L (PhiP μ) z := by
  induction L with
  | nil => intro z hz; exact Set.indicator_of_mem hz _
  | cons Z L ih =>
    intro z hz
    set F := (L.map (actM (eMM μ))).prod (phiMM μ) with hF
    have h1 : ∀ a b, evZ μ z (eMM μ a b F) =
        fderiv ℂ (hWord L (PhiP μ)) z (z * Matrix.single a b 1) := fun a b => by
      have e : ((F : cOm n) : Matrix (Fin n) (Fin n) ℂ → ℂ) =ᶠ[𝓝 z] hWord L (PhiP μ) :=
        eventually_of_mem (omegaP_mem_nhds hz) ih
      rw [← e.fderiv_eq]
      exact Set.indicator_of_mem hz _
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ← hF]
    show _ = fderiv ℂ (hWord L (PhiP μ)) z (z * Z)
    have hZ : z * Z = ∑ a, ∑ b, Z a b • (z * (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ)) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp only [Matrix.mul_sum, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hZ]
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h1]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
end
end

section
noncomputable section

open Finset Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D} {M : Type*} [AddCommGroup M] [Module ℂ M]

def aF (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ D) (w0 : H)
    (g : Matrix (Fin n) (Fin n) ℂ) : V →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ w0) ∘ₗ (σ g : H →ₗ[ℂ] H) ∘ₗ D.subtype ∘ₗ V.subtype

def Xi (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ D) (w0 : H)
    (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ) (c' : Fin n)
    (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : KS (n := n) V →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun p => (ei X s c' p.2 * l (wB EM φ X s p.1)) • aF σ V w0 (ei X s)

theorem Xi_single (w0 : H) (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ) (c' : Fin n)
    (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    Xi σ V w0 EM φ l c' X s (Finsupp.single p v) =
      ei X s c' p.2 * l (wB EM φ X s p.1) * aF σ V w0 (ei X s) v := by
  simp [Xi]

theorem sA_single (hV : IsKStableSub ε E V) (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    sA ε E V hV a b (Finsupp.single p v) =
      (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) +
      (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) +
      (if p.2 = b then Finsupp.single (p.1, a) v else 0) := by
  simp only [sA, Finsupp.lsum_single, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lsingle_apply]
  congr 1
  · congr 1
    split_ifs <;> rfl
  · split_ifs <;> rfl

theorem deriv_aF (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (w0 : H)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s : ℝ) (v : V) :
    HasDerivAt (fun s => aF σ V w0 (ei X s) v)
      (-⟪w0, σ (ei X s) ((actM E X (v : D) : D) : H)⟫_ℂ) s := by
  have h := coef_deriv hσ hD (exp_smul_mem_UJset hX (-s)) hX w0 (v : D)
  rw [← sub_self s] at h
  have h2 := h.scomp s ((hasDerivAt_id s).const_sub s)
  refine HasDerivAt.congr_deriv (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)) ?_
  · show ⟪w0, σ (ei X t) _⟫_ℂ = ⟪w0, σ (_ * NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) _⟫_ℂ
    rw [← exp_add_smul, show -s + (s - t) = -t by ring]; rfl
  · simp [ei]

theorem deriv_Xi (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKStableSub ε E V)
    (w0 : H) (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ) (c' : Fin n)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (s : ℝ) (y : KS (n := n) V) :
    HasDerivAt (fun s => Xi σ V w0 EM φ l c' X s y)
      (-(Xi σ V w0 EM φ l c' X s ((∑ a, ∑ b, X a b • sA ε E V hV a b) y))) s := by
  induction y using Finsupp.induction_linear with
  | zero => simpa using hasDerivAt_const s (0 : ℂ)
  | add y y' h h' =>
    simp only [map_add, neg_add]
    exact h.add h'
  | single p v =>
    simp only [Xi_single]
    refine ((((deriv_entries X 0 s c' p.2).1.mul (deriv_word EM φ X s p.1 l))).mul
      (deriv_aF hσ hD w0 hX.1 s v)).congr_deriv ?_
    set A := aF σ V w0 (ei X s) with hA
    set B := l (wB EM φ X s p.1) with hB
    have t1 : ∀ a b, Xi σ V w0 EM φ l c' X s
        (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) =
        ei X s c' p.2 * l (Finsupp.linearCombination ℂ (wB EM φ X s) (adLW a b p.1)) * A v := by
      intro a b
      simp only [map_sum, map_smul, Xi_single, Finsupp.linearCombination_apply, Finsupp.sum,
        smul_eq_mul, mul_sum, sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    have t2 : ∀ a b, X a b * Xi σ V w0 EM φ l c' X s
        (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) =
        ei X s c' p.2 * B * (X a b * ⟪w0, σ (ei X s) ((E a b (v : D) : D) : H)⟫_ℂ) := by
      intro a b
      split_ifs with h
      · rw [Xi_single]
        show _ * (_ * ⟪w0, σ (ei X s) ((E a b (v : D) : D) : H)⟫_ℂ) = _
        ring
      · simp [inK_apply_eq_zero hX h]
    have t3 : ∀ a b, Xi σ V w0 EM φ l c' X s (if p.2 = b then Finsupp.single (p.1, a) v else 0) =
        if p.2 = b then ei X s c' a * B * A v else 0 := by
      intro a b
      split_ifs
      · rw [Xi_single]
      · exact map_zero _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sA_single, map_add,
      smul_eq_mul, mul_add, sum_add_distrib, t1, t2, t3, mul_ite, mul_zero, sum_ite_eq, mem_univ,
      if_true, adX, actM, Submodule.coe_sum, Submodule.coe_smul, inner_sum, inner_smul_right,
      Matrix.mul_apply, Pi.mul_apply, ← mul_sum, ← hB]
    have u1 : ∑ a, ∑ b, X a b * (ei X s c' p.2 *
        l (Finsupp.linearCombination ℂ (wB EM φ X s) (adLW a b p.1)) * A v) =
        ei X s c' p.2 * (∑ a, ∑ b, X a b *
          l (Finsupp.linearCombination ℂ (wB EM φ X s) (adLW a b p.1))) * A v := by
      simp only [mul_sum, sum_mul]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    have u3 : ∑ a, X a p.2 * (ei X s c' a * B * A v) = (∑ a, ei X s c' a * X a p.2) * B * A v := by
      simp only [sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    rw [u1, u3]
    ring

theorem Xi_vanish (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) [FiniteDimensional ℂ V]
    (hV : IsKStableSub ε E V) (w0 : H) (EM : Fin n → Fin n → Module.End ℂ M) (φ : M) (l : M →ₗ[ℂ] ℂ)
    (c' : Fin n) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (W : Submodule ℂ (KS (n := n) V))
    (hW : IsKStableSub ε (sA ε E V hV) W) (h0 : ∀ y ∈ W, Xi σ V w0 EM φ l c' X 0 y = 0) (s : ℝ) :
    ∀ y ∈ W, Xi σ V w0 EM φ l c' X s y = 0 := by
  intro x hx
  set R := x.support.sup fun p => p.1.length with hR
  let S : Set (List (Fin n × Fin n) × Fin n) := {p | p.1.length ≤ R}
  have hSf : S.Finite := ((List.finite_length_le (Fin n × Fin n) R).prod Set.finite_univ).subset
    fun p hp => ⟨hp, trivial⟩
  have := hSf.to_subtype
  have : FiniteDimensional ℂ (Finsupp.supported V ℂ S) :=
    Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := V) (R := ℂ) S).symm
  have : FiniteDimensional ℂ (W ⊓ Finsupp.supported V ℂ S : Submodule ℂ _) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hS : ∀ a b, ∀ y ∈ Finsupp.supported V ℂ S, sA ε E V hV a b y ∈ Finsupp.supported V ℂ S := by
    intro a b y hy
    rw [← Finsupp.sum_single y, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun p hp => ?_
    have hpS : p.1.length ≤ R := hy hp
    rw [sA_single]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun w' hw' =>
      Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ _ ?_)) ?_) ?_
    · show w'.length ≤ R
      rw [adLW_length a b _ _ hw']; exact hpS
    · split_ifs
      · exact Finsupp.single_mem_supported ℂ _ hpS
      · exact Submodule.zero_mem _
    · split_ifs
      · exact Finsupp.single_mem_supported ℂ _ hpS
      · exact Submodule.zero_mem _
  have hA : ∀ y ∈ W ⊓ Finsupp.supported V ℂ S,
      (∑ a, ∑ b, X a b • sA ε E V hV a b) y ∈ W ⊓ Finsupp.supported V ℂ S := by
    intro y hy
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    by_cases h : ε a = ε b
    · exact Submodule.smul_mem _ _ ⟨hW a b h y hy.1, hS a b y hy.2⟩
    · rw [inK_apply_eq_zero hX h, zero_smul]; exact Submodule.zero_mem _
  have key := ode_zero ((∑ a, ∑ b, X a b • sA ε E V hV a b).restrict hA)
    (fun s => Xi σ V w0 EM φ l c' X s ∘ₗ (W ⊓ Finsupp.supported V ℂ S).subtype)
    (fun s y => deriv_Xi hσ hD hV w0 EM φ l c' hX s y) (LinearMap.ext fun y => h0 y y.2.1) s
  exact LinearMap.congr_fun key
    ⟨x, hx, fun p hp => Finset.le_sup (f := fun p : List (Fin n × Fin n) × Fin n => p.1.length) hp⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
end
end

section
noncomputable section

open Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def submoduleEvaluationFunctional {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H} (V : Submodule ℂ D)
    (w0 : V) : V →ₗ[ℂ] ℂ where
  toFun v := ⟪((w0 : D) : H), ((v : D) : H)⟫_ℂ
  map_add' x y := by simp [inner_add_right]
  map_smul' c x := by simp [inner_smul_right]

theorem lowestKType_vector_exists (ε : Fin n → Bool) (lam : Fin n → ℝ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (T : KType ε (lowK ε lam)) (ι : V ≃ₗ[ℂ] T.V)
    (hιK : ∀ (k : KG ε) (v w : V), ((w : D) : H) = σ (toMK k) ((v : D) : H) → ι w = T.op k (ι v)) :
    IsKHWVec ε E (lowK ε lam) ((ι.symm T.w : V) : D) := by
  have := hV.1
  have hVK : ∀ (k : KG ε) (v : V), ∃ w : V, ((w : D) : H) = σ (toMK k) ((v : D) : H) := by
    intro k v
    obtain ⟨Z, hZ, he⟩ := HW.exists_log ε k
    have hs := KTypeIsomorphism.orbit_hasSum hσ hD hV.1 hV.2.1 hZ v
    let P : Submodule ℂ H := LinearMap.range (D.subtype ∘ₗ V.subtype)
    have hmem : σ (NormedSpace.exp Z) ((v : D) : H) ∈ P :=
      P.closed_of_finiteDimensional.mem_of_tendsto hs (Filter.Eventually.of_forall fun t =>
        P.sum_mem fun m _ => P.smul_mem _ ⟨_, rfl⟩)
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, by rw [he]; exact hw⟩
  let L : T.V →L[ℂ] H := LinearMap.toContinuousLinearMap (D.subtype ∘ₗ V.subtype ∘ₗ ι.symm.toLinearMap)
  have hK : ∀ X, inK ε X → ((actM E X ((ι.symm T.w : V) : D) : D) : H) = L (T.dτ X T.w) := by
    intro X hX
    obtain ⟨γ, hγ⟩ := HW.exists_curve ε hX
    have h1 := ((L.comp (ContinuousLinearMap.apply ℂ T.V T.w)).restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (T.hasDeriv X hX γ hγ)
    refine (hD.deriv X hX.1 _).unique (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
    obtain ⟨w, hw⟩ := hVK (γ t) (ι.symm T.w)
    have h2 := hιK (γ t) _ w hw
    rw [ι.apply_symm_apply] at h2
    show σ _ _ = ((ι.symm (T.op (γ t) T.w) : D) : H)
    rw [← h2, ι.symm_apply_apply, hw, hγ]
  have hC : ∀ a b, ε a = ε b →
      ((E a b ((ι.symm T.w : V) : D) : D) : H) = L (T.dτ (Matrix.single a b 1) T.w) := by
    intro a b hab
    have hZ : (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
      ext i j
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
      split_ifs with h <;> simp_all
    have hJ : Jm ε * Jm ε = 1 := by
      rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp
    have hJh : (Jm ε).conjTranspose = Jm ε := by
      rw [Jm, Matrix.diagonal_conjTranspose]; congr 1; funext i
      simp only [Pi.star_apply]; split_ifs <;> simp
    have hZ' : Jm ε * (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * Jm ε =
        Jm ε * (Jm ε * (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε) := by
      have := congrArg Matrix.conjTranspose hZ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh] at this
      rw [Matrix.mul_assoc _ (Jm ε) (Jm ε), hJ, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        hJ, Matrix.one_mul, this]
    have k1 : inK ε (cpart1 ε (Matrix.single a b 1)) := ⟨ta_inG_cpart1 ε _, by
      simp only [cpart1, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, hZ, hZ']⟩
    have k2 : inK ε (cpart2 ε (Matrix.single a b 1)) := ⟨ta_inG_cpart2 ε _, by
      simp only [cpart2, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, hZ, hZ']⟩
    rw [← TRA.actM_single E a b, TRA.act_cpart (ε := ε), Submodule.coe_add, Submodule.coe_smul,
      hK _ k1, hK _ k2]
    conv_rhs => rw [← ta_cpart_sum ε (Matrix.single a b 1), map_add, map_smul, _root_.add_apply,
      _root_.smul_apply, map_add, map_smul]
  refine ⟨fun a => Subtype.ext ?_, fun a b hab he => Subtype.ext ?_⟩
  · rw [hC a a rfl, T.w_wt a, map_smul]; rfl
  · rw [hC a b he, T.w_hw a b hab he, map_zero]; rfl

theorem lowestKType_trace_integral (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hanti : StrictAnti lam)
    (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (ι : V ≃ₗ[ℂ] T.V) (hμ : IsMu lam μ)
    (hcoef : ∀ g : Matrix (Fin n) (Fin n) ℂ, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', PsiM T μ g (ι v)⟫_ℂ)
    (W : Submodule ℂ (KS (n := n) V)) (hW : IsKStableSub ε (sA ε E V hV.2.1) W)
    (hθ : ∀ x ∈ W, sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) x = 0) :
    ∀ x ∈ W, sT E V x = 0 := by
  have := hV.1
  intro x hx
  funext c
  set w0 : H := (((ι.symm T.w : V) : D) : H) with hw0
  have hsT : sT E V x c = ∑ p ∈ x.support, if p.2 = c then wordE E p.1 (x p : D) else 0 := by
    conv_lhs => rw [← Finsupp.sum_single x, Finsupp.sum, map_sum, Finset.sum_apply]
    refine sum_congr rfl fun p _ => ?_
    rw [show p = (p.1, p.2) from rfl, sT_single, Pi.single_apply]
    simp only [eq_comm]
  have hword : ∀ w : List (Fin n × Fin n),
      ((w.map fun p => (Matrix.single p.1 p.2 1 : Matrix (Fin n) (Fin n) ℂ)).map (actM E)).prod =
        wordE E w := fun w => by
    rw [List.map_map, wordE]; congr 2; funext p; exact TRA.actM_single E p.1 p.2
  have h1J : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
    show (1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * 1 = Jm ε
    simp
  refine TRA.eq_zero_of_coef hσ hD (V := V) ?_ fun g hg v' => ?_
  · rw [hsT]
    refine Submodule.sum_mem _ fun p _ => ?_
    split_ifs
    · generalize p.1 = w
      induction w with
      | nil => exact Submodule.mem_sInf.mpr fun S hS => hS.1 (x p).2
      | cons q w ih => exact Submodule.mem_sInf.mpr fun S hS => hS.2 _ _ _ (Submodule.mem_sInf.mp ih S hS)
    · exact Submodule.zero_mem _
  let e := x.support.equivFin
  have hsum : ∀ F : List (Fin n × Fin n) × Fin n → ℂ, ∑ i, F (e.symm i) = ∑ p ∈ x.support, F p :=
    fun F => by rw [Equiv.sum_comp e.symm (fun p : x.support => F p), Finset.sum_coe_sort]
  have key := transfer n ε lam T μ ⟨hanti, hint⟩ hμ _
    (fun i => (e.symm i).1.1.map fun p => (Matrix.single p.1 p.2 1 : Matrix (Fin n) (Fin n) ℂ))
    (fun i => if (e.symm i).1.2 = c then ι (x (e.symm i)) else 0) ?_ g hg
  · have h2 := congrArg (fun u => ⟪ι v', u⟫_ℂ) key
    simp only [inner_sum, inner_zero_right] at h2
    rw [hsum fun p => ⟪ι v', rWord ε (p.1.map fun q =>
      (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ)) (PsiM T μ) g
        (if p.2 = c then ι (x p) else 0)⟫_ℂ] at h2
    rw [hsT, ← h2, Submodule.coe_sum, map_sum, inner_sum]
    refine sum_congr rfl fun p _ => ?_
    split_ifs
    · rw [TRA.rWord_coef hσ hD ι _ hcoef _ g hg, hword]
    · simp
  intro k z hz
  obtain ⟨X, hX, he⟩ := HW.exists_log ε k
  have he1 : NormedSpace.exp (((1 : ℝ) : ℂ) • X) = toMK k := by rw [he]; simp
  have hinv : toMK k * TRA.ei X 1 = 1 := by
    rw [← he1, TRA.ei, ← exp_add_smul]; simp
  have hki : toMK k⁻¹ = TRA.ei X 1 := by
    rw [← Matrix.mul_one (toMK k⁻¹), ← hinv, ← Matrix.mul_assoc, toMK_inv_mul', Matrix.one_mul]
  have hXi : ∀ c', TRA.Xi σ V w0 (eMM μ) (phiMM μ) (TRA.evZ μ z) c' X 1 x = 0 := fun c' =>
    TRA.Xi_vanish hσ hD hV.2.1 w0 _ _ _ c' hX W hW (fun y hy => by
      have h0 : ∀ y, TRA.Xi σ V w0 (eMM μ) (phiMM μ) (TRA.evZ μ z) c' X 0 y =
          TRA.evZ μ z (sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) y c') := by
        intro y
        induction y using Finsupp.induction_linear with
        | zero => simp
        | add y y' h h' => simp only [map_add, Pi.add_apply, h, h']
        | single p v =>
          have e0 : TRA.ei X 0 = 1 := by simp [TRA.ei]
          have e1 : TRA.wB (eMM μ) (phiMM μ) X 0 p.1 = wordE (eMM μ) p.1 (phiMM μ) := by
            simp [TRA.wB, TRA.cj, e0, TRA.actM_single, wordE]
          have e2 : TRA.aF σ V w0 1 v = submoduleEvaluationFunctional V (ι.symm T.w) v := by
            show ⟪w0, σ 1 _⟫_ℂ = _
            rw [hσ.1.1]; rfl
          rw [TRA.Xi_single, e0, e1, e2, show p = (p.1, p.2) from rfl, sθ_single, Pi.single_apply,
            Matrix.one_apply]
          split_ifs <;> simp [mul_comm]
      rw [h0, hθ y hy, Pi.zero_apply, map_zero]) 1 x hx
  let a : List (Fin n × Fin n) × Fin n → ℂ := fun p => ⟪T.op k T.w, ι (x p)⟫_ℂ *
    hWord (adW ε k (p.1.map fun q => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))) (PhiP μ) z
  have hXa : ∀ c', ∑ p ∈ x.support, TRA.ei X 1 c' p.2 * a p = 0 := fun c' => by
    rw [← hXi c']
    conv_rhs => rw [← Finsupp.sum_single x, Finsupp.sum, map_sum]
    refine sum_congr rfl fun p _ => ?_
    have e1 : TRA.evZ μ z (TRA.wB (eMM μ) (phiMM μ) X 1 p.1) = hWord (adW ε k (p.1.map fun q =>
        (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))) (PhiP μ) z := by
      rw [← TRA.evZ_word μ _ z hz, adW, List.map_map, List.map_map, hki, ← he1]; rfl
    have e2 : TRA.aF σ V w0 (TRA.ei X 1) (x p) = ⟪T.op k T.w, ι (x p)⟫_ℂ := by
      have hP : PsiM T μ (toMK k⁻¹) = T.op k⁻¹ := by
        have := psiM_equiv T μ k⁻¹ 1 h1J
        rwa [toMK_one', Matrix.mul_one, Matrix.mul_one, psiM_one, op_one', mul_one, mul_one] at this
      have h3 := hcoef (toMK k⁻¹) (k⁻¹).1.2 (x p) (ι.symm T.w)
      rw [ι.apply_symm_apply, hP] at h3
      rw [← hki]
      refine h3.trans ?_
      have hu : star (T.op k) * T.op k = 1 := Unitary.star_mul_self_of_mem (T.τ k).2
      have h4 : T.op k⁻¹ = star (T.op k) := by
        rw [← one_mul (T.op k⁻¹), ← hu, mul_assoc, ← op_mul', mul_inv_cancel, op_one', mul_one]
      rw [h4, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    rw [TRA.Xi_single, e1, e2]
    simp only [a]; ring
  rw [hsum fun p => ⟪T.op k T.w, if p.2 = c then ι (x p) else 0⟫_ℂ *
    hWord (adW ε k (p.1.map fun q => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))) (PhiP μ) z]
  calc _ = ∑ p ∈ x.support, (toMK k * TRA.ei X 1) c p.2 * a p := sum_congr rfl fun p _ => by
        rw [hinv, Matrix.one_apply]
        by_cases h : p.2 = c
        · simp [h, a]
        · simp [h, Ne.symm h]
    _ = ∑ c', toMK k c c' * ∑ p ∈ x.support, TRA.ei X 1 c' p.2 * a p := by
        simp only [Matrix.mul_apply, sum_mul, mul_sum, mul_assoc]
        exact sum_comm
    _ = 0 := by simp [hXa]

theorem lowestKType_trace (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hanti : StrictAnti lam)
    (hgap : GapLap ε lam h) (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε)
    (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (ι : V ≃ₗ[ℂ] T.V) (hμ : IsMu lam μ)
    (hιK : ∀ (k : KG ε) (v w : V), ((w : D) : H) = σ (toMK k) ((v : D) : H) → ι w = T.op k (ι v))
    (hcoef : ∀ g : Matrix (Fin n) (Fin n) ℂ, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', PsiM T μ g (ι v)⟫_ℂ)
    (W : Submodule ℂ (KS (n := n) V)) (hW : IsKStableSub ε (sA ε E V hV.2.1) W)
    (hθ : ∀ x ∈ W, sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) x = 0) :
    ∀ x ∈ W, sT E V x = 0 := by
  exact lowestKType_trace_integral ε lam H σ D E V hσ hD hV hint hanti T μ ι hμ hcoef W hW hθ

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.Cone

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {MM : Type*} [AddCommGroup MM] [Module ℂ MM]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

def sC (V : Submodule ℂ M) (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p => if p.2 = b then Finsupp.lsingle (p.1, a) else 0

theorem sC_single (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    sC V a b (Finsupp.single p v) = if p.2 = b then Finsupp.single (p.1, a) v else 0 := by
  simp only [sC, Finsupp.lsum_single]; split_ifs <;> rfl

def compactWordAction (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  sA ε E V hV a b - sC V a b

theorem compactWordAction_single (hV : IsKStableSub ε E V) (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    compactWordAction ε E V hV a b (Finsupp.single p v) =
      (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.single (w', p.2) v) +
      (if h : ε a = ε b then Finsupp.single p ⟨E a b v, hV a b h v v.2⟩ else 0) := by
  rw [compactWordAction, LinearMap.sub_apply, sC_single, sub_eq_iff_eq_add]
  simp only [sA, Finsupp.lsum_single, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lsingle_apply]
  congr 1
  · congr 1
    split_ifs <;> rfl
  · split_ifs <;> rfl

theorem sC_mul (a b c d : Fin n) : sC V a b * sC V c d = if b = c then sC V a d else 0 := by
  refine Finsupp.lhom_ext fun p v => ?_
  rw [Module.End.mul_apply, sC_single]
  by_cases h1 : p.2 = d <;> by_cases h2 : b = c <;> simp [h1, h2, sC_single, eq_comm]

theorem compactWordAction_commute (hV : IsKStableSub ε E V) (a b c d : Fin n) :
    compactWordAction ε E V hV a b * sC V c d = sC V c d * compactWordAction ε E V hV a b := by
  refine Finsupp.lhom_ext fun p v => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, sC_single, compactWordAction_single, map_add, map_sum]
  by_cases h1 : p.2 = d <;> by_cases h : ε a = ε b <;>
    simp only [h1, h, if_true, if_false, dif_pos, dif_neg, not_false_eq_true, compactWordAction_single, map_smul,
      sC_single, map_zero, smul_zero, sum_const_zero, add_zero]

theorem isKRelation_compactWordAction (hV : IsKStableSub ε E V) (hE : IsGlRep E) : IsKRel ε (compactWordAction ε E V hV) := by
  intro a b c d hab hcd
  have h1 := sA_isKRel ε E V hV hE a b c d hab hcd
  have e : ∀ x y, sA ε E V hV x y = compactWordAction ε E V hV x y + sC V x y := fun x y => by simp [compactWordAction]
  rw [e a b, e c d, e a d, e c b] at h1
  simp only [add_mul, mul_add, sC_mul, compactWordAction_commute] at h1
  have h2 : compactWordAction ε E V hV a b * compactWordAction ε E V hV c d - compactWordAction ε E V hV c d * compactWordAction ε E V hV a b =
      ((if b = c then compactWordAction ε E V hV a d + sC V a d else 0) -
        if d = a then compactWordAction ε E V hV c b + sC V c b else 0) -
      ((if b = c then sC V a d else 0) - if d = a then sC V c b else 0) := by
    rw [← h1]; abel
  rw [h2]
  split_ifs <;> abel

theorem sT_sC (a b : Fin n) (x : KS (n := n) V) :
    sT E V (sC V a b x) = Pi.single a (sT E V x b) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y h h' => simp only [map_add, h, h', Pi.add_apply, Pi.single_add]
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [sC_single, sT_single]
    by_cases h : c = b
    · subst h; simp [sT_single]
    · simp [h, Ne.symm h]

theorem sθ_sC (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM) (ℓ : V →ₗ[ℂ] ℂ) (a b : Fin n)
    (x : KS (n := n) V) : sθ V EM φ ℓ (sC V a b x) = Pi.single a (sθ V EM φ ℓ x b) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y h h' => simp only [map_add, h, h', Pi.add_apply, Pi.single_add]
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [sC_single, sθ_single]
    by_cases h : c = b
    · subst h; simp [sθ_single]
    · simp [h, Ne.symm h]

theorem tensV_eq (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (Pi.single a (f b) : Fin n → M) c := by
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply, Pi.single_apply]
  split_ifs <;> rfl

theorem contraction_compactWordAction (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b)
    (x : KS (n := n) V) (c : Fin n) : sT E V (compactWordAction ε E V hV a b x) c = E a b (sT E V x c) := by
  rw [compactWordAction, LinearMap.sub_apply, map_sub, sT_sA ε E V hV hE a b hab, sT_sC, Pi.sub_apply, tensV_eq,
    add_sub_cancel_right]

theorem exists_stable (hV : IsKStableSub ε E V) (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM)
    (ℓ : V →ₗ[ℂ] ℂ) (W0 : Submodule ℂ (KS (n := n) V)) (hW0 : IsKStableSub ε (compactWordAction ε E V hV) W0)
    (hθ : ∀ x ∈ W0, sθ V EM φ ℓ x = 0) :
    ∃ W : Submodule ℂ (KS (n := n) V), W0 ≤ W ∧ IsKStableSub ε (sA ε E V hV) W ∧
      ∀ x ∈ W, sθ V EM φ ℓ x = 0 := by
  let G : Set (KS (n := n) V) := {x | x ∈ W0 ∨ ∃ c d, ∃ y ∈ W0, x = sC V c d y}
  refine ⟨Submodule.span ℂ G, fun x hx => Submodule.subset_span (Or.inl hx), fun a b hab x hx => ?_,
    fun x hx => ?_⟩
  · refine (Submodule.span_le (p := (Submodule.span ℂ G).comap (sA ε E V hV a b))).mpr ?_ hx
    have e : ∀ y, sA ε E V hV a b y = compactWordAction ε E V hV a b y + sC V a b y := fun y => by simp [compactWordAction]
    rintro y (hy | ⟨c, d, y, hy, rfl⟩)
    · show sA ε E V hV a b y ∈ Submodule.span ℂ G
      rw [e]
      exact add_mem (Submodule.subset_span (Or.inl (hW0 a b hab y hy)))
        (Submodule.subset_span (Or.inr ⟨a, b, y, hy, rfl⟩))
    · show sA ε E V hV a b (sC V c d y) ∈ Submodule.span ℂ G
      rw [e, ← Module.End.mul_apply, compactWordAction_commute, ← Module.End.mul_apply (sC V a b), sC_mul]
      refine add_mem (Submodule.subset_span (Or.inr ⟨c, d, _, hW0 a b hab y hy, rfl⟩)) ?_
      split_ifs
      · exact Submodule.subset_span (Or.inr ⟨a, d, y, hy, rfl⟩)
      · exact Submodule.zero_mem _
  · refine (Submodule.span_le (p := LinearMap.ker (sθ V EM φ ℓ))).mpr ?_ hx
    rintro y (hy | ⟨c, d, y, hy, rfl⟩)
    · exact hθ y hy
    · show sθ V EM φ ℓ (sC V c d y) = 0
      rw [sθ_sC, hθ y hy]; simp

theorem verma_weight (EM : Fin n → Fin n → Module.End ℂ MM) (hEM : IsGlRep EM) (φ : MM) (ν : Fin n → ℝ)
    (hlow : ∀ a b, b < a → EM a b φ = 0) (hwt : ∀ a, EM a a φ = ((ν a : ℝ) : ℂ) • φ)
    (hgen : genSub EM (Submodule.span ℂ {φ}) = ⊤) {μ : Fin n → ℝ} {x : MM} (hx0 : x ≠ 0)
    (hx : ∀ a, EM a a x = ((μ a : ℝ) : ℂ) • x) : InRootCone (μ - ν) := by
  by_contra hμ
  refine hx0 (vc_eq_zero_of_mem_span EM (fun β => InRootCone (β - ν)) hμ hx ?_)
  have h1 := vc_genSub_le_mon EM hEM φ ⊥ (fun a b y hy => by simp_all)
    (fun a b h => by simp [hlow a b h]) (fun a => ⟨_, hwt a⟩)
  rw [hgen, sup_bot_eq] at h1
  refine Submodule.span_mono ?_ (h1 Submodule.mem_top)
  intro w hw
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
  obtain ⟨β, h2, h3, -⟩ := vcMon_weight EM hEM hwt k w hk
  exact ⟨β, h3, h2⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.Cone
end
end

section
noncomputable section

open Finset
open scoped InnerProductSpace ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.Cone

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem klw_cons_nil (a b : Fin n) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    adLW a b (p :: w) [] = 0 := by
  simp only [adLW, Finsupp.add_apply]
  rw [Finsupp.mapDomain_of_notMem_range, Finsupp.mapDomain_of_notMem_range, add_zero] <;> simp

theorem klw_cons_cons (a b : Fin n) (p q : Fin n × Fin n) (w w' : List (Fin n × Fin n)) :
    adLW a b (p :: w) (q :: w') =
      (if w' = w then adL a b p q else 0) + (if q = p then adLW a b w w' else 0) := by
  simp only [adLW, Finsupp.add_apply]
  congr 1
  · split_ifs with h
    · subst h
      exact Finsupp.mapDomain_apply (f := fun x => x :: w') (fun x y hxy => (List.cons.inj hxy).1) _ _
    · rw [Finsupp.mapDomain_of_notMem_range]
      rintro ⟨x, hx⟩
      exact h (List.cons.inj hx).2.symm
  · split_ifs with h
    · subst h
      exact Finsupp.mapDomain_apply (f := fun x => q :: x) List.cons_injective _ _
    · rw [Finsupp.mapDomain_of_notMem_range]
      rintro ⟨x, hx⟩
      exact h (List.cons.inj hx).1.symm

theorem kl_adL_apply (a b : Fin n) (p q : Fin n × Fin n) :
    adL a b p q = (if b = p.1 ∧ q = (a, p.2) then 1 else 0) - (if p.2 = a ∧ q = (p.1, b) then 1 else 0) := by
  simp only [adL, Finsupp.sub_apply]
  congr 1
  · by_cases h : b = p.1
    · simp [h, Finsupp.single_apply, eq_comm]
    · simp [h]
  · by_cases h : p.2 = a
    · simp [h, Finsupp.single_apply, eq_comm]
    · simp [h]

theorem kl_adL_symm (a b : Fin n) (p q : Fin n × Fin n) :
    starRingEnd ℂ (adL a b p q) = adL b a q p := by
  rw [kl_adL_apply, kl_adL_apply]
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [map_sub, apply_ite (starRingEnd ℂ), map_one, map_zero, Prod.mk.injEq]
  congr 1
  · by_cases h : b = p1 ∧ q1 = a ∧ q2 = p2
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · rw [if_neg h, if_neg]; rintro ⟨rfl, rfl, rfl⟩; exact h ⟨rfl, rfl, rfl⟩
  · by_cases h : p2 = a ∧ q1 = p1 ∧ q2 = b
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · rw [if_neg h, if_neg]; rintro ⟨rfl, rfl, rfl⟩; exact h ⟨rfl, rfl, rfl⟩

theorem klw_symm (a b : Fin n) (w w' : List (Fin n × Fin n)) :
    starRingEnd ℂ (adLW a b w w') = adLW b a w' w := by
  induction w generalizing w' with
  | nil =>
    cases w' with
    | nil => simp [adLW]
    | cons q w' => rw [klw_cons_nil]; simp [adLW]
  | cons p w ih =>
    cases w' with
    | nil => rw [klw_cons_nil]; simp [adLW]
    | cons q w' =>
      rw [klw_cons_cons, klw_cons_cons, map_add, apply_ite (starRingEnd ℂ), apply_ite (starRingEnd ℂ)]
      simp only [map_zero, kl_adL_symm, ih]
      by_cases h1 : w' = w
      · subst h1
        by_cases h2 : q = p
        · subst h2; simp
        · simp [h2, Ne.symm h2]
      · by_cases h2 : q = p
        · subst h2; simp [h1, Ne.symm h1]
        · simp [h1, Ne.symm h1, h2, Ne.symm h2]

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

def ipK (V : Submodule ℂ M) : KS (n := n) V →ₗ⋆[ℂ] KS (n := n) V →ₗ[ℂ] ℂ where
  toFun x := x.sum fun p v => (innerₛₗ ℂ v) ∘ₗ Finsupp.lapply p
  map_add' x y := Finsupp.sum_add_index' (fun p => by simp) (fun p v v' => by
    rw [map_add, LinearMap.add_comp])
  map_smul' c x := by
    rw [Finsupp.sum_smul_index' (fun p => by simp), Finsupp.smul_sum]
    exact Finsupp.sum_congr fun p _ => by rw [map_smulₛₗ, LinearMap.smul_comp]

theorem ipK_single (p : List (Fin n × Fin n) × Fin n) (v : V) (y : KS (n := n) V) :
    ipK V (Finsupp.single p v) y = ⟪v, y p⟫_ℂ := by
  show ((Finsupp.single p v).sum fun p v => (innerₛₗ ℂ v) ∘ₗ Finsupp.lapply p) y = _
  rw [Finsupp.sum_single_index (by simp)]; rfl

theorem ipK_apply (x y : KS (n := n) V) : ipK V x y = ∑ p ∈ x.support, ⟪x p, y p⟫_ℂ := by
  conv_lhs => rw [← Finsupp.sum_single x, Finsupp.sum, map_sum, LinearMap.sum_apply]
  simp only [ipK_single]

theorem ipK_symm (x y : KS (n := n) V) : conj (ipK V y x) = ipK V x y := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | single p v =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | single q u =>
      rw [ipK_single, ipK_single, Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : p = q
      · simp [h]
      · simp [h, Ne.symm h]

theorem compactWordAction_single_apply (hV : IsKStableSub ε E V) {a b : Fin n} (hab : ε a = ε b)
    (p q : List (Fin n × Fin n) × Fin n) (v : V) :
    compactWordAction ε E V hV a b (Finsupp.single p v) q = (if p.2 = q.2 then adLW a b p.1 q.1 • v else 0) +
      (if p = q then (⟨E a b v, hV a b hab v v.2⟩ : V) else 0) := by
  classical
  rw [compactWordAction_single, dif_pos hab, Finsupp.add_apply, Finsupp.single_apply, Finsupp.finsetSum_apply]
  congr 1
  simp only [Finsupp.smul_apply, Finsupp.single_apply, Prod.ext_iff]
  by_cases h : p.2 = q.2
  · simp only [h, and_true, if_true]
    rw [sum_eq_single q.1 (fun w _ hw => by simp [hw]) (fun hq => by
      simp [Finsupp.notMem_support_iff.mp hq])]
    simp
  · simp [h]

theorem inner_compactWordAction_adjoint (hV : IsKStableSub ε E V) (hU : IsKUnitary ε E) {a b : Fin n} (hab : ε a = ε b)
    (x y : KS (n := n) V) : ipK V (compactWordAction ε E V hV a b x) y = ipK V x (compactWordAction ε E V hV b a y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | single p v =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' h h' => simp only [map_add, h, h']
    | single q u =>
      rw [← ipK_symm, ipK_single, ipK_single, compactWordAction_single_apply hV hab, compactWordAction_single_apply hV hab.symm,
        inner_conj_symm, inner_add_left, inner_add_right]
      congr 1
      · by_cases h : p.2 = q.2
        · rw [if_pos h, if_pos h.symm, inner_smul_left, inner_smul_right, klw_symm]
        · rw [if_neg h, if_neg (Ne.symm h), inner_zero_left, inner_zero_right]
      · by_cases h : p = q
        · rw [if_pos h, if_pos h.symm]; exact hU a b hab v u
        · rw [if_neg h, if_neg (Ne.symm h), inner_zero_left, inner_zero_right]

theorem lift0 (hV : IsKStableSub ε E V) [FiniteDimensional ℂ V] (hE : IsGlRep E) (hU : IsKUnitary ε E)
    {μ : Fin n → ℝ} {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) (hμ : ∀ c, IsKHWVec ε E μ (f c)) :
    ∃ u, IsKHWVec ε (compactWordAction ε E V hV) μ u ∧ sT E V u = f := by
  obtain ⟨x, rfl⟩ := sT_surj E V f hf
  set R := x.support.sup fun p => p.1.length with hR
  let S : Set (List (Fin n × Fin n) × Fin n) := {p | p.1.length ≤ R}
  have hSf : S.Finite := ((List.finite_length_le (Fin n × Fin n) R).prod Set.finite_univ).subset
    fun p hp => ⟨hp, trivial⟩
  have := hSf.to_subtype
  have hfd : FiniteDimensional ℂ (Finsupp.supported V ℂ S) :=
    Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := V) (R := ℂ) S).symm
  have hS : IsKStableSub ε (compactWordAction ε E V hV) (Finsupp.supported V ℂ S) := by
    intro a b hab y hy
    rw [← Finsupp.sum_single y, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun p hp => ?_
    have hpS : p.1.length ≤ R := hy hp
    rw [compactWordAction_single]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun w' hw' =>
      Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ _ ?_)) ?_
    · show w'.length ≤ R
      rw [TRA.adLW_length a b _ _ hw']; exact hpS
    · rw [dif_pos hab]
      exact Finsupp.single_mem_supported ℂ _ hpS
  let cr : InnerProductSpace.Core ℂ (KS (n := n) V) :=
    { inner := fun x y => ipK V x y
      conj_inner_symm := fun x y => ipK_symm x y
      re_inner_nonneg := fun x => by
        rw [ipK_apply, map_sum]; exact sum_nonneg fun p _ => inner_self_nonneg
      add_left := fun x y z => by rw [map_add, LinearMap.add_apply]
      smul_left := fun x y r => by rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
      definite := fun x hx => by
        have h1 := congrArg RCLike.re hx
        rw [ipK_apply, map_sum, map_zero,
          sum_eq_zero_iff_of_nonneg fun p _ => inner_self_nonneg] at h1
        ext1 p
        by_cases hp : p ∈ x.support
        · have h2 := h1 p hp
          rw [inner_self_eq_norm_sq] at h2
          exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
        · exact Finsupp.notMem_support_iff.mp hp }
  let _ : NormedAddCommGroup (KS (n := n) V) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ cr
  let _ : InnerProductSpace ℂ (KS (n := n) V) := InnerProductSpace.ofCore cr.toCore
  obtain ⟨u, -, -, h1, h2⟩ := lift_khw (ε := ε) (A := compactWordAction ε E V hV) (μ := μ)
    (B := fun a b => (E a b).compLeft (Fin n)) (fun a b hab x y => inner_compactWordAction_adjoint hV hU hab x y) (sT E V)
    (fun a b hab x => funext fun c => contraction_compactWordAction hV hE a b hab x c) hfd hS (x₀ := x)
    (fun p hp => Finset.le_sup (f := fun p : List (Fin n × Fin n) × Fin n => p.1.length) hp)
    ⟨fun a => funext fun c => (hμ c).1 a, fun a b hab he => funext fun c => (hμ c).2 a b hab he⟩
  exact ⟨u, h1, h2⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.Cone
end
end
