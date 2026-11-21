import Mathlib
import GroundTheory.PAdicHodge.FieldOfNormsRam
import GroundTheory.PAdicHodge.FieldOfNormsTower
import GroundTheory.LocalFields.Examples
import GroundTheory.LocalFields.ExamplesCharZero

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology

namespace NormTower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
  (t : NormTower K Ω p)

section Composite

def Nto (i : ℕ) : ℕ → Ω → Ω
  | 0 => id
  | j + 1 => fun y ↦ Nto i j (t.N (i + j) y)

@[simp]
theorem Nto_zero (i : ℕ) (y : Ω) : t.Nto i 0 y = y := rfl

theorem Nto_succ (i j : ℕ) (y : Ω) : t.Nto i (j + 1) y = t.Nto i j (t.N (i + j) y) := rfl

theorem Nto_succ' (i j : ℕ) (y : Ω) : t.Nto i (j + 1) y = t.N i (t.Nto (i + 1) j y) := by
  induction j generalizing y with
  | zero => simp [Nto]
  | succ j ih =>
    rw [Nto_succ, ih, Nto_succ, show i + (j + 1) = i + 1 + j by omega]

theorem Nto_mem (i : ℕ) {j : ℕ} {y : Ω} (hy : y ∈ t.E (i + j)) : t.Nto i j y ∈ t.E i := by
  induction j generalizing y with
  | zero => exact hy
  | succ j ih => exact ih (t.N_mem (i + j) hy)

@[simp]
theorem Nto_one (i j : ℕ) : t.Nto i j 1 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Nto_succ, t.N_one, ih]

@[simp]
theorem Nto_zero' (i j : ℕ) : t.Nto i j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Nto_succ, t.N_zero, ih]

def D (i j : ℕ) : ℕ :=
  ∏ m ∈ Finset.range j, p ^ t.k (i + m)

theorem D_succ (i j : ℕ) : t.D i (j + 1) = t.D i j * p ^ t.k (i + j) := by
  rw [D, Finset.prod_range_succ]; rfl

theorem D_pos (i j : ℕ) : 0 < t.D i j :=
  Finset.prod_pos fun _ _ ↦ pow_pos t.prime.pos _

theorem nrm_Nto (i j : ℕ) (y : Ω) : nrm K (t.Nto i j y) = nrm K y ^ t.D i j := by
  induction j generalizing y with
  | zero => simp [D]
  | succ j ih => rw [Nto_succ, ih, t.nrm_N, D_succ, ← pow_mul, mul_comm]

theorem nrm_Nto_le_one (i j : ℕ) {y : Ω} (hy : nrm K y ≤ 1) : nrm K (t.Nto i j y) ≤ 1 := by
  rw [nrm_Nto]; exact pow_le_one₀ (nrm_nonneg _) hy

theorem nrm_Nto_sub_Nto_le_ρ (i : ℕ) {j : ℕ} {a b : Ω} (ha : a ∈ t.E (i + j)) (hb : b ∈ t.E (i + j))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) (hab : nrm K (a - b) ≤ t.ρ) :
    nrm K (t.Nto i j a - t.Nto i j b) ≤ t.ρ := by
  induction j generalizing a b with
  | zero => exact hab
  | succ j ih =>
    exact ih (t.N_mem _ ha) (t.N_mem _ hb) (t.nrm_N_le_one _ ha1) (t.nrm_N_le_one _ hb1)
      (t.nrm_N_sub_N_le_ρ _ ha hb ha1 hb1 hab)

theorem nrm_Nto_add_sub_le_ρ (i : ℕ) {j : ℕ} {a b : Ω} (ha : a ∈ t.E (i + j)) (hb : b ∈ t.E (i + j))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) :
    nrm K (t.Nto i j (a + b) - t.Nto i j a - t.Nto i j b) ≤ t.ρ := by
  induction j generalizing a b with
  | zero => simp [t.ρ_nonneg]
  | succ j ih =>
    simp only [Nto_succ]
    have hNa := t.N_mem _ ha
    have hNb := t.N_mem _ hb
    have hNa1 := t.nrm_N_le_one (i + j) ha1
    have hNb1 := t.nrm_N_le_one (i + j) hb1
    have h1 := t.nrm_Nto_sub_Nto_le_ρ i (t.N_mem _ (add_mem ha hb)) (add_mem hNa hNb)
      (t.nrm_N_le_one _ (nrm_add_le_one ha1 hb1)) (nrm_add_le_one hNa1 hNb1)
      (by rw [sub_add_eq_sub_sub]; exact t.nrm_N_add_sub_le_ρ _ ha hb ha1 hb1)
    have h2 := ih hNa hNb hNa1 hNb1
    have e : t.Nto i j (t.N (i + j) (a + b)) - t.Nto i j (t.N (i + j) a) - t.Nto i j (t.N (i + j) b) =
        (t.Nto i j (t.N (i + j) (a + b)) - t.Nto i j (t.N (i + j) a + t.N (i + j) b)) +
        (t.Nto i j (t.N (i + j) a + t.N (i + j) b) - t.Nto i j (t.N (i + j) a) -
          t.Nto i j (t.N (i + j) b)) := by ring
    rw [e]
    exact nrm_add_le_of_le h1 h2

def cnt (i j : ℕ) : ℕ :=
  ((Finset.range j).filter fun m ↦ t.k (i + m) ≠ 0).card

theorem cnt_succ (i j : ℕ) : t.cnt i (j + 1) = t.cnt i j + if t.k (i + j) ≠ 0 then 1 else 0 := by
  simp only [cnt, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rw [add_zero]

theorem cnt_mono (i : ℕ) : Monotone (t.cnt i) := by
  intro j j' h
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

theorem exists_le_cnt (i M : ℕ) : ∃ j, M ≤ t.cnt i j := by
  induction M with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ M ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨m, hm, hk⟩ := t.frequently_ne_zero (i + j)
    refine ⟨m - i + 1, ?_⟩
    rw [cnt_succ, if_pos (by rwa [show i + (m - i) = m by omega])]
    have := t.cnt_mono i (show j ≤ m - i by omega)
    omega

theorem nrm_Nto_sub_Nto_le (i : ℕ) {j : ℕ} {a b : Ω} (ha : a ∈ t.E (i + j)) (hb : b ∈ t.E (i + j))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) {s : ℝ} (hs : s ≤ t.ρ) (hab : nrm K (a - b) ≤ s) :
    nrm K (t.Nto i j a - t.Nto i j b) ≤ t.ρ ^ t.cnt i j * s := by
  induction j generalizing a b s with
  | zero => simpa [cnt] using hab
  | succ j ih =>
    simp only [Nto_succ]
    have hs0 : 0 ≤ s := (nrm_nonneg _).trans hab
    by_cases hk : t.k (i + j) ≠ 0
    · have h1 := t.nrm_N_sub_N_le_mul (i + j) hk ha hb ha1 hb1 hs hab
      have hs' : t.ρ * s ≤ t.ρ :=
        (mul_le_of_le_one_left hs0 t.ρ_lt_one.le).trans hs
      refine (ih (t.N_mem _ ha) (t.N_mem _ hb) (t.nrm_N_le_one _ ha1) (t.nrm_N_le_one _ hb1)
        hs' h1).trans (le_of_eq ?_)
      rw [cnt_succ, if_pos hk, pow_succ]; ring
    · have h1 := t.nrm_N_sub_N_le (i + j) ha hb ha1 hb1 hs hab
      refine (ih (t.N_mem _ ha) (t.N_mem _ hb) (t.nrm_N_le_one _ ha1) (t.nrm_N_le_one _ hb1)
        hs h1).trans (le_of_eq ?_)
      rw [cnt_succ, if_neg hk, add_zero]

end Composite

section Families

def IsFam (z : ℕ → Ω) : Prop :=
  ∀ n, z n ∈ t.E n ∧ t.N n (z (n + 1)) = z n

def IsIntFam (z : ℕ → Ω) : Prop :=
  t.IsFam z ∧ ∀ n, nrm K (z n) ≤ 1

variable {t}

theorem IsFam.Nto_eq {z : ℕ → Ω} (hz : t.IsFam z) (i j : ℕ) : t.Nto i j (z (i + j)) = z i := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Nto_succ, ← add_assoc, (hz (i + j)).2, ih]

theorem IsFam.nrm_eq {z : ℕ → Ω} (hz : t.IsFam z) (i j : ℕ) :
    nrm K (z i) = nrm K (z (i + j)) ^ t.D i j := by
  rw [← hz.Nto_eq i j, nrm_Nto]

theorem intFam_ext {z z' : ℕ → Ω} (hz : t.IsIntFam z) (hz' : t.IsIntFam z')
    (h : ∀ n, nrm K (z n - z' n) ≤ t.ρ) : z = z' := by
  funext i
  rw [← sub_eq_zero, ← nrm_eq_zero (K := K)]
  refine le_antisymm ?_ (nrm_nonneg _)
  have hle : ∀ M : ℕ, nrm K (z i - z' i) ≤ t.ρ ^ M := by
    intro M
    obtain ⟨j, hj⟩ := t.exists_le_cnt i M
    rw [← hz.1.Nto_eq i j, ← hz'.1.Nto_eq i j]
    refine (t.nrm_Nto_sub_Nto_le i (hz.1 _).1 (hz'.1 _).1 (hz.2 _) (hz'.2 _) le_rfl
      (h _)).trans ?_
    calc t.ρ ^ t.cnt i j * t.ρ ≤ t.ρ ^ t.cnt i j * 1 :=
          mul_le_mul_of_nonneg_left t.ρ_lt_one.le (pow_nonneg t.ρ_nonneg _)
      _ = t.ρ ^ t.cnt i j := mul_one _
      _ ≤ t.ρ ^ M := pow_le_pow_of_le_one t.ρ_nonneg t.ρ_lt_one.le hj
  exact ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one t.ρ_nonneg t.ρ_lt_one) hle

variable (t)

def intSet (n : ℕ) : Set Ω :=
  {y | y ∈ t.E n ∧ nrm K y ≤ 1}

theorem isCompact_intSet (n : ℕ) : IsCompact (t.intSet n) := by
  haveI := t.finiteDimensional n
  have hc := IsNonarchimedeanLocalField.isCompact_closedBall (t.E n) 1
  have : t.intSet n = Subtype.val '' {x : t.E n | valuation (t.E n) x ≤ 1} := by
    ext y
    simp only [intSet, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hy, hy1⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [← map_one (valuation (t.E n)), ← (valuation (t.E n)).vle_iff_le,
        ← IntermediateField.coe_vle_coe_iff]
      rw [← nrm_le_nrm_iff (K := K)]
      simpa using hy1
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      rw [← map_one (valuation (t.E n)), ← (valuation (t.E n)).vle_iff_le,
        ← IntermediateField.coe_vle_coe_iff, ← nrm_le_nrm_iff (K := K)] at hx
      simpa using hx
  rw [this]
  exact hc.image continuous_subtype_val

theorem continuous_N (n : ℕ) : Continuous (t.N n) :=
  continuous_finsetProd _ fun σ _ ↦ continuous_algEquiv_of_isAlgebraic σ

theorem nrm_Nto_sub_le_of_cong {a : ℕ → Ω} (ha : ∀ n, a n ∈ t.E n) (ha1 : ∀ n, nrm K (a n) ≤ 1)
    (hcong : ∀ n, nrm K (t.N n (a (n + 1)) - a n) ≤ t.ρ) (i j : ℕ) :
    nrm K (t.Nto i j (a (i + j)) - a i) ≤ t.ρ := by
  induction j with
  | zero => simp [t.ρ_nonneg]
  | succ j ih =>
    rw [Nto_succ, ← add_assoc]
    have h1 := t.nrm_Nto_sub_Nto_le_ρ i (t.N_mem _ (ha _)) (ha (i + j))
      (t.nrm_N_le_one _ (ha1 _)) (ha1 _) (hcong _)
    exact nrm_sub_le_of_le' h1 ih

theorem exists_intFam {a : ℕ → Ω} (ha : ∀ n, a n ∈ t.E n) (ha1 : ∀ n, nrm K (a n) ≤ 1)
    (hcong : ∀ n, nrm K (t.N n (a (n + 1)) - a n) ≤ t.ρ) :
    ∃ z, t.IsIntFam z ∧ ∀ n, nrm K (z n - a n) ≤ t.ρ := by

  let S : ℕ → Set (ℕ → Ω) := fun m ↦
    {z | (∀ n < m, nrm K (t.N n (z (n + 1)) - z n) ≤ 0) ∧ ∀ n ≤ m, nrm K (z n - a n) ≤ t.ρ}
  have hP : IsCompact {z : ℕ → Ω | ∀ n, z n ∈ t.intSet n} :=
    isCompact_pi_infinite t.isCompact_intSet
  have hcont : ∀ n, Continuous fun z : ℕ → Ω ↦ nrm K (t.N n (z (n + 1)) - z n) := fun n ↦
    (continuous_nrm K Ω).comp (((t.continuous_N n).comp (continuous_apply _)).sub
      (continuous_apply _))
  have hcont' : ∀ n, Continuous fun z : ℕ → Ω ↦ nrm K (z n - a n) := fun n ↦
    (continuous_nrm K Ω).comp ((continuous_apply _).sub continuous_const)
  have hcl : ∀ m, IsClosed (S m) := by
    intro m
    have e : S m = (⋂ n ∈ {n | n < m}, {z : ℕ → Ω | nrm K (t.N n (z (n + 1)) - z n) ≤ 0}) ∩
        ⋂ n ∈ {n | n ≤ m}, {z : ℕ → Ω | nrm K (z n - a n) ≤ t.ρ} := by
      ext z; simp [S]
    rw [e]
    exact (isClosed_biInter fun n _ ↦ isClosed_le (hcont n) continuous_const).inter
      (isClosed_biInter fun n _ ↦ isClosed_le (hcont' n) continuous_const)
  have hanti : ∀ {m m'}, m ≤ m' → S m' ⊆ S m := fun hmm' z hz ↦
    ⟨fun n hn ↦ hz.1 n (by omega), fun n hn ↦ hz.2 n (by omega)⟩
  have hne : ∀ m, ({z : ℕ → Ω | ∀ n, z n ∈ t.intSet n} ∩ S m).Nonempty := by
    intro m
    refine ⟨fun n ↦ if n ≤ m then t.Nto n (m - n) (a m) else a n, ?_, ?_, ?_⟩
    · intro n
      dsimp only
      split_ifs with h
      · have ham : a m ∈ t.E (n + (m - n)) := by rw [Nat.add_sub_cancel' h]; exact ha m
        exact ⟨t.Nto_mem n ham, t.nrm_Nto_le_one _ _ (ha1 m)⟩
      · exact ⟨ha n, ha1 n⟩
    · intro n hn
      simp only [if_pos hn.le, if_pos (show n + 1 ≤ m by omega)]
      rw [← Nto_succ', show m - n = m - (n + 1) + 1 by omega]
      simp
    · intro n hn
      simp only [if_pos hn]
      have := t.nrm_Nto_sub_le_of_cong ha ha1 hcong n (m - n)
      rwa [Nat.add_sub_cancel' hn] at this
  obtain ⟨z, hzP, hz⟩ := hP.inter_iInter_nonempty S hcl fun u ↦ by
    obtain ⟨z, hzP, hzS⟩ := hne (u.sup id)
    refine ⟨z, hzP, Set.mem_iInter₂.mpr fun m hm ↦ hanti (Finset.le_sup (f := id) hm) hzS⟩
  rw [Set.mem_iInter] at hz
  refine ⟨z, ⟨fun n ↦ ⟨(hzP n).1, ?_⟩, fun n ↦ (hzP n).2⟩, fun n ↦ (hz n).2 n le_rfl⟩
  have := (hz (n + 1)).1 n (Nat.lt_succ_self n)
  rw [← sub_eq_zero, ← nrm_eq_zero (K := K)]
  exact le_antisymm this (nrm_nonneg _)

end Families

section Ring

def Plus : Type _ :=
  {z : ℕ → Ω // t.IsIntFam z}

namespace Plus

variable {t}

theorem mem (x : t.Plus) (n : ℕ) : x.1 n ∈ t.E n := (x.2.1 n).1

theorem nrm_le (x : t.Plus) (n : ℕ) : nrm K (x.1 n) ≤ 1 := x.2.2 n

theorem N_eq (x : t.Plus) (n : ℕ) : t.N n (x.1 (n + 1)) = x.1 n := (x.2.1 n).2

theorem isFam (x : t.Plus) : t.IsFam x.1 := x.2.1

theorem eq_of_cong {x y : t.Plus} (h : ∀ n, nrm K (x.1 n - y.1 n) ≤ t.ρ) : x = y :=
  Subtype.ext (intFam_ext x.2 y.2 h)

instance : Zero t.Plus :=
  ⟨⟨fun _ ↦ 0, fun n ↦ ⟨zero_mem _, t.N_zero n⟩, fun n ↦ by simp⟩⟩

instance : One t.Plus :=
  ⟨⟨fun _ ↦ 1, fun n ↦ ⟨one_mem _, t.N_one n⟩, fun n ↦ by simp⟩⟩

instance : Mul t.Plus :=
  ⟨fun x y ↦ ⟨fun n ↦ x.1 n * y.1 n, fun n ↦ ⟨mul_mem (x.mem n) (y.mem n),
    by rw [t.N_mul, x.N_eq, y.N_eq]⟩, fun n ↦ nrm_mul_le_one (x.nrm_le n) (y.nrm_le n)⟩⟩

@[simp] theorem zero_val (n : ℕ) : (0 : t.Plus).1 n = 0 := rfl
@[simp] theorem one_val (n : ℕ) : (1 : t.Plus).1 n = 1 := rfl
@[simp] theorem mul_val (x y : t.Plus) (n : ℕ) : (x * y).1 n = x.1 n * y.1 n := rfl

theorem exists_add (x y : t.Plus) :
    ∃ z, t.IsIntFam z ∧ ∀ n, nrm K (z n - (x.1 n + y.1 n)) ≤ t.ρ :=
  t.exists_intFam (fun n ↦ add_mem (x.mem n) (y.mem n))
    (fun n ↦ nrm_add_le_one (x.nrm_le n) (y.nrm_le n)) fun n ↦ by
      have := t.nrm_N_add_sub_le_ρ n (x.mem (n + 1)) (y.mem (n + 1)) (x.nrm_le _) (y.nrm_le _)
      rw [x.N_eq, y.N_eq] at this
      rwa [sub_add_eq_sub_sub]

theorem exists_neg (x : t.Plus) : ∃ z, t.IsIntFam z ∧ ∀ n, nrm K (z n - -x.1 n) ≤ t.ρ :=
  t.exists_intFam (fun n ↦ neg_mem (x.mem n)) (fun n ↦ by simpa using x.nrm_le n) fun n ↦ by
    have := t.nrm_N_add_sub_le_ρ n (neg_mem (x.mem (n + 1))) (x.mem (n + 1))
      (by simpa using x.nrm_le (n + 1)) (x.nrm_le _)
    rw [neg_add_cancel, t.N_zero, x.N_eq] at this
    rw [sub_neg_eq_add, ← nrm_neg]
    convert this using 2; ring

instance : Add t.Plus :=
  ⟨fun x y ↦ ⟨(exists_add x y).choose, (exists_add x y).choose_spec.1⟩⟩

instance : Neg t.Plus :=
  ⟨fun x ↦ ⟨(exists_neg x).choose, (exists_neg x).choose_spec.1⟩⟩

theorem add_cong (x y : t.Plus) (n : ℕ) : nrm K ((x + y).1 n - (x.1 n + y.1 n)) ≤ t.ρ :=
  (exists_add x y).choose_spec.2 n

theorem neg_cong (x : t.Plus) (n : ℕ) : nrm K ((-x).1 n - -x.1 n) ≤ t.ρ :=
  (exists_neg x).choose_spec.2 n

theorem ρ_nonneg' : 0 ≤ t.ρ := t.ρ_nonneg

private theorem cong4 {a b c d e : Ω} (h1 : nrm K a ≤ t.ρ) (h2 : nrm K b ≤ t.ρ)
    (h3 : nrm K c ≤ t.ρ) (h4 : nrm K d ≤ t.ρ) (he : e = a + b - c - d) : nrm K e ≤ t.ρ := by
  rw [he]
  exact nrm_sub_le_of_le (nrm_sub_le_of_le (nrm_add_le_of_le h1 h2) h3) h4

instance instCommRing : CommRing t.Plus where
  add_assoc x y z := eq_of_cong fun n ↦
    cong4 (add_cong (x + y) z n) (add_cong x y n) (add_cong y z n) (add_cong x (y + z) n) (by ring)
  zero_add x := eq_of_cong fun n ↦ by
    have := add_cong 0 x n; simpa using this
  add_zero x := eq_of_cong fun n ↦ by
    have := add_cong x 0 n; simpa using this
  add_comm x y := eq_of_cong fun n ↦
    cong4 (add_cong x y n) (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg)
      (add_cong y x n) (by ring)
  neg_add_cancel x := eq_of_cong fun n ↦ by
    have h1 := add_cong (-x) x n
    have h2 := neg_cong x n
    exact cong4 h1 h2 (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg)
      (by rw [zero_val]; ring)
  nsmul := nsmulRec
  zsmul := zsmulRec
  left_distrib x y z := eq_of_cong fun n ↦ by
    have h1 := add_cong y z n
    have h2 := add_cong (x * y) (x * z) n
    have h1' : nrm K (x.1 n * (y + z).1 n - x.1 n * (y.1 n + z.1 n)) ≤ t.ρ := by
      rw [← mul_sub, nrm_mul]
      exact (mul_le_of_le_one_left (nrm_nonneg _) (x.nrm_le n)).trans h1
    exact cong4 h1' (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) h2
      (by simp; ring)
  right_distrib x y z := eq_of_cong fun n ↦ by
    have h1 := add_cong x y n
    have h2 := add_cong (x * z) (y * z) n
    have h1' : nrm K ((x + y).1 n * z.1 n - (x.1 n + y.1 n) * z.1 n) ≤ t.ρ := by
      rw [← sub_mul, nrm_mul]
      exact (mul_le_of_le_one_right (nrm_nonneg _) (z.nrm_le n)).trans h1
    exact cong4 h1' (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) (nrm_zero (K := K) (Ω := Ω) ▸ t.ρ_nonneg) h2
      (by simp; ring)
  zero_mul x := Subtype.ext (funext fun n ↦ by simp)
  mul_zero x := Subtype.ext (funext fun n ↦ by simp)
  mul_assoc x y z := Subtype.ext (funext fun n ↦ by simp [mul_assoc])
  one_mul x := Subtype.ext (funext fun n ↦ by simp)
  mul_one x := Subtype.ext (funext fun n ↦ by simp)
  mul_comm x y := Subtype.ext (funext fun n ↦ by simp [mul_comm])

end Plus

end Ring

end NormTower

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}

namespace NormTower

variable (t : NormTower K Ω p)

theorem exists_intFam_mem {C : ℕ → Set Ω} (hcl : ∀ n, IsClosed (C n))
    (hne : ∀ n, (t.intSet n ∩ C n).Nonempty)
    (hN : ∀ n, ∀ y ∈ t.intSet (n + 1) ∩ C (n + 1), t.N n y ∈ C n) :
    ∃ z, t.IsIntFam z ∧ ∀ n, z n ∈ C n := by
  have hNint : ∀ n, ∀ y ∈ t.intSet (n + 1), t.N n y ∈ t.intSet n :=
    fun n y hy ↦ ⟨t.N_mem n hy.1, t.nrm_N_le_one n hy.2⟩

  have hNto : ∀ i j, ∀ y ∈ t.intSet (i + j) ∩ C (i + j), t.Nto i j y ∈ t.intSet i ∩ C i := by
    intro i j
    induction j with
    | zero => exact fun y hy ↦ hy
    | succ j ih =>
      intro y hy
      rw [Nto_succ]
      exact ih _ ⟨hNint _ _ hy.1, hN _ _ hy⟩
  let S : ℕ → Set (ℕ → Ω) := fun m ↦
    {z | (∀ n < m, nrm K (t.N n (z (n + 1)) - z n) ≤ 0) ∧ ∀ n ≤ m, z n ∈ C n}
  have hP : IsCompact {z : ℕ → Ω | ∀ n, z n ∈ t.intSet n} :=
    isCompact_pi_infinite t.isCompact_intSet
  have hcont : ∀ n, Continuous fun z : ℕ → Ω ↦ nrm K (t.N n (z (n + 1)) - z n) := fun n ↦
    (continuous_nrm K Ω).comp (((t.continuous_N n).comp (continuous_apply _)).sub
      (continuous_apply _))
  have hcl' : ∀ m, IsClosed (S m) := by
    intro m
    have e : S m = (⋂ n ∈ {n | n < m}, {z : ℕ → Ω | nrm K (t.N n (z (n + 1)) - z n) ≤ 0}) ∩
        ⋂ n ∈ {n | n ≤ m}, (fun z : ℕ → Ω ↦ z n) ⁻¹' C n := by
      ext z; simp [S]
    rw [e]
    exact (isClosed_biInter fun n _ ↦ isClosed_le (hcont n) continuous_const).inter
      (isClosed_biInter fun n _ ↦ (hcl n).preimage (continuous_apply n))
  have hanti : ∀ {m m'}, m ≤ m' → S m' ⊆ S m := fun hmm' z hz ↦
    ⟨fun n hn ↦ hz.1 n (by omega), fun n hn ↦ hz.2 n (by omega)⟩
  have hne' : ∀ m, ({z : ℕ → Ω | ∀ n, z n ∈ t.intSet n} ∩ S m).Nonempty := by
    intro m
    obtain ⟨y, hy⟩ := hne m
    refine ⟨fun n ↦ if n ≤ m then t.Nto n (m - n) y else 0, ?_, ?_, ?_⟩
    · intro n
      dsimp only
      split_ifs with h
      · have hy' : y ∈ t.intSet (n + (m - n)) ∩ C (n + (m - n)) := by
          rw [Nat.add_sub_cancel' h]; exact hy
        exact (hNto n _ y hy').1
      · exact ⟨zero_mem _, by simp⟩
    · intro n hn
      simp only [if_pos hn.le, if_pos (show n + 1 ≤ m by omega)]
      rw [← Nto_succ', show m - n = m - (n + 1) + 1 by omega]
      simp
    · intro n hn
      simp only [if_pos hn]
      have hy' : y ∈ t.intSet (n + (m - n)) ∩ C (n + (m - n)) := by
        rw [Nat.add_sub_cancel' hn]; exact hy
      exact (hNto n _ y hy').2
  obtain ⟨z, hzP, hz⟩ := hP.inter_iInter_nonempty S hcl' fun u ↦ by
    obtain ⟨z, hzP, hzS⟩ := hne' (u.sup id)
    refine ⟨z, hzP, Set.mem_iInter₂.mpr fun m hm ↦ hanti (Finset.le_sup (f := id) hm) hzS⟩
  rw [Set.mem_iInter] at hz
  refine ⟨z, ⟨fun n ↦ ⟨(hzP n).1, ?_⟩, fun n ↦ (hzP n).2⟩, fun n ↦ (hz n).2 n le_rfl⟩
  have := (hz (n + 1)).1 n (Nat.lt_succ_self n)
  rw [← sub_eq_zero, ← nrm_eq_zero (K := K)]
  exact le_antisymm this (nrm_nonneg _)

namespace Plus

variable {t}

theorem nrm_val_zero (x : t.Plus) (n : ℕ) : nrm K (x.1 0) = nrm K (x.1 n) ^ t.D 0 n := by
  have := x.isFam.nrm_eq 0 n
  rwa [zero_add] at this

theorem val_eq_zero_iff (x : t.Plus) (n : ℕ) : x.1 n = 0 ↔ x.1 0 = 0 := by
  rw [← nrm_eq_zero (K := K), ← nrm_eq_zero (K := K) (x := x.1 0), nrm_val_zero x n,
    pow_eq_zero_iff (t.D_pos 0 n).ne']

theorem eq_zero_iff (x : t.Plus) : x = 0 ↔ x.1 0 = 0 := by
  constructor
  · rintro rfl; rfl
  · intro h
    exact Subtype.ext (funext fun n ↦ (val_eq_zero_iff x n).mpr h)

theorem natCast_cong (m n : ℕ) : nrm K (((m : ℕ) : t.Plus).1 n - (m : Ω)) ≤ t.ρ := by
  induction m with
  | zero => simp [t.ρ_nonneg]
  | succ m ih =>
    have h := add_cong (m : t.Plus) 1 n
    rw [Nat.cast_succ, Nat.cast_succ]
    have e : ((m : t.Plus) + 1).1 n - ((m : Ω) + 1) =
        (((m : t.Plus) + 1).1 n - ((m : t.Plus).1 n + (1 : t.Plus).1 n)) +
          ((m : t.Plus).1 n - (m : Ω)) := by simp; ring
    rw [e]
    exact nrm_add_le_of_le h ih

instance instNontrivial : Nontrivial t.Plus :=
  ⟨⟨0, 1, fun h ↦ by simpa using congrArg (fun x : t.Plus ↦ x.1 0) h⟩⟩

theorem natCast_p : ((p : ℕ) : t.Plus) = 0 :=
  eq_of_cong fun n ↦ by
    have h := natCast_cong (t := t) p n
    simp only [zero_val, sub_zero]
    have : ((p : ℕ) : t.Plus).1 n = (((p : ℕ) : t.Plus).1 n - (p : Ω)) + (p : Ω) := by ring
    rw [this]
    exact nrm_add_le_of_le h t.nrm_p_le_ρ

instance instNoZeroDivisors : NoZeroDivisors t.Plus where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    rw [eq_zero_iff] at h
    simp only [mul_val, mul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl ((eq_zero_iff x).mpr h)
    · exact Or.inr ((eq_zero_iff y).mpr h)

instance instIsDomain : IsDomain t.Plus :=
  NoZeroDivisors.to_isDomain _

theorem charP : CharP t.Plus p :=
  (CharP.charP_iff_prime_eq_zero t.prime).mpr natCast_p

variable (t) in

theorem exists_unif : ∃ z, t.IsIntFam z ∧ ∀ n, nrm K (z n) = t.value n := by
  refine t.exists_intFam_mem (C := fun n ↦ {y | nrm K y = t.value n})
    (fun n ↦ isClosed_eq (continuous_nrm K Ω) continuous_const) (fun n ↦ ?_) (fun n y hy ↦ ?_)
  · obtain ⟨π, hπ, hπv⟩ := t.exists_value n
    exact ⟨π, ⟨hπ, hπv ▸ (t.value_lt_one n).le⟩, hπv⟩
  · simp only [Set.mem_ofPred_eq] at hy ⊢
    rw [t.nrm_N, hy.2, t.value_succ]

variable (t) in

def unif : t.Plus :=
  ⟨(exists_unif t).choose, (exists_unif t).choose_spec.1⟩

theorem nrm_unif (n : ℕ) : nrm K ((unif t).1 n) = t.value n :=
  (exists_unif t).choose_spec.2 n

theorem unif_ne_zero : unif t ≠ 0 := by
  rw [Ne, eq_zero_iff, ← nrm_eq_zero (K := K), nrm_unif]
  exact (t.value_pos 0).ne'

theorem unif_val_ne_zero (n : ℕ) : (unif t).1 n ≠ 0 := by
  rw [← nrm_pos (K := K), nrm_unif]; exact t.value_pos n

theorem val_ne_zero {x : t.Plus} (hx : x ≠ 0) (n : ℕ) : x.1 n ≠ 0 := by
  rw [Ne, val_eq_zero_iff, ← eq_zero_iff]; exact hx

theorem pow_val (x : t.Plus) (k n : ℕ) : (x ^ k).1 n = x.1 n ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_val, ih, pow_succ]

end Plus

section Fam

def Fam : Type _ :=
  {z : ℕ → Ω // t.IsFam z}

namespace Plus

variable {t}

def toFam (x : t.Plus) : t.Fam := ⟨x.1, x.2.1⟩

@[simp] theorem toFam_val (x : t.Plus) : x.toFam.1 = x.1 := rfl

theorem pow_max_max_le_max_pow {a b c : ℝ} (n : ℕ) :
    (max (max a b) c) ^ n ≤ max (max (a ^ n) (b ^ n)) (c ^ n) := by
  rcases max_choice (max a b) c with h | h
  · rw [h]
    rcases max_choice a b with h' | h'
    · rw [h']; exact le_max_of_le_left (le_max_left _ _)
    · rw [h']; exact le_max_of_le_left (le_max_right _ _)
  · rw [h]; exact le_max_right _ _

theorem nrm_add_val_zero_le (x y : t.Plus) :
    nrm K ((x + y).1 0) ≤ max (nrm K (x.1 0)) (nrm K (y.1 0)) := by
  have hle : ∀ j, nrm K ((x + y).1 0) ≤ max (max (nrm K (x.1 0)) (nrm K (y.1 0))) (t.ρ ^ t.D 0 j) := by
    intro j
    rw [nrm_val_zero (x + y) j, nrm_val_zero x j, nrm_val_zero y j]
    have h1 : nrm K ((x + y).1 j) ≤ max (max (nrm K (x.1 j)) (nrm K (y.1 j))) t.ρ := by
      have : (x + y).1 j = ((x + y).1 j - (x.1 j + y.1 j)) + (x.1 j + y.1 j) := by ring
      rw [this]
      refine (nrm_add_le_max _ _).trans (max_le (le_max_of_le_right (add_cong x y j)) ?_)
      exact le_max_of_le_left (nrm_add_le_max _ _)
    have hD := t.D_pos 0 j
    calc nrm K ((x + y).1 j) ^ t.D 0 j ≤ (max (max (nrm K (x.1 j)) (nrm K (y.1 j))) t.ρ) ^ t.D 0 j :=
          pow_le_pow_left₀ (nrm_nonneg _) h1 _
      _ ≤ max (max (nrm K (x.1 j) ^ t.D 0 j) (nrm K (y.1 j) ^ t.D 0 j)) (t.ρ ^ t.D 0 j) :=
          pow_max_max_le_max_pow _

  have hDj : ∀ M : ℕ, ∃ j, M ≤ t.D 0 j := by
    intro M
    obtain ⟨j, hj⟩ := t.exists_le_cnt 0 M
    refine ⟨j, hj.trans ?_⟩

    clear hj
    induction j with
    | zero => simp [cnt, D]
    | succ j ih =>
      rw [cnt_succ, D_succ]
      split_ifs with hk
      · have h2 : 2 ≤ p ^ t.k (0 + j) :=
          (t.prime.two_le).trans (Nat.le_self_pow hk _)
        have := t.D_pos 0 j
        nlinarith
      · have := Nat.one_le_pow (t.k (0 + j)) p t.prime.pos
        nlinarith
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε t.ρ_lt_one
  obtain ⟨j, hj⟩ := hDj M
  have h := hle j
  have hρj : t.ρ ^ t.D 0 j ≤ t.ρ ^ M := pow_le_pow_of_le_one t.ρ_nonneg t.ρ_lt_one.le hj
  rcases le_total (max (nrm K (x.1 0)) (nrm K (y.1 0))) (t.ρ ^ t.D 0 j) with h' | h'
  · rw [max_eq_right h'] at h
    linarith [le_max_left (nrm K (x.1 0)) (nrm K (y.1 0)), nrm_nonneg (K := K) (x.1 0)]
  · rw [max_eq_left h'] at h
    linarith

end Plus

namespace Fam

variable {t}

theorem mem (x : t.Fam) (n : ℕ) : x.1 n ∈ t.E n := (x.2 n).1

theorem N_eq (x : t.Fam) (n : ℕ) : t.N n (x.1 (n + 1)) = x.1 n := (x.2 n).2

theorem nrm_val_zero (x : t.Fam) (n : ℕ) : nrm K (x.1 0) = nrm K (x.1 n) ^ t.D 0 n := by
  have := x.2.nrm_eq 0 n
  rwa [zero_add] at this

theorem val_eq_zero_iff (x : t.Fam) (n : ℕ) : x.1 n = 0 ↔ x.1 0 = 0 := by
  rw [← nrm_eq_zero (K := K), ← nrm_eq_zero (K := K) (x := x.1 0), nrm_val_zero x n,
    pow_eq_zero_iff (t.D_pos 0 n).ne']

theorem isIntFam_of_nrm_le {x : t.Fam} (h : nrm K (x.1 0) ≤ 1) : t.IsIntFam x.1 := by
  refine ⟨x.2, fun n ↦ ?_⟩
  rw [nrm_val_zero x n] at h
  exact (pow_le_one_iff_of_nonneg (nrm_nonneg _) (t.D_pos 0 n).ne').mp h

def scale (x : t.Fam) (m : ℕ) : t.Fam :=
  ⟨fun n ↦ (Plus.unif t).1 n ^ m * x.1 n, fun n ↦ ⟨mul_mem (pow_mem ((Plus.unif t).mem n) m) (x.mem n),
    by rw [t.N_mul, t.N_pow, (Plus.unif t).N_eq, x.N_eq]⟩⟩

theorem nrm_scale_val_zero (x : t.Fam) (m : ℕ) :
    nrm K ((x.scale m).1 0) = t.value 0 ^ m * nrm K (x.1 0) := by
  show nrm K ((Plus.unif t).1 0 ^ m * x.1 0) = _
  rw [nrm_mul, nrm_pow, Plus.nrm_unif]

theorem exists_scale (x : t.Fam) : ∃ m, t.value 0 ^ m * nrm K (x.1 0) ≤ 1 := by
  rcases eq_or_lt_of_le (nrm_nonneg (K := K) (x.1 0)) with h | h
  · exact ⟨0, by rw [← h]; simp⟩
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr h) (t.value_lt_one 0)
  refine ⟨m, ?_⟩
  rw [← le_div_iff₀ h, one_div]
  exact hm.le

def scalePlus (x : t.Fam) (m : ℕ) (h : t.value 0 ^ m * nrm K (x.1 0) ≤ 1) : t.Plus :=
  ⟨(x.scale m).1, isIntFam_of_nrm_le (by rwa [nrm_scale_val_zero])⟩

theorem unif_pow_mem (m : ℕ) : Plus.unif t ^ m ∈ nonZeroDivisors t.Plus :=
  pow_mem (mem_nonZeroDivisors_of_ne_zero Plus.unif_ne_zero) m

def toFrac (x : t.Fam) : FractionRing t.Plus :=
  IsLocalization.mk' _ (scalePlus x (Nat.find (exists_scale x)) (Nat.find_spec (exists_scale x)))
    ⟨Plus.unif t ^ Nat.find (exists_scale x), unif_pow_mem _⟩

theorem injective_algebraMap :
    Function.Injective (algebraMap t.Plus (FractionRing t.Plus)) :=
  IsFractionRing.injective t.Plus (FractionRing t.Plus)

theorem toFrac_eq (x : t.Fam) (m : ℕ) (h : t.value 0 ^ m * nrm K (x.1 0) ≤ 1) :
    toFrac x = IsLocalization.mk' _ (scalePlus x m h) ⟨Plus.unif t ^ m, unif_pow_mem _⟩ := by
  rw [toFrac, IsLocalization.mk'_eq_iff_eq]
  congr 1
  refine Subtype.ext (funext fun n ↦ ?_)
  change (Plus.unif t ^ m).1 n * ((Plus.unif t).1 n ^ _ * x.1 n) =
    (Plus.unif t ^ _).1 n * ((Plus.unif t).1 n ^ m * x.1 n)
  rw [Plus.pow_val, Plus.pow_val]
  ring

def ofDiv (a : t.Plus) (b : nonZeroDivisors t.Plus) : t.Fam :=
  ⟨fun n ↦ a.1 n / b.1.1 n, fun n ↦ ⟨div_mem (a.mem n) (b.1.mem n), by
    show t.N n (a.1 (n + 1) / b.1.1 (n + 1)) = a.1 n / b.1.1 n
    rw [div_eq_mul_inv, t.N_mul, t.N_inv, a.N_eq, b.1.N_eq, div_eq_mul_inv]⟩⟩

theorem ofDiv_val (a : t.Plus) (b : nonZeroDivisors t.Plus) (n : ℕ) :
    (ofDiv a b).1 n = a.1 n / b.1.1 n := rfl

theorem val_ne_zero_of_mem {b : t.Plus} (hb : b ∈ nonZeroDivisors t.Plus) (n : ℕ) : b.1 n ≠ 0 :=
  Plus.val_ne_zero (nonZeroDivisors.ne_zero hb) n

theorem ofDiv_eq_ofDiv {a a' : t.Plus} {b b' : nonZeroDivisors t.Plus}
    (h : IsLocalization.mk' (FractionRing t.Plus) a b = IsLocalization.mk' _ a' b') :
    ofDiv a b = ofDiv a' b' := by
  rw [IsLocalization.mk'_eq_iff_eq] at h
  have h' := congrArg (fun z : t.Plus ↦ z.1) (injective_algebraMap h)
  refine Subtype.ext (funext fun n ↦ ?_)
  have hn := congrFun h' n
  simp only [Plus.mul_val] at hn
  simp only [ofDiv_val]
  rw [div_eq_div_iff (val_ne_zero_of_mem b.2 n) (val_ne_zero_of_mem b'.2 n)]
  linear_combination hn

def ofFrac (q : FractionRing t.Plus) : t.Fam :=
  ofDiv (IsLocalization.mk'_surjective (nonZeroDivisors t.Plus) q).choose.1
    (IsLocalization.mk'_surjective (nonZeroDivisors t.Plus) q).choose.2

theorem ofFrac_mk' (a : t.Plus) (b : nonZeroDivisors t.Plus) :
    ofFrac (IsLocalization.mk' (FractionRing t.Plus) a b) = ofDiv a b :=
  ofDiv_eq_ofDiv (IsLocalization.mk'_surjective (nonZeroDivisors t.Plus)
    (IsLocalization.mk' (FractionRing t.Plus) a b)).choose_spec

variable (t) in

def equivFrac : t.Fam ≃ FractionRing t.Plus where
  toFun := toFrac
  invFun := ofFrac
  left_inv x := by
    rw [toFrac, ofFrac_mk']
    refine Subtype.ext (funext fun n ↦ ?_)
    change (Plus.unif t).1 n ^ _ * x.1 n / (Plus.unif t ^ _).1 n = x.1 n
    have := Plus.unif_val_ne_zero (t := t) n
    rw [Plus.pow_val]
    field_simp
    ring
  right_inv q := by
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors t.Plus) q
    rw [ofFrac_mk', toFrac, IsLocalization.mk'_eq_iff_eq]
    congr 1
    refine Subtype.ext (funext fun n ↦ ?_)
    change b.1.1 n * ((Plus.unif t).1 n ^ _ * (a.1 n / b.1.1 n)) = (Plus.unif t ^ _).1 n * a.1 n
    have := val_ne_zero_of_mem b.2 n
    rw [Plus.pow_val]
    field_simp
    ring

instance instField : Field t.Fam :=
  (equivFrac t).field

theorem equivFrac_mul (x y : t.Fam) : equivFrac t (x * y) = equivFrac t x * equivFrac t y :=
  (equivFrac t).apply_symm_apply _

theorem equivFrac_add (x y : t.Fam) : equivFrac t (x + y) = equivFrac t x + equivFrac t y :=
  (equivFrac t).apply_symm_apply _

theorem equivFrac_zero : equivFrac t (0 : t.Fam) = 0 :=
  (equivFrac t).apply_symm_apply _

theorem equivFrac_one : equivFrac t (1 : t.Fam) = 1 :=
  (equivFrac t).apply_symm_apply _

theorem equivFrac_toFam (a : t.Plus) :
    equivFrac t a.toFam = algebraMap t.Plus (FractionRing t.Plus) a := by
  show toFrac a.toFam = _
  rw [toFrac_eq a.toFam 0 (by simpa using a.nrm_le 0), ← IsLocalization.mk'_one (M := nonZeroDivisors t.Plus)]
  congr 1
  refine Subtype.ext (funext fun n ↦ ?_)
  change (Plus.unif t).1 n ^ 0 * a.1 n = a.1 n
  simp

theorem mul_val (x y : t.Fam) (n : ℕ) : (x * y).1 n = x.1 n * y.1 n := by
  let xy : t.Fam := ⟨fun n ↦ x.1 n * y.1 n, fun n ↦ ⟨mul_mem (x.mem n) (y.mem n),
    by rw [t.N_mul, x.N_eq, y.N_eq]⟩⟩
  suffices h : x * y = xy by rw [h]
  apply (equivFrac t).injective
  rw [equivFrac_mul]
  obtain ⟨mx, hmx⟩ := exists_scale x
  obtain ⟨my, hmy⟩ := exists_scale y
  have hxy : t.value 0 ^ (mx + my) * nrm K (xy.1 0) ≤ 1 := by
    show t.value 0 ^ (mx + my) * nrm K (x.1 0 * y.1 0) ≤ 1
    rw [nrm_mul, pow_add]
    calc t.value 0 ^ mx * t.value 0 ^ my * (nrm K (x.1 0) * nrm K (y.1 0)) =
        (t.value 0 ^ mx * nrm K (x.1 0)) * (t.value 0 ^ my * nrm K (y.1 0)) := by ring
      _ ≤ 1 * 1 := mul_le_mul hmx hmy (mul_nonneg (pow_nonneg (t.value_pos 0).le _) (nrm_nonneg _))
          zero_le_one
      _ = 1 := one_mul 1
  show toFrac x * toFrac y = toFrac xy
  rw [toFrac_eq x mx hmx, toFrac_eq y my hmy, toFrac_eq xy (mx + my) hxy,
    ← IsLocalization.mk'_mul]
  congr 1
  · refine Subtype.ext (funext fun n ↦ ?_)
    change (Plus.unif t).1 n ^ mx * x.1 n * ((Plus.unif t).1 n ^ my * y.1 n) =
      (Plus.unif t).1 n ^ (mx + my) * (x.1 n * y.1 n)
    ring
  · exact Subtype.ext (pow_add _ _ _).symm

@[simp]
theorem zero_val (n : ℕ) : (0 : t.Fam).1 n = 0 := by
  have : (0 : t.Fam) = (0 : t.Plus).toFam := by
    apply (equivFrac t).injective
    rw [equivFrac_zero, equivFrac_toFam, map_zero]
  rw [this]; rfl

@[simp]
theorem one_val (n : ℕ) : (1 : t.Fam).1 n = 1 := by
  have : (1 : t.Fam) = (1 : t.Plus).toFam := by
    apply (equivFrac t).injective
    rw [equivFrac_one, equivFrac_toFam, map_one]
  rw [this]; rfl

theorem toFam_add (a b : t.Plus) : (a + b).toFam = a.toFam + b.toFam := by
  apply (equivFrac t).injective
  rw [equivFrac_add, equivFrac_toFam, equivFrac_toFam, equivFrac_toFam, map_add]

theorem toFam_mul (a b : t.Plus) : (a * b).toFam = a.toFam * b.toFam :=
  Subtype.ext (funext fun n ↦ by rw [mul_val]; rfl)

theorem eq_zero_iff (x : t.Fam) : x = 0 ↔ x.1 0 = 0 := by
  constructor
  · rintro rfl; exact zero_val 0
  · intro h
    exact Subtype.ext (funext fun n ↦ by rw [zero_val]; exact (val_eq_zero_iff x n).mpr h)

theorem inv_val (x : t.Fam) (n : ℕ) : x⁻¹.1 n = (x.1 n)⁻¹ := by
  by_cases hx : x = 0
  · subst hx; simp
  have hxn : ∀ n, x.1 n ≠ 0 := fun n ↦ by
    rw [Ne, val_eq_zero_iff, ← eq_zero_iff]; exact hx
  let y : t.Fam := ⟨fun n ↦ (x.1 n)⁻¹, fun n ↦ ⟨inv_mem (x.mem n), by rw [t.N_inv, x.N_eq]⟩⟩
  have hxy : x * y = 1 := Subtype.ext (funext fun n ↦ by
    rw [mul_val, one_val]; exact mul_inv_cancel₀ (hxn n))
  rw [inv_eq_of_mul_eq_one_right hxy]

end Fam

end Fam

end NormTower

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}

namespace NormTower

variable (t : NormTower K Ω p)

namespace Plus

variable {t}

theorem sub_cong (x y : t.Plus) (n : ℕ) : nrm K ((x - y).1 n - (x.1 n - y.1 n)) ≤ t.ρ := by
  rw [show x - y = x + -y from sub_eq_add_neg x y]
  have h1 := add_cong x (-y) n
  have h2 := neg_cong y n
  have e : (x + -y).1 n - (x.1 n - y.1 n) =
      ((x + -y).1 n - (x.1 n + (-y).1 n)) + ((-y).1 n - -y.1 n) := by ring
  rw [e]
  exact nrm_add_le_of_le h1 h2

theorem exists_le_D (M : ℕ) : ∃ j, M ≤ t.D 0 j := by
  obtain ⟨j, hj⟩ := t.exists_le_cnt 0 M
  refine ⟨j, hj.trans ?_⟩
  clear hj
  induction j with
  | zero => simp [cnt, D]
  | succ j ih =>
    rw [cnt_succ, D_succ]
    split_ifs with hk
    · have h2 : 2 ≤ p ^ t.k (0 + j) := (t.prime.two_le).trans (Nat.le_self_pow hk _)
      have := t.D_pos 0 j
      nlinarith
    · have := Nat.one_le_pow (t.k (0 + j)) p t.prime.pos
      nlinarith

end Plus

namespace Fam

variable {t}

theorem eq_scalePlus_mul_inv (x : t.Fam) (m : ℕ) (h : t.value 0 ^ m * nrm K (x.1 0) ≤ 1) :
    x = (scalePlus x m h).toFam * ((Plus.unif t ^ m).toFam)⁻¹ := by
  refine Subtype.ext (funext fun n ↦ ?_)
  rw [mul_val, inv_val]
  change x.1 n = (Plus.unif t).1 n ^ m * x.1 n * ((Plus.unif t ^ m).1 n)⁻¹
  rw [Plus.pow_val]
  have := Plus.unif_val_ne_zero (t := t) n
  field_simp

theorem nrm_add_val_zero_le (x y : t.Fam) :
    nrm K ((x + y).1 0) ≤ max (nrm K (x.1 0)) (nrm K (y.1 0)) := by
  obtain ⟨mx, hmx⟩ := exists_scale x
  obtain ⟨my, hmy⟩ := exists_scale y
  set m := max mx my
  have hv0 := t.value_pos 0
  have hv1 := (t.value_lt_one 0).le
  have hm : ∀ {z : t.Fam} {mz : ℕ}, mz ≤ m → t.value 0 ^ mz * nrm K (z.1 0) ≤ 1 →
      t.value 0 ^ m * nrm K (z.1 0) ≤ 1 := fun hle hz ↦
    (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hv0.le hv1 hle) (nrm_nonneg _)).trans hz
  have hx := hm (le_max_left _ _) hmx
  have hy := hm (le_max_right _ _) hmy
  set a := scalePlus x m hx
  set b := scalePlus y m hy
  set w := (Plus.unif t ^ m).toFam
  have hxy : x + y = (a + b).toFam * w⁻¹ := by
    conv_lhs => rw [eq_scalePlus_mul_inv x m hx, eq_scalePlus_mul_inv y m hy]
    rw [toFam_add]; ring
  have hw : nrm K (w⁻¹.1 0) = (t.value 0 ^ m)⁻¹ := by
    rw [inv_val, nrm_inv]
    change (nrm K ((Plus.unif t ^ m).1 0))⁻¹ = _
    rw [Plus.pow_val, nrm_pow, Plus.nrm_unif]
  have ha : nrm K (x.1 0) = nrm K (a.1 0) * (t.value 0 ^ m)⁻¹ := by
    conv_lhs => rw [eq_scalePlus_mul_inv x m hx]
    rw [mul_val, nrm_mul, hw]; rfl
  have hb : nrm K (y.1 0) = nrm K (b.1 0) * (t.value 0 ^ m)⁻¹ := by
    conv_lhs => rw [eq_scalePlus_mul_inv y m hy]
    rw [mul_val, nrm_mul, hw]; rfl
  rw [hxy, mul_val, nrm_mul, hw, ha, hb, ← max_mul_of_nonneg _ _ (inv_nonneg.mpr (pow_nonneg hv0.le _))]
  exact mul_le_mul_of_nonneg_right (Plus.nrm_add_val_zero_le a b) (inv_nonneg.mpr (pow_nonneg hv0.le _))

variable (t) in

def abv : AbsoluteValue t.Fam ℝ where
  toFun x := nrm K (x.1 0)
  map_mul' x y := by simp only [mul_val, nrm_mul]
  nonneg' x := nrm_nonneg _
  eq_zero' x := by rw [nrm_eq_zero, ← eq_zero_iff]
  add_le' x y := (nrm_add_val_zero_le x y).trans (max_le_add_of_nonneg (nrm_nonneg _) (nrm_nonneg _))

theorem abv_add_le_max (x y : t.Fam) : abv t (x + y) ≤ max (abv t x) (abv t y) :=
  nrm_add_val_zero_le x y

theorem abv_unif : abv t (Plus.unif t).toFam = t.value 0 :=
  Plus.nrm_unif 0

end Fam

namespace Fam

variable {t}

theorem toFam_zero : (0 : t.Plus).toFam = 0 := Subtype.ext (funext fun n ↦ by rw [zero_val]; rfl)

theorem toFam_one : (1 : t.Plus).toFam = 1 := Subtype.ext (funext fun n ↦ by rw [one_val]; rfl)

variable (t) in

def toFamHom : t.Plus →+* t.Fam where
  toFun := Plus.toFam
  map_one' := toFam_one
  map_mul' := toFam_mul
  map_zero' := toFam_zero
  map_add' := toFam_add

theorem toFam_sub (a b : t.Plus) : (a - b).toFam = a.toFam - b.toFam :=
  map_sub (toFamHom t) a b

theorem natCast_p : ((p : ℕ) : t.Fam) = 0 := by
  rw [← map_natCast (toFamHom t), Plus.natCast_p, map_zero]

instance charP : CharP t.Fam p :=
  (CharP.charP_iff_prime_eq_zero t.prime).mpr natCast_p

instance instNormedField : NormedField t.Fam :=
  (abv t).toNormedField

theorem norm_def (x : t.Fam) : ‖x‖ = nrm K (x.1 0) := rfl

instance instIsUltrametricDist : IsUltrametricDist t.Fam :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm abv_add_le_max

theorem norm_unif : ‖(Plus.unif t).toFam‖ = t.value 0 := abv_unif

instance instNontriviallyNormedField : NontriviallyNormedField t.Fam where
  non_trivial := ⟨((Plus.unif t).toFam)⁻¹, by
    rw [norm_inv, norm_unif]; exact one_lt_inv_iff₀.mpr ⟨t.value_pos 0, t.value_lt_one 0⟩⟩

def intFamSet : Set (ℕ → Ω) := {z | t.IsIntFam z}

variable (t) in
theorem isCompact_intFamSet : IsCompact (intFamSet (t := t)) := by
  have hP : IsCompact {z : ℕ → Ω | ∀ n, z n ∈ t.intSet n} :=
    isCompact_pi_infinite t.isCompact_intSet
  have hC : IsClosed {z : ℕ → Ω | ∀ n, nrm K (t.N n (z (n + 1)) - z n) ≤ 0} := by
    have e : {z : ℕ → Ω | ∀ n, nrm K (t.N n (z (n + 1)) - z n) ≤ 0} =
        ⋂ n, {z : ℕ → Ω | nrm K (t.N n (z (n + 1)) - z n) ≤ 0} := by ext; simp
    rw [e]
    exact isClosed_iInter fun n ↦ isClosed_le ((continuous_nrm K Ω).comp
      (((t.continuous_N n).comp (continuous_apply _)).sub (continuous_apply _))) continuous_const
  convert hP.inter_right hC using 1
  ext z
  simp only [intFamSet, Set.mem_ofPred_eq, Set.mem_inter_iff, IsIntFam, IsFam, intSet]
  constructor
  · rintro ⟨h, h1⟩
    exact ⟨fun n ↦ ⟨(h n).1, h1 n⟩, fun n ↦ by rw [(h n).2, sub_self, nrm_zero]⟩
  · rintro ⟨h, h1⟩
    refine ⟨fun n ↦ ⟨(h n).1, ?_⟩, fun n ↦ (h n).2⟩
    rw [← sub_eq_zero, ← nrm_eq_zero (K := K)]
    exact le_antisymm (h1 n) (nrm_nonneg _)

open Classical in

def ofSeq (z : ℕ → Ω) : t.Fam :=
  if h : t.IsFam z then ⟨z, h⟩ else 0

theorem ofSeq_of_isFam {z : ℕ → Ω} (h : t.IsFam z) : ofSeq z = ⟨z, h⟩ := by
  unfold ofSeq; exact dif_pos h

variable (t) in

theorem isCompact_closedBall : IsCompact (Metric.closedBall (0 : t.Fam) 1) := by
  have himage : Metric.closedBall (0 : t.Fam) 1 = ofSeq '' intFamSet (t := t) := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_image]
    constructor
    · intro hx
      exact ⟨x.1, isIntFam_of_nrm_le hx, ofSeq_of_isFam x.2⟩
    · rintro ⟨z, hz, rfl⟩
      rw [ofSeq_of_isFam hz.1]
      exact hz.2 0
  rw [himage]
  refine (isCompact_intFamSet t).image_of_continuousOn fun z₀ hz₀ ↦ ?_
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  set ρ' := max t.ρ (1 / 2)
  have hρ'1 : ρ' < 1 := max_lt t.ρ_lt_one (by norm_num)
  have hρ'0 : 0 < ρ' := lt_max_of_lt_right (by norm_num)
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hρ'1
  obtain ⟨j, hj⟩ := Plus.exists_le_D (t := t) M
  have hU : {z : ℕ → Ω | nrm K (z j - z₀ j) < ρ'} ∈ 𝓝[intFamSet (t := t)] z₀ := by
    refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds ?_ ?_)
    · exact isOpen_lt ((continuous_nrm K Ω).comp ((continuous_apply j).sub continuous_const))
        continuous_const
    · show nrm K (z₀ j - z₀ j) < ρ'
      rw [sub_self, nrm_zero]; exact hρ'0
  filter_upwards [hU, self_mem_nhdsWithin] with z hz hzI
  let a : t.Plus := ⟨z, hzI⟩
  let b : t.Plus := ⟨z₀, hz₀⟩
  have ha : ofSeq z = a.toFam := ofSeq_of_isFam hzI.1
  have hb : ofSeq z₀ = b.toFam := ofSeq_of_isFam hz₀.1
  rw [dist_eq_norm, ha, hb, ← toFam_sub, norm_def]

  have h1 : nrm K ((a - b).1 j) ≤ ρ' := by
    have e : (a - b).1 j = ((a - b).1 j - (a.1 j - b.1 j)) + (a.1 j - b.1 j) := by ring
    rw [e]
    exact nrm_add_le_of_le ((Plus.sub_cong a b j).trans (le_max_left _ _)) hz.le
  calc nrm K ((a - b).toFam.1 0) = nrm K ((a - b).1 j) ^ t.D 0 j := Plus.nrm_val_zero (a - b) j
    _ ≤ ρ' ^ t.D 0 j := pow_le_pow_left₀ (nrm_nonneg _) h1 _
    _ ≤ ρ' ^ M := pow_le_pow_of_le_one hρ'0.le hρ'1.le hj
    _ < ε := hM

instance instProperSpace : ProperSpace t.Fam := by
  haveI : WeaklyLocallyCompactSpace t.Fam := ⟨fun x ↦ ⟨Metric.closedBall x 1, by
    have : Metric.closedBall x 1 = (fun y ↦ x + y) '' Metric.closedBall 0 1 := by
      ext y
      simp only [Set.mem_image, Metric.mem_closedBall, dist_eq_norm]
      constructor
      · intro h; exact ⟨y - x, by simpa using h, by ring⟩
      · rintro ⟨z, hz, rfl⟩; simpa using hz
    rw [this]
    exact (isCompact_closedBall t).image (continuous_const.add continuous_id),
    Metric.closedBall_mem_nhds x one_pos⟩⟩
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace t.Fam

instance instValuativeRel : ValuativeRel t.Fam :=
  ValuativeRel.ofValuation (NormedField.valuation (K := t.Fam))

theorem vle_iff_norm_le (x y : t.Fam) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe

instance instCompatible : (NormedField.valuation (K := t.Fam)).Compatible :=
  Valuation.Compatible.ofValuation _

instance instIsValuativeTopology : IsValuativeTopology t.Fam := by
  let : Valued t.Fam NNReal := NormedField.toValued
  have : (Valued.v : Valuation t.Fam NNReal).Compatible := instCompatible
  exact GroundTheory.LocalField.isValuativeTopology_of_valued

instance instIsNontrivial : IsNontrivial t.Fam := by
  refine ⟨⟨valuation t.Fam (Plus.unif t).toFam, ?_, ?_⟩⟩
  · rw [ne_eq, Valuation.zero_iff, ← norm_eq_zero, norm_unif]
    exact (t.value_pos 0).ne'
  · intro h
    have h2 : (1 : t.Fam) ≤ᵥ (Plus.unif t).toFam := by
      rw [Valuation.vle_iff_le (valuation t.Fam), h, map_one]
    rw [vle_iff_norm_le, norm_unif, norm_one] at h2
    exact absurd h2 (not_le.2 (t.value_lt_one 0))

instance instIsNonarchimedeanLocalField : IsNonarchimedeanLocalField t.Fam where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

end Fam

end NormTower

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

section GaloisAPF

variable {L : IntermediateField K Ω} [IsGalois K L]

theorem fixingSubgroup_normal_of_isGalois : L.fixingSubgroup.Normal :=
  (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance

instance upperSupFixing_normal (u : ℝ) : (upperSupFixing K Ω L u).Normal := by
  haveI := fixingSubgroup_normal_of_isGalois (L := L)
  exact Subgroup.sup_normal _ _

variable (hL : IsAPF K Ω L)
include hL


theorem isGalois_upperField (u : ℝ) : IsGalois K (upperField K Ω L u) := by
  rw [← InfiniteGalois.normal_iff_isGalois, fixingSubgroup_upperField hL]
  infer_instance

def upperFieldFG (u : ℝ) : FiniteGaloisIntermediateField K Ω :=
  @FiniteGaloisIntermediateField.mk K Ω _ _ _ (upperField K Ω L u) (finiteDimensional_upperField hL u)
    (isGalois_upperField hL u)

theorem upperFieldFG_coe (u : ℝ) : (upperFieldFG hL u : IntermediateField K Ω) = upperField K Ω L u :=
  rfl

theorem ker_restrictNormalHom_upperField (u : ℝ) :
    (AlgEquiv.restrictNormalHom (upperFieldFG hL u : IntermediateField K Ω)).ker =
      upperSupFixing K Ω L u := by
  rw [IntermediateField.restrictNormalHom_ker, upperFieldFG_coe, fixingSubgroup_upperField hL]

theorem upperRamificationGroup_upperField_eq_bot (u' : ℝ) :
    upperRamificationGroup K (upperFieldFG hL u' : IntermediateField K Ω) u' = ⊥ := by
  rw [← map_absUpper (upperFieldFG hL u') u', Subgroup.map_eq_bot_iff,
    ker_restrictNormalHom_upperField hL]
  exact absUpper_le_upperSupFixing u'

theorem upperIndex_upperField {u' w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ u') :
    upperIndex K (upperFieldFG hL u' : IntermediateField K Ω) w = apfIndex K Ω L w := by
  haveI := fixingSubgroup_normal_of_isGalois (L := L)
  rw [upperIndex, ← upperRamificationGroup_zero, ← map_absUpper (upperFieldFG hL u') w,
    ← map_absUpper (upperFieldFG hL u') 0, Subgroup.relIndex_map_map,
    ker_restrictNormalHom_upperField hL, apfIndex]
  have h1 : absUpper K Ω w ⊔ upperSupFixing K Ω L u' = upperSupFixing K Ω L w := by
    rw [upperSupFixing, upperSupFixing, ← sup_assoc,
      sup_eq_left.mpr (absUpper_antitone K Ω hw)]
  have h2 : absUpper K Ω 0 ⊔ upperSupFixing K Ω L u' = absUpper K Ω 0 ⊔ upperSupFixing K Ω L w := by
    rw [upperSupFixing, upperSupFixing, ← sup_assoc, ← sup_assoc,
      sup_eq_left.mpr (absUpper_antitone K Ω (hw0.trans hw)),
      sup_eq_left.mpr (absUpper_antitone K Ω hw0)]
  rw [h1, h2, Subgroup.relIndex_sup_right]

theorem ramificationIndex_upperField {u' : ℝ} (hu' : 0 ≤ u') :
    ramificationIndex K (upperFieldFG hL u' : IntermediateField K Ω) = apfIndex K Ω L u' := by
  rw [← upperIndex_upperField hL hu' le_rfl, upperIndex, upperRamificationGroup_upperField_eq_bot,
    Subgroup.relIndex_bot_left, card_lowerRamificationGroup_zero]

theorem herbrandPsi_upperField {u u' : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ u') :
    herbrandPsi K (upperFieldFG hL u' : IntermediateField K Ω) u = apfPsi K Ω L u := by
  rw [herbrandPsi_eq_integral hu0, apfPsi]
  refine intervalIntegral.integral_congr fun w hw ↦ ?_
  rw [Set.uIcc_of_le hu0] at hw
  simp only [upperIndex_upperField hL hw.1 (hw.2.trans hu)]

theorem exists_mem_upperField {x : Ω} (hx : x ∈ L) : ∃ u : ℝ, x ∈ upperField K Ω L u := by
  let M := FiniteGaloisIntermediateField.adjoin K ({x} : Set Ω)
  have hxM : x ∈ (M : IntermediateField K Ω) :=
    FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set Ω) rfl
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K (M : IntermediateField K Ω)
  refine ⟨herbrandPhi K (M : IntermediateField K Ω) N, ?_⟩
  rw [upperField, IntermediateField.mem_fixedField_iff]
  intro σ hσ

  let S : Subgroup Gal(Ω/K) := (IntermediateField.adjoin K ({x} : Set Ω)).fixingSubgroup
  have hS : ∀ τ ∈ S, τ x = x := fun τ hτ ↦
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x (IntermediateField.subset_adjoin K _ rfl)
  have hup : absUpper K Ω (herbrandPhi K (M : IntermediateField K Ω) N) ≤ S := by
    intro τ hτ
    have h1 := hτ M
    rw [upperRamificationGroup_herbrandPhi, lowerRamificationGroupReal_natCast, hN N le_rfl,
      Subgroup.mem_bot] at h1
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hyM : y ∈ (M : IntermediateField K Ω) :=
      (IntermediateField.le_normalClosure _) hy
    have := congrArg (fun f ↦ ((f ⟨y, hyM⟩ : M) : Ω)) h1
    simpa [AlgEquiv.restrictNormalHom_apply] using this
  have hfix : L.fixingSubgroup ≤ S := by
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hyL : y ∈ L := IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx) hy
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ y hyL
  exact hS σ (sup_le hup hfix hσ)

end GaloisAPF

section Tower

variable {L : IntermediateField K Ω} [IsGalois K L] (hL : IsAPF K Ω L)
include hL

theorem map_upperSupFixing {u u' : ℝ} :
    (upperSupFixing K Ω L u).map
        (AlgEquiv.restrictNormalHom (upperFieldFG hL u' : IntermediateField K Ω)) =
      upperRamificationGroup K (upperFieldFG hL u' : IntermediateField K Ω) u := by
  rw [upperSupFixing, Subgroup.map_sup, map_absUpper]
  have : L.fixingSubgroup.map
      (AlgEquiv.restrictNormalHom (upperFieldFG hL u' : IntermediateField K Ω)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, ker_restrictNormalHom_upperField hL]
    exact fixingSubgroup_le_upperSupFixing u'
  rw [this, sup_bot_eq]

theorem apfPsi_le_add {u u' : ℝ} (h : u ≤ u') :
    apfPsi K Ω L u' ≤ apfPsi K Ω L u + (u' - u) * apfIndex K Ω L u' := by
  rw [apfPsi, apfPsi, ← intervalIntegral.integral_add_adjacent_intervals (b := u)
    (intervalIntegrable_apfIndex hL _ _) (intervalIntegrable_apfIndex hL _ _)]
  gcongr
  calc ∫ w in u..u', (apfIndex K Ω L w : ℝ) ≤ ∫ _ in u..u', (apfIndex K Ω L u' : ℝ) :=
        intervalIntegral.integral_mono_on h (intervalIntegrable_apfIndex hL _ _)
          intervalIntegrable_const fun w hw ↦ by exact_mod_cast apfIndex_mono hL hw.2
    _ = (u' - u) * apfIndex K Ω L u' := by simp

end Tower

section Construction

variable {L : IntermediateField K Ω} [IsGalois K L]

structure APFData (L : IntermediateField K Ω) where
  apf : IsAPF K Ω L
  c : ℝ
  c_pos : 0 < c
  u₀ : ℝ
  one_le_u₀ : 1 ≤ u₀
  le_psi : ∀ u, u₀ ≤ u → c * apfIndex K Ω L u ≤ apfPsi K Ω L u

theorem IsStrictlyAPF.nonempty_apfData (h : IsStrictlyAPF K Ω L) : Nonempty (APFData L) := by
  obtain ⟨hapf, c, hc, hev⟩ := h
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp hev
  exact ⟨⟨hapf, c, hc, max U 1, le_max_right _ _, fun u hu ↦ hU u ((le_max_left _ _).trans hu)⟩⟩

namespace APFData

variable (d : APFData L)

def u (n : ℕ) : ℝ := d.u₀ + n * (d.c / 2)

theorem u_succ (n : ℕ) : d.u (n + 1) = d.u n + d.c / 2 := by
  simp only [u]; push_cast; ring

theorem one_le_u (n : ℕ) : 1 ≤ d.u n := by
  have := d.one_le_u₀
  have : 0 ≤ (n : ℝ) * (d.c / 2) := mul_nonneg n.cast_nonneg (by linarith [d.c_pos])
  simp only [u]; linarith

theorem u_nonneg (n : ℕ) : 0 ≤ d.u n := zero_le_one.trans (d.one_le_u n)

theorem u_mono : Monotone d.u := by
  intro m n h
  simp only [u]
  have : (m : ℝ) ≤ n := by exact_mod_cast h
  nlinarith [d.c_pos]

theorem exists_le_u (v : ℝ) : ∃ n, v ≤ d.u n := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((v - d.u₀) / (d.c / 2))
  refine ⟨n, ?_⟩
  have hc : 0 < d.c / 2 := by linarith [d.c_pos]
  rw [div_lt_iff₀ hc] at hn
  simp only [u]; linarith

def F (n : ℕ) : FiniteGaloisIntermediateField K Ω := upperFieldFG d.apf (d.u n)

def H (n : ℕ) : Subgroup Gal((d.F (n + 1) : IntermediateField K Ω)/K) :=
  upperRamificationGroup K (d.F (n + 1) : IntermediateField K Ω) (d.u n)

theorem exists_lift (n : ℕ) (g : d.H n) :
    ∃ σ ∈ absUpper K Ω (d.u n),
      AlgEquiv.restrictNormalHom (d.F (n + 1) : IntermediateField K Ω) σ = g := by
  have : (g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ∈
      upperRamificationGroup K (d.F (n + 1) : IntermediateField K Ω) (d.u n) := g.2
  rw [← map_absUpper (d.F (n + 1)) (d.u n)] at this
  exact this

def lift (n : ℕ) (g : d.H n) : Gal(Ω/K) := (d.exists_lift n g).choose

theorem lift_mem (n : ℕ) (g : d.H n) : d.lift n g ∈ absUpper K Ω (d.u n) :=
  (d.exists_lift n g).choose_spec.1

theorem restrict_lift (n : ℕ) (g : d.H n) :
    AlgEquiv.restrictNormalHom (d.F (n + 1) : IntermediateField K Ω) (d.lift n g) = g :=
  (d.exists_lift n g).choose_spec.2

theorem lift_injective (n : ℕ) : Function.Injective (d.lift n) := by
  intro g g' h
  have := congrArg (AlgEquiv.restrictNormalHom (d.F (n + 1) : IntermediateField K Ω)) h
  rw [restrict_lift, restrict_lift] at this
  exact Subtype.ext this

instance (n : ℕ) : Fintype (d.H n) := Fintype.ofFinite _

open Classical in

def T (n : ℕ) : Finset Gal(Ω/K) := Finset.univ.image (d.lift n)

theorem card_alt (n : ℕ) : (d.T n).card = Nat.card (d.H n) := by
  classical
  rw [T, Finset.card_image_of_injective _ (d.lift_injective n), Finset.card_univ,
    Nat.card_eq_fintype_card]

theorem lift_apply (n : ℕ) (g : d.H n) {y : Ω} (hy : y ∈ (d.F (n + 1) : IntermediateField K Ω)) :
    d.lift n g y = ((g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ⟨y, hy⟩ : Ω) := by
  rw [← d.restrict_lift n g, AlgEquiv.restrictNormalHom_apply]

theorem psi_ge (n : ℕ) : d.c / 2 * apfIndex K Ω L (d.u (n + 1)) ≤ apfPsi K Ω L (d.u n) := by
  have h1 := d.le_psi (d.u (n + 1)) (by simp only [u]; have := d.c_pos; push_cast; nlinarith)
  have h2 := apfPsi_le_add d.apf (d.u_mono (Nat.le_succ n))
  rw [d.u_succ] at h1 h2 ⊢
  have : d.u n + d.c / 2 - d.u n = d.c / 2 := by ring
  rw [this] at h2
  linarith

end APFData

end Construction

omit [IsGalois K Ω] in
theorem exists_nrm_eq_unifNrm_zpow (F : IntermediateField K Ω) [FiniteDimensional K F] {y : Ω}
    (hy : y ∈ F) (hy0 : y ≠ 0) : ∃ j : ℤ, nrm K y = unifNrm F ^ j := by
  obtain ⟨z, rfl⟩ : ∃ z : F, (z : Ω) = y := ⟨⟨y, hy⟩, rfl⟩
  have hz : z ≠ 0 := by
    rintro rfl; exact hy0 (ZeroMemClass.coe_zero _)
  exact ⟨_, nrm_eq_unifNrm_zpow F hz⟩

omit [IsGalois K Ω] in
theorem exists_nrm_eq_unifNrm (F : IntermediateField K Ω) [FiniteDimensional K F] :
    ∃ π ∈ F, nrm K π = unifNrm F :=
  ⟨_, SetLike.coe_mem ((unif F : 𝒪[F]) : F), rfl⟩

namespace APFData

variable {L : IntermediateField K Ω} [IsGalois K L] (d : APFData L)

theorem psi_pos (n : ℕ) : 0 < apfPsi K Ω L (d.u n) := by
  have h := d.psi_ge n
  have hI : (0 : ℝ) < apfIndex K Ω L (d.u (n + 1)) := by exact_mod_cast apfIndex_pos d.apf _
  have hc : 0 < d.c / 2 := by linarith [d.c_pos]
  nlinarith

theorem herbrandPsi_F (n : ℕ) :
    herbrandPsi K (d.F (n + 1) : IntermediateField K Ω) (d.u n) = apfPsi K Ω L (d.u n) :=
  herbrandPsi_upperField d.apf (d.u_nonneg n) (d.u_mono (Nat.le_succ n))

def i (n : ℕ) : ℕ := (⌈apfPsi K Ω L (d.u n)⌉).toNat

theorem i_cast (n : ℕ) : ((d.i n : ℕ) : ℤ) = ⌈apfPsi K Ω L (d.u n)⌉ :=
  Int.toNat_of_nonneg (Int.ceil_nonneg (d.psi_pos n).le)

theorem H_eq (n : ℕ) : d.H n = lowerRamificationGroup K (d.F (n + 1) : IntermediateField K Ω) (d.i n) := by
  rw [H, upperRamificationGroup, lowerRamificationGroupReal, d.herbrandPsi_F, d.i_cast]

theorem one_le_i (n : ℕ) : 1 ≤ d.i n := by
  have h := d.i_cast n
  have : (1 : ℤ) ≤ ⌈apfPsi K Ω L (d.u n)⌉ := Int.one_le_ceil_iff.mpr (d.psi_pos n)
  omega

theorem isPGroup_H (n : ℕ) : IsPGroup (ringChar 𝓀[K]) (d.H n) := by
  refine (isPGroup_lowerRamificationGroup_one K (d.F (n + 1) : IntermediateField K Ω)).to_le ?_
  rw [d.H_eq]
  exact lowerRamificationGroup_antitone K _ (by exact_mod_cast d.one_le_i n)

instance fact_prime : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] _⟩

theorem exists_card_H (n : ℕ) : ∃ k : ℕ, Nat.card (d.H n) = ringChar 𝓀[K] ^ k :=
  IsPGroup.iff_card.mp (d.isPGroup_H n)

def k (n : ℕ) : ℕ := (d.exists_card_H n).choose

theorem card_H (n : ℕ) : Nat.card (d.H n) = ringChar 𝓀[K] ^ d.k n :=
  (d.exists_card_H n).choose_spec

theorem restrict_mem_H (n : ℕ) {τ : Gal(Ω/K)} (hτ : τ ∈ upperSupFixing K Ω L (d.u n)) :
    AlgEquiv.restrictNormalHom (d.F (n + 1) : IntermediateField K Ω) τ ∈ d.H n := by
  show _ ∈ upperRamificationGroup K (upperFieldFG d.apf (d.u (n + 1)) : IntermediateField K Ω) (d.u n)
  rw [← map_upperSupFixing d.apf]
  exact Subgroup.mem_map_of_mem _ hτ

theorem prod_mem (n : ℕ) {y : Ω} (hy : y ∈ (d.F (n + 1) : IntermediateField K Ω)) :
    (∏ σ ∈ d.T n, σ y) ∈ (d.F n : IntermediateField K Ω) := by
  classical
  have e : (∏ σ ∈ d.T n, σ y) =
      ∏ g : d.H n, ((g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ⟨y, hy⟩ : Ω) := by
    rw [T, Finset.prod_image (fun g _ g' _ h ↦ d.lift_injective n h)]
    exact Finset.prod_congr rfl fun g _ ↦ d.lift_apply n g hy
  rw [e]
  show _ ∈ upperField K Ω L (d.u n)
  rw [upperField, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  rw [map_prod]
  let h : d.H n := ⟨_, d.restrict_mem_H n hτ⟩
  have hτg : ∀ g : d.H n, τ ((g : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ⟨y, hy⟩ : Ω) =
      (((h * g : d.H n) : Gal((d.F (n + 1) : IntermediateField K Ω)/K)) ⟨y, hy⟩ : Ω) := by
    intro g
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply, ← AlgEquiv.restrictNormalHom_apply]
  simp_rw [hτg]
  exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ fun g ↦ rfl

theorem step (n : ℕ) {σ : Gal(Ω/K)} (hσ : σ ∈ d.T n) {x : Ω}
    (hx : x ∈ (d.F (n + 1) : IntermediateField K Ω)) :
    nrm K (σ x - x) ≤ baseUnifNrm K Ω ^ (d.c / 2) * nrm K x := by
  classical
  simp only [T, Finset.mem_image, Finset.mem_univ, true_and] at hσ
  obtain ⟨g, rfl⟩ := hσ
  set F := (d.F (n + 1) : IntermediateField K Ω)
  have hg : AlgEquiv.restrictNormalHom F (d.lift n g) ∈ lowerRamificationGroup K F (d.i n) := by
    rw [d.restrict_lift, ← d.H_eq]; exact g.2
  have h1 := nrm_sub_le_of_mem_lowerRamificationGroup F hg ⟨x, hx⟩
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (nrm_nonneg _))

  set r := unifNrm F
  set e := ramificationIndex K F
  have hr0 := unifNrm_pos F
  have hr1 := unifNrm_lt_one F
  have hre : r ^ e = baseUnifNrm K Ω := unifNrm_pow_ramificationIndex F
  have he : (e : ℝ) = apfIndex K Ω L (d.u (n + 1)) := by
    exact_mod_cast ramificationIndex_upperField d.apf (d.u_nonneg (n + 1))
  have hi : d.c / 2 * e ≤ d.i n := by
    rw [he]
    refine (d.psi_ge n).trans ?_
    have := d.i_cast n
    have h2 : apfPsi K Ω L (d.u n) ≤ (⌈apfPsi K Ω L (d.u n)⌉ : ℝ) := Int.le_ceil _
    rw [← this] at h2
    exact_mod_cast h2
  rw [← hre, ← Real.rpow_natCast r e, ← Real.rpow_mul hr0.le, ← Real.rpow_natCast r (d.i n)]
  exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le (by linarith)

theorem value_succ (n : ℕ) :
    unifNrm (d.F (n + 1) : IntermediateField K Ω) ^ (ringChar 𝓀[K] ^ d.k n) =
      unifNrm (d.F n : IntermediateField K Ω) := by
  set F := (d.F (n + 1) : IntermediateField K Ω)
  have he1 : ramificationIndex K F = apfIndex K Ω L (d.u (n + 1)) :=
    ramificationIndex_upperField d.apf (d.u_nonneg (n + 1))
  have he0 : ramificationIndex K (d.F n : IntermediateField K Ω) = apfIndex K Ω L (d.u n) :=
    ramificationIndex_upperField d.apf (d.u_nonneg n)
  have hidx : upperIndex K F (d.u n) = apfIndex K Ω L (d.u n) :=
    upperIndex_upperField d.apf (d.u_nonneg n) (d.u_mono (Nat.le_succ n))

  have hmul : ramificationIndex K F = ramificationIndex K (d.F n : IntermediateField K Ω) *
      Nat.card (d.H n) := by
    rw [he0, ← hidx, ← card_lowerRamificationGroup_zero, upperIndex]
    have hle : d.H n ≤ lowerRamificationGroup K F 0 := by
      rw [← upperRamificationGroup_zero]
      exact upperRamificationGroup_antitone K F (d.u_nonneg n)
    have := relIndex_mul_card_inf (d.H n) (lowerRamificationGroup K F 0)
    rw [inf_eq_left.mpr hle] at this
    exact this.symm
  have h1 := unifNrm_pow_ramificationIndex F
  have h0 := unifNrm_pow_ramificationIndex (d.F n : IntermediateField K Ω)
  rw [hmul, mul_comm, pow_mul, ← h0, d.card_H] at h1
  have hpos : ramificationIndex K (d.F n : IntermediateField K Ω) ≠ 0 :=
    (ramificationIndex_pos K _).ne'
  exact (pow_left_inj₀ (pow_nonneg (unifNrm_pos F).le _) (unifNrm_pos _).le hpos).mp h1

theorem F_succ_le_of_k_eq_zero {m : ℕ} (hk : d.k m = 0) :
    (d.F (m + 1) : IntermediateField K Ω) ≤ d.F m := by
  have hH : d.H m = ⊥ := by
    rw [← Subgroup.card_eq_one, d.card_H, hk, pow_zero]
  intro x hx
  show x ∈ upperField K Ω L (d.u m)
  rw [upperField, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  have h := d.restrict_mem_H m hτ
  rw [hH, Subgroup.mem_bot] at h
  have := congrArg (fun f ↦ ((f ⟨x, hx⟩ : (d.F (m + 1) : IntermediateField K Ω)) : Ω)) h
  simpa [AlgEquiv.restrictNormalHom_apply] using this


theorem frequently_ne_zero (hinf : ¬ FiniteDimensional K L) (n : ℕ) : ∃ m, n ≤ m ∧ d.k m ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hstab : ∀ j, (d.F (n + j) : IntermediateField K Ω) ≤ d.F n := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (d.F_succ_le_of_k_eq_zero (hcon (n + j) (by omega))).trans ih
  have hL : L ≤ d.F n := by
    intro x hx
    obtain ⟨v, hv⟩ := exists_mem_upperField d.apf hx
    obtain ⟨m, hm⟩ := d.exists_le_u v
    have : x ∈ (d.F (n + m) : IntermediateField K Ω) :=
      upperField_mono (hm.trans (d.u_mono (by omega))) hv
    exact hstab m this
  exact hinf (FiniteDimensional.of_injective (IntermediateField.inclusion hL).toLinearMap
    (IntermediateField.inclusion_injective hL))

omit [IsGalois K Ω] in
theorem nrm_ringChar_lt_one : nrm K ((ringChar 𝓀[K] : ℕ) : Ω) < 1 := by
  have h := CharZero.valuation_p_lt_one K (ringChar 𝓀[K])
  rw [nrm_lt_one_iff, ← map_natCast (algebraMap K Ω)]
  exact (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation Ω) _).mpr h

theorem value_zpow (n : ℕ) {y : Ω} (hy : y ∈ (d.F n : IntermediateField K Ω)) (hy0 : y ≠ 0) :
    ∃ j : ℤ, nrm K y = unifNrm (d.F n : IntermediateField K Ω) ^ j :=
  exists_nrm_eq_unifNrm_zpow _ hy hy0

theorem exists_value (n : ℕ) : ∃ π ∈ (d.F n : IntermediateField K Ω),
    nrm K π = unifNrm (d.F n : IntermediateField K Ω) :=
  exists_nrm_eq_unifNrm _

def tower (hinf : ¬ FiniteDimensional K L) : NormTower K Ω (ringChar 𝓀[K]) where
  E n := (d.F n : IntermediateField K Ω)
  mono _ _ h := upperField_mono (d.u_mono h)
  finiteDimensional _ := inferInstance
  T := d.T
  fix n σ hσ x hx := by
    classical
    simp only [T, Finset.mem_image, Finset.mem_univ, true_and] at hσ
    obtain ⟨g, rfl⟩ := hσ
    have h1 : d.lift n g ∈ (upperField K Ω L (d.u n)).fixingSubgroup := by
      rw [fixingSubgroup_upperField d.apf]
      exact absUpper_le_upperSupFixing _ (d.lift_mem n g)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp h1 x hx
  prod_mem n y hy := d.prod_mem n hy
  k := d.k
  card_alt n := (d.card_alt n).trans (d.card_H n)
  frequently_ne_zero := d.frequently_ne_zero hinf
  c := baseUnifNrm K Ω ^ (d.c / 2)
  c_nonneg := Real.rpow_nonneg baseUnifNrm_pos.le _
  c_lt_one := by
    refine Real.rpow_lt_one baseUnifNrm_pos.le ?_ (by linarith [d.c_pos])
    rw [← unifNrm_pow_ramificationIndex (d.F 0 : IntermediateField K Ω)]
    exact pow_lt_one₀ (unifNrm_pos _).le (unifNrm_lt_one _) (ramificationIndex_pos K _).ne'
  step n σ hσ x hx := d.step n hσ hx
  prime := Fact.out
  nrm_p_lt_one := nrm_ringChar_lt_one
  value n := unifNrm (d.F n : IntermediateField K Ω)
  value_pos n := unifNrm_pos _
  value_lt_one n := unifNrm_lt_one _
  exists_value n := d.exists_value n
  value_zpow n y hy hy0 := d.value_zpow n hy hy0
  value_succ n := d.value_succ n

end APFData

end GroundTheory.PAdicHodge
end
end
