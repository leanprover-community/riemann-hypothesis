import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec

section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

variable (k d) in

@[ext] structure COSub where

  sub : AddSubgroup (Fin d → k)
  isOpen : IsOpen (sub : Set (Fin d → k))
  isCompact : IsCompact (sub : Set (Fin d → k))

def gHom (g : GL (Fin d) k) : (Fin d → k) →+ (Fin d → k) :=
  (Matrix.mulVecLin (g : Matrix (Fin d) (Fin d) k)).toAddMonoidHom


def COSub.act (L : COSub k d) (g : GL (Fin d) k) : COSub k d where
  sub := L.sub.comap (gHom g⁻¹)
  isOpen := L.isOpen.preimage (glHomeo g).symm.continuous
  isCompact := (glHomeo g).symm.isCompact_preimage.2 L.isCompact

theorem COSub.mem_act {L : COSub k d} {g : GL (Fin d) k} {y : Fin d → k} :
    y ∈ (L.act g).sub ↔ ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y ∈ L.sub := Iff.rfl

theorem COSub.mulVec_mem_act {L : COSub k d} (g : GL (Fin d) k) {y : Fin d → k} :
    (g : Matrix (Fin d) (Fin d) k).mulVec y ∈ (L.act g).sub ↔ y ∈ L.sub := by
  rw [COSub.mem_act, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem COSub.act_one (L : COSub k d) : L.act 1 = L := by
  ext y
  simp [COSub.mem_act]

theorem COSub.act_act (L : COSub k d) (g h : GL (Fin d) k) : (L.act g).act h = L.act (h * g) := by
  ext y
  simp only [COSub.mem_act, mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev]

theorem COSub.act_mono {L L' : COSub k d} (h : L'.sub ≤ L.sub) (g : GL (Fin d) k) :
    (L'.act g).sub ≤ (L.act g).sub := fun _ hy => h hy

def lat0 : COSub k d where
  sub :=
    { carrier := {y | ∀ i, ValuativeRel.valuation k (y i) ≤ 1}
      add_mem' := fun ha hb i => by
        rw [Pi.add_apply]
        exact (Valuation.map_add _ _ _).trans (max_le (ha i) (hb i))
      zero_mem' := fun i => by simp
      neg_mem' := fun ha i => by
        rw [Pi.neg_apply, Valuation.map_neg]
        exact ha i }
  isOpen := by
    have e : {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1} = Set.univ.pi fun _ => cball (1 : kˣ) := by
      ext y
      simp [cball, Set.mem_pi]
    show IsOpen {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1}
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball 1
  isCompact := by
    have e : {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1} = Set.univ.pi fun _ => cball (1 : kˣ) := by
      ext y
      simp [cball, Set.mem_pi]
    show IsCompact {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1}
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_cball 1

def latZ (z : GL (Fin d) k) (r : ℤ) : COSub k d := lat0.act (z ^ r)

def IsReps (L' L : COSub k d) (S : Finset (Fin d → k)) : Prop :=
  (∀ s ∈ S, s ∈ L.sub) ∧ ∀ y ∈ L.sub, ∃! s, s ∈ S ∧ y - s ∈ L'.sub

theorem isClopen_coset (L : COSub k d) (c : Fin d → k) : IsClopen {y | y - c ∈ L.sub} :=
  ⟨L.isCompact.isClosed.preimage (continuous_id.sub continuous_const),
    L.isOpen.preimage (continuous_id.sub continuous_const)⟩

open Classical in

def ind (L : COSub k d) (c : Fin d → k) (a : V) : SchF k d V :=
  ⟨fun y => if y - c ∈ L.sub then a else 0, by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, ?_⟩
    · by_cases hx : x - c ∈ L.sub
      · filter_upwards [(isClopen_coset L c).isOpen.mem_nhds hx] with y hy
        have hy' : y - c ∈ L.sub := hy
        rw [if_pos hx, if_pos hy']
      · filter_upwards [(isClopen_coset L c).compl.isOpen.mem_nhds hx] with y hy
        have hy' : y - c ∉ L.sub := hy
        rw [if_neg hx, if_neg hy']
    · refine HasCompactSupport.intro (L.isCompact.image (continuous_add_right c)) fun x hx => ?_
      rw [if_neg]
      intro h
      exact hx ⟨x - c, h, by simp⟩⟩

open Classical in
theorem ind_apply (L : COSub k d) (c y : Fin d → k) (a : V) :
    (ind L c a).1 y = if y - c ∈ L.sub then a else 0 := rfl

theorem ind_add_mem (L : COSub k d) (x : Fin d → k) {l : Fin d → k} (hl : l ∈ L.sub) (a : V) :
    ind L (x + l) a = ind L x a := by
  refine Subtype.ext (funext fun y => ?_)
  rw [ind_apply, ind_apply]
  have : y - (x + l) ∈ L.sub ↔ y - x ∈ L.sub := by
    have e : y - (x + l) = y - x - l := by abel
    rw [e]
    exact ⟨fun h => by simpa using L.sub.add_mem h hl, fun h => L.sub.sub_mem h hl⟩
  by_cases h : y - x ∈ L.sub
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg (mt this.1 h)]

theorem ind_add (L : COSub k d) (c : Fin d → k) (a b : V) : ind L c (a + b) = ind L c a + ind L c b := by
  refine Subtype.ext (funext fun y => ?_)
  show (ind L c (a + b)).1 y = (ind L c a).1 y + (ind L c b).1 y
  simp only [ind_apply]
  split_ifs <;> simp

theorem ind_smul (L : COSub k d) (c : Fin d → k) (t : ℂ) (a : V) : ind L c (t • a) = t • ind L c a := by
  refine Subtype.ext (funext fun y => ?_)
  show (ind L c (t • a)).1 y = t • (ind L c a).1 y
  simp only [ind_apply]
  split_ifs <;> simp

theorem shiftF_ind (L : COSub k d) (x c : Fin d → k) (a : V) : shiftF x (ind L c a) = ind L (c - x) a := by
  refine Subtype.ext (funext fun y => ?_)
  rw [shiftF_apply, ind_apply, ind_apply]
  have e : y + x - c = y - (c - x) := by abel
  rw [e]

theorem actF_ind (X : Representation ℂ (GL (Fin d) k) V) (g : GL (Fin d) k) (L : COSub k d) (c : Fin d → k) (a : V) :
    actF X g (ind L c a) = ind (L.act g) ((g : Matrix (Fin d) (Fin d) k).mulVec c) (X g a) := by
  refine Subtype.ext (funext fun y => ?_)
  rw [actF_apply, ind_apply, ind_apply]
  have e : ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec (y - (g : Matrix (Fin d) (Fin d) k).mulVec c) =
      ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y - c := by
    rw [mulVec_sub, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have h : (y - (g : Matrix (Fin d) (Fin d) k).mulVec c ∈ (L.act g).sub) ↔
      ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y - c ∈ L.sub := by
    rw [COSub.mem_act, e]
  by_cases hc : ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y - c ∈ L.sub
  · rw [if_pos hc, if_pos (h.2 hc)]
  · rw [if_neg hc, if_neg (mt h.1 hc), map_zero]

def mL (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a : V) (a' : V') : ℂ :=
  B (ind L x a) (ind L 0 a')

theorem B_ind_ind (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hT : ∀ x f f', B (shiftF x f) (shiftF x f') = B f f') (L : COSub k d) (c c' : Fin d → k) (a : V) (a' : V') :
    B (ind L c a) (ind L c' a') = mL B L (c - c') a a' := by
  rw [mL, ← hT c' (ind L c a) (ind L c' a'), shiftF_ind, shiftF_ind, sub_self]

theorem mL_act (X : Representation ℂ (GL (Fin d) k) V) (Y : Representation ℂ (GL (Fin d) k) V')
    (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hG : ∀ g f f', B (actF X g f) (actF Y g f') = B f f') (g : GL (Fin d) k) (L : COSub k d) (x : Fin d → k)
    (a : V) (a' : V') :
    mL B (L.act g) ((g : Matrix (Fin d) (Fin d) k).mulVec x) (X g a) (Y g a') = mL B L x a a' := by
  rw [mL, mL, ← hG g (ind L x a) (ind L 0 a'), actF_ind, actF_ind, mulVec_zero]

theorem mL_add_mem (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) {l : Fin d → k}
    (hl : l ∈ L.sub) (a : V) (a' : V') : mL B L (x + l) a a' = mL B L x a a' := by
  rw [mL, mL, ind_add_mem L x hl]

theorem mL_add_left (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a b : V) (a' : V') :
    mL B L x (a + b) a' = mL B L x a a' + mL B L x b a' := by
  simp [mL, ind_add]

theorem mL_add_right (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a : V) (a' b' : V') :
    mL B L x a (a' + b') = mL B L x a a' + mL B L x a b' := by
  simp [mL, ind_add]

theorem mL_smul_left (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (t : ℂ) (a : V) (a' : V') :
    mL B L x (t • a) a' = t * mL B L x a a' := by
  simp [mL, ind_smul]

theorem mL_smul_right (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a : V) (t : ℂ) (a' : V') :
    mL B L x a (t • a') = t * mL B L x a a' := by
  simp [mL, ind_smul]

def Refines (F : COSub k d → (Fin d → k) → ℂ) : Prop :=
  ∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S → ∀ x,
    (S.card : ℂ) * F L x = ∑ s ∈ S, F L' (x + s)

end GlobalTheory.CompanionTheory.BZCore

end
end

section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

theorem zpow_mulVec (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ0 : ϖ ≠ 0) (r : ℤ) (y : Fin d → k) :
    ((z ^ r : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y = ϖ ^ r • y := by
  let φ : kˣ →* GL (Fin d) k := Units.map (Matrix.scalar (Fin d) : k →+* Matrix (Fin d) (Fin d) k).toMonoidHom
  have hφ : ∀ u : kˣ, ((φ u : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) = (u : k) • (1 : Matrix (Fin d) (Fin d) k) := by
    intro u
    ext i j
    simp [φ, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have h1 : z = φ (Units.mk0 ϖ hϖ0) := Units.ext (by rw [hφ, hz]; rfl)
  rw [h1, ← map_zpow, hφ, Matrix.smul_mulVec, one_mulVec]
  simp

theorem mem_latZ (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ0 : ϖ ≠ 0) (r : ℤ) (y : Fin d → k) :
    y ∈ (latZ z r).sub ↔ ∀ i, ValuativeRel.valuation k (y i) ≤ ValuativeRel.valuation k ϖ ^ r := by
  have hv : ValuativeRel.valuation k ϖ ≠ 0 := by simpa using hϖ0
  rw [latZ, COSub.mem_act, ← _root_.zpow_neg, zpow_mulVec z ϖ hz hϖ0]
  show (∀ i, ValuativeRel.valuation k ((ϖ ^ (-r) • y) i) ≤ 1) ↔ _
  refine forall_congr' fun i => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_zpow₀, _root_.zpow_neg, inv_mul_le_iff₀ (zero_lt_iff.2 (zpow_ne_zero _ hv)), mul_one]

theorem latZ_anti (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (r s : ℤ) (h : r ≤ s) : (latZ z s).sub ≤ (latZ z r).sub := by
  intro y hy
  have hv : 0 < ValuativeRel.valuation k ϖ := zero_lt_iff.2 (by simpa using hϖ0)
  rw [mem_latZ z ϖ hz hϖ0] at hy ⊢
  exact fun i => (hy i).trans (zpow_le_zpow_right_of_le_one₀ hv hϖ.le h)

theorem latZ_basis (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (L : COSub k d) : ∃ r : ℕ, (latZ z (r : ℤ)).sub ≤ L.sub := by
  have hall : ∀ᶠ t : k in 𝓝 0, ∀ w ∈ ((lat0 : COSub k d).sub : Set (Fin d → k)), t • w ∈ (L.sub : Set (Fin d → k)) := by
    refine (lat0 : COSub k d).isCompact.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun p : k × (Fin d → k) => p.1 • p.2 := continuous_fst.smul continuous_snd
    have h0 : (L.sub : Set (Fin d → k)) ∈ 𝓝 (((0 : k), w).1 • ((0 : k), w).2) := by
      simpa using L.isOpen.mem_nhds (show (0 : Fin d → k) ∈ (L.sub : Set (Fin d → k)) from L.sub.zero_mem)
    exact hc.continuousAt.eventually h0
  have ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  obtain ⟨r, hr⟩ := (ht.eventually hall).exists
  refine ⟨r, fun y hy => ?_⟩
  have h1 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) ∈ (L.sub : Set (Fin d → k)) := hr _ hy
  have h2 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) = y := by
    have := zpow_mulVec z ϖ hz hϖ0 (r : ℤ) ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, zpow_natCast] at this
    exact this.symm
  rw [h2] at h1
  exact h1

theorem exists_reps (L' L : COSub k d) (h : L'.sub ≤ L.sub) : ∃ S : Finset (Fin d → k), IsReps L' L S := by
  classical
  obtain ⟨t, ht⟩ := L.isCompact.elim_finite_subcover (fun c : L.sub => {y | y - (c : Fin d → k) ∈ L'.sub})
    (fun c => (isClopen_coset L' c).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, by simp⟩)
  let mk : (Fin d → k) → (Fin d → k) ⧸ L'.sub := QuotientAddGroup.mk
  have hout : ∀ c : Fin d → k, (-(Quotient.out (mk c)) + c) ∈ L'.sub := fun c =>
    QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (mk c))
  let S : Finset (Fin d → k) := (t.image fun c : L.sub => mk c.1).image Quotient.out
  refine ⟨S, ?_, ?_⟩
  · intro s hs
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hq
    have h1 := L.sub.sub_mem c.2 (h (hout c.1))
    simpa [sub_eq_add_neg] using h1
  · intro y hy
    obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hc' : y - c.1 ∈ L'.sub := hc
    have key : ∀ s ∈ S, y - s ∈ L'.sub → s = Quotient.out (mk y) := by
      intro s hs hys
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
      have e1 : mk (Quotient.out q) = q := QuotientAddGroup.out_eq' q
      have e2 : mk (Quotient.out q) = mk y :=
        QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using hys)
      rw [← e2, e1]
    have hmem : Quotient.out (mk c.1) ∈ S :=
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem (fun c : L.sub => mk c.1) hct)
    have hs : y - Quotient.out (mk c.1) ∈ L'.sub := by
      have := L'.sub.add_mem hc' (hout c.1)
      have e : y - c.1 + (-(Quotient.out (mk c.1)) + c.1) = y - Quotient.out (mk c.1) := by abel
      rwa [e] at this
    exact ⟨_, ⟨hmem, hs⟩, fun s' hs' => (key s' hs'.1 hs'.2).trans (key _ hmem hs).symm⟩

end GlobalTheory.CompanionTheory.BZCore

end
end
