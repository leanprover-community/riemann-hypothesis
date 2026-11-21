import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeStabilizerNormalisingSubgroup
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerCommensurableUnramifiedHermitia
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeConjModularCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonal

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', ∃ Λ : Submodule L.O S.V, IsLat L Λ ∧ S.St ⊓ stabL L Λ = S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ⊓ stabL L (Submodule.span L.O (Set.range fun b => n' (S.f' b))) ∧ S.St ⊓ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) ≤ S.St ⊓ stabL L Λ ∧ ∀ h ∈ S.St ⊓ stabL L Λ, CongId L S.ϖ Λ 1 h → h ∈ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) := by
  first | exact @GlobalTheory.HL.FrameStabLat.main | exact GlobalTheory.HL.FrameStabLat.main | (intros; apply GlobalTheory.HL.FrameStabLat.main <;> assumption)
end

section
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FlagUnipotent

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sub_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a - b) y = hf L H a y - hf L H b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_sub_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x a b : Fin n → E) :
    hf L H x (a - b) = hf L H x a - hf L H x b := by
  simp [hf, mul_sub, Finset.sum_sub_distrib]

theorem pow_eq_zero_of_mem_Nof {L : LocE F E} {r k : ℕ} (S : Frames L r k)
    (f : Fin (r + 1) → S.V) (g : S.GLV) (hg : g ∈ S.Nof f) :
    ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 := by
  obtain ⟨⟨hiso, hfl⟩, hmid⟩ := hg
  have hfl' : ∀ j, j < r → g ∈ unipOn (S.spanTo f (j + 1)) (S.spanTo f j) := fun j hj =>
    (Subgroup.mem_iInf.1 hfl) ⟨j, hj⟩
  set A : S.V →ₗ[E] S.V := (g : S.V →ₗ[E] S.V) - 1 with hA
  have hAv : ∀ v, A v = g v - v := fun v => rfl
  have h0 : S.spanTo f 0 = ⊥ := by simp [Frames.spanTo]
  have ha : ∀ j, j ≤ r → ∀ v, (A ^ j) v ∈ perp L S.Hm (S.spanTo f j) := by
    intro j
    induction j with
    | zero =>
      intro _ v y hy
      rw [h0, Submodule.mem_bot] at hy
      simp [hy, hf]
    | succ j ih =>
      intro hj v x hx
      obtain ⟨h1, h2⟩ := hfl' j hj
      have hw := ih (by omega) v
      rw [pow_succ', Module.End.mul_apply, hAv]
      generalize (A ^ j) v = w at hw
      obtain ⟨y, rfl⟩ := g.surjective x
      have h3 : hf L S.Hm w (g y - y) = 0 := hw _ (h2 y ((h1 y).1 hx))
      have h4 : hf L S.Hm (g w) (g y) = hf L S.Hm w y := hiso w y
      rw [hf_sub_right] at h3
      rw [hf_sub_left, h4]
      linear_combination -h3
  have hc : ∀ j, j ≤ r → ∀ v ∈ S.spanTo f j, (A ^ j) v = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ v hv
      rw [h0, Submodule.mem_bot] at hv
      simp [hv]
    | succ j ih =>
      intro hj v hv
      rw [pow_succ, Module.End.mul_apply, hAv]
      exact ih (by omega) _ ((hfl' j hj).2 v hv)
  refine LinearMap.ext fun v => ?_
  have e : 2 * r + 1 = r + (1 + r) := by omega
  rw [e, pow_add, pow_add, pow_one, Module.End.mul_apply, Module.End.mul_apply, hAv]
  exact hc r le_rfl _ (hmid.2 _ (ha r le_rfl v))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g ∈ S.N, ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 :=
  fun _ _ _ S g hg => pow_eq_zero_of_mem_Nof S S.f g hg

end GlobalTheory.FlagUnipotent
end
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_eq_zero_of_mem_hermitianFrameUnipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g ∈ S.N, ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 := by
  atlas_forward_decl GlobalTheory.FlagUnipotent.main
end

section
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem exists_fg_span_stable_of_unipotent {E : Type} [CommRing E] (O : Subring E) {n : ℕ}
    (g : (Fin n → E) →ₗ[E] (Fin n → E)) (e : ℕ) (hg : (g - 1) ^ e = 0) :
    ∃ Λ : Submodule O (Fin n → E), Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
      (∀ v ∈ Λ, g v ∈ Λ) ∧ ∀ v ∈ Λ, ∃ w ∈ Λ, g w = v := by
  set x : (Fin n → E) →ₗ[E] (Fin n → E) := 1 - g with hx
  have hxe : x ^ e = 0 := by
    have : x = -(g - 1) := by rw [hx, neg_sub]
    rw [this, neg_pow, hg, mul_zero]
  let s : Set (Fin n → E) :=
    Set.range fun p : Fin (e + 1) × Fin n => (x ^ (p.1 : ℕ)) (Pi.single p.2 1)
  have hall : ∀ (i : ℕ) (j : Fin n), (x ^ i) (Pi.single j 1) ∈ Submodule.span O s := by
    intro i j
    by_cases hi : i < e + 1
    · exact Submodule.subset_span ⟨(⟨i, hi⟩, j), rfl⟩
    · have : x ^ i = 0 := pow_eq_zero_of_le (by omega) hxe
      rw [this]
      exact Submodule.zero_mem _
  have hpow : ∀ (k : ℕ), ∀ v ∈ Submodule.span O s, (x ^ k) v ∈ Submodule.span O s := by
    intro k v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      have := hall (k + p.1) p.2
      rwa [pow_add, Module.End.mul_apply] at this
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : (x ^ k) (c • a) = c • (x ^ k) a := (x ^ k).map_smul (c : E) a
      rw [this]
      exact Submodule.smul_mem _ c ha
  refine ⟨Submodule.span O s, Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    have := hall 0 j
    simpa using this
  · intro v hv
    have h1 := hpow 1 v hv
    have h2 : g v = v - (x ^ 1) v := by simp [hx]
    rw [h2]
    exact Submodule.sub_mem _ hv h1
  · intro v hv
    refine ⟨(∑ i ∈ Finset.range e, x ^ i) v, ?_, ?_⟩
    · rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => hpow i v hv
    · have h := mul_neg_geom_sum x e
      have h1 : 1 - x = g := by rw [hx, sub_sub_cancel]
      rw [h1, hxe, sub_zero] at h
      rw [← Module.End.mul_apply, h, Module.End.one_apply]

theorem exists_isLat_stabL_of_unipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (g : ((Fin n → E) ≃ₗ[E] (Fin n → E))) (e : ℕ), (((g : (Fin n → E) →ₗ[E] (Fin n → E)) - 1) ^ e = 0) → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ g ∈ stabL L Λ := by
  intro F _ _ _ _ _ E _ _ _ L n g e hg
  obtain ⟨Λ, h1, h2, h3, h4⟩ := exists_fg_span_stable_of_unipotent L.O _ e hg
  refine ⟨Λ, ⟨h1, h2⟩, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact h3 w hw
  · intro hv
    obtain ⟨w, hw, h⟩ := h4 v hv
    exact ⟨w, hw, h⟩

end GlobalTheory.HL
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_stabilizes_some_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (g : ((Fin n → E) ≃ₗ[E] (Fin n → E))) (e : ℕ), (((g : (Fin n → E) →ₗ[E] (Fin n → E)) - 1) ^ e = 0) → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ g ∈ stabL L Λ := by
  atlas_forward_decl GlobalTheory.HL.exists_isLat_stabL_of_unipotent
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_pairingStabilizer_blockDiagonal : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → IsUni s' → cT L s * S.Zh * s' = S.Zh → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0 ∧ s' i j = 0) ∧ (IsIntM L s ↔ IsIntM L s')) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0) → ∃ s', IsUni s' ∧ cT L s * S.Zh * s' = S.Zh := by
  first | exact @GlobalTheory.HL.BlockStab.stabiliser_blockDiag | exact GlobalTheory.HL.BlockStab.stabiliser_blockDiag | (intros; apply GlobalTheory.HL.BlockStab.stabiliser_blockDiag <;> assumption)
end

section
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StabConj

section Blocks
variable {E : Type} [CommRing E]

def bd {n : ℕ} (w : Pt E n) (A : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  fun i j => if sameBlock w.blocks i j = true then A i j else 0

def Rep {n m : ℕ} (f : Fin m → Fin n → E) (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (s : Matrix (Fin m) (Fin m) E) : Prop := ∀ j, g (f j) = ∑ i, s i j • f i

lemma Rep.mul {n m : ℕ} {f : Fin m → Fin n → E} {g h : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    {s t : Matrix (Fin m) (Fin m) E} (hg : Rep f g s) (hh : Rep f h t) : Rep f (g * h) (s * t) := by
  intro j
  rw [LinearEquiv.mul_apply, hh j, map_sum]
  simp only [map_smul, hg _, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end Blocks

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {E : Type} [CommRing E] in
private lemma rep_apply_sum_smul_eq_sum_mul_smul {n m : ℕ} {f : Fin m → Fin n → E}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {A : Matrix (Fin m) (Fin m) E}
    (hg : _root_.GlobalTheory.HL.StabConj.Rep f g A) (B : Matrix (Fin m) (Fin m) E) (j : Fin m) :
    g (∑ i, B i j • f i) = ∑ i, (A * B) i j • f i := by
  simp only [map_sum, map_smul, hg _, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {E : Type} [CommRing E] in
private lemma rep_inv_of_mul_eq_one {n m : ℕ} {f : Fin m → Fin n → E}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {A B : Matrix (Fin m) (Fin m) E}
    (hg : _root_.GlobalTheory.HL.StabConj.Rep f g A) (hAB : A * B = 1) :
    _root_.GlobalTheory.HL.StabConj.Rep f g⁻¹ B := by
  intro j
  have h := rep_apply_sum_smul_eq_sum_mul_smul hg B j
  have h1 : ∑ i, (1 : Matrix (Fin m) (Fin m) E) i j • f i = f j := by
    simp [Matrix.one_apply]
  rw [hAB, h1] at h
  rw [← h]
  exact g.symm_apply_apply _

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {E : Type} [CommRing E] in
private lemma matrix_eq_of_linearIndependent_sum_smul_eq {n m : ℕ} {f : Fin m → Fin n → E}
    (hf : LinearIndependent E f) {A B : Matrix (Fin m) (Fin m) E}
    (h : ∀ j, ∑ i, A i j • f i = ∑ i, B i j • f i) : A = B := by
  ext i j
  have := Fintype.linearIndependent_iff.mp hf (fun l => A l j - B l j)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h j, sub_self])
  exact sub_eq_zero.mp (this i)

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
private lemma smul_span_le_of_rep_entries_mem (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n m : ℕ} {f : Fin m → Fin n → E}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {A : Matrix (Fin m) (Fin m) E}
    (hg : _root_.GlobalTheory.HL.StabConj.Rep f g A) (hA : ∀ i j, A i j ∈ L.O) :
    g • Submodule.span L.O (Set.range f) ≤ Submodule.span L.O (Set.range f) := by
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  show g (f j) ∈ Submodule.span L.O (Set.range f)
  rw [hg j]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : A i j • f i = (⟨A i j, hA i j⟩ : L.O) • f i := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.StabConj.main : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ)
    (S : _root_.GlobalTheory.HL.Frames L r k), ∀ n ∈ S.N,
    ∃ h ∈ S.St, S.St ⊓
      _root_.GlobalTheory.HL.stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ≤
        MulAut.conj h • S.K0 ∧
      ∃ u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, _root_.GlobalTheory.HL.IsUni u ∧
        (∀ i j : Fin (r + 1), _root_.Formalism.MainNotions.S.Loc.sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧
        ∀ j, h⁻¹ (n (S.f j)) = ∑ i, u i j • S.f i := by
  intro F _ _ _ _ _ E _ _ _ L r k S n hn

  obtain ⟨σ, β, τ, hβ⟩ :=
    _root_.GlobalTheory.HL.BlockStab.exists_monomial S.w.blocks
  rw [S.w.size] at hβ
  have hsame : ∀ i j : Fin (r + 1),
      _root_.Formalism.MainNotions.S.Loc.sameBlock S.w.blocks i j = true ↔ β i = β j :=
    fun i j => ((hβ i i.isLt).2.2.2 j j.isLt).1
  have hmono : ∀ i j : Fin (r + 1), i ≤ j → β i ≤ β j :=
    fun i j hij => ((hβ i i.isLt).2.2.2 j j.isLt).2.1 hij
  have hfalse : ∀ i j : Fin (r + 1), β i ≠ β j →
      _root_.Formalism.MainNotions.S.Loc.sameBlock S.w.blocks i j = false :=
    fun i j hij => Bool.eq_false_iff.mpr fun ht => hij ((hsame i j).1 ht)
  have hoff : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, _root_.GlobalTheory.HL.IsUni M →
      (∀ i j : Fin (r + 1), β i < β j → M i j = 0) →
      ∀ i j : Fin (r + 1), β i ≠ β j → M i j = 0 := by
    intro M hM hlt i j hij
    rcases lt_or_gt_of_ne hij with h1 | h1
    · exact hlt i j h1
    · exact hM.1 i j (lt_of_not_ge fun hle => absurd (hmono i j hle) (not_le.mpr h1))
  have hlower : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, _root_.GlobalTheory.HL.IsUni M →
      ∀ i j : Fin (r + 1), β j < β i → M i j = 0 := by
    intro M hM i j hij
    exact hM.1 i j (lt_of_not_ge fun hle => absurd (hmono i j hle) (not_le.mpr hij))

  obtain ⟨s, hsU, hns⟩ := (_root_.GlobalTheory.HL.FrameOnto.unipotent_onto L r k S).1 n hn
  have hsU' : _root_.GlobalTheory.HL.IsUni s := hsU
  obtain ⟨sb, hsb⟩ : ∃ sb, sb = _root_.GlobalTheory.HL.StabConj.bd S.w s := ⟨_, rfl⟩
  have hsbU : _root_.GlobalTheory.HL.IsUni sb := by
    unfold _root_.GlobalTheory.HL.IsUni
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hsb]
      simp only [_root_.GlobalTheory.HL.StabConj.bd]
      split_ifs
      · exact hsU'.1 i j hji
      · rfl
    · rw [hsb]
      simp only [_root_.GlobalTheory.HL.StabConj.bd, (hsame i i).2 rfl, if_true]
      exact hsU'.2 i
  have hsb0 : ∀ i j : Fin (r + 1),
      _root_.Formalism.MainNotions.S.Loc.sameBlock S.w.blocks i j = false → sb i j = 0 := by
    intro i j hij
    rw [hsb]
    simp [_root_.GlobalTheory.HL.StabConj.bd, hij]

  obtain ⟨s', hs'U, hs'⟩ := (_root_.GlobalTheory.HL.BlockStab.stabiliser_blockDiag L r k S).2 sb hsbU hsb0
  obtain ⟨h, hhSt, hhf, -⟩ :=
    ((_root_.GlobalTheory.HL.FrameStab.stab_eq L r k S).2 sb s' hsbU hs'U).mp hs'
  have hhR : _root_.GlobalTheory.HL.StabConj.Rep S.f h sb := hhf
  obtain ⟨B, hsbB, hBsb, hBU, -, hBβ⟩ := _root_.GlobalTheory.HL.BlockStab.inv_facts sb hsbU
  have hBoff : ∀ i j : Fin (r + 1), β i ≠ β j → B i j = 0 :=
    hoff B hBU (hBβ (fun i => β i) fun i j hij => hsb0 i j (hfalse i j hij.ne))
  have hu : _root_.GlobalTheory.HL.IsUni (B * s) := _root_.GlobalTheory.HL.FrameStabLat.uni_mul hBU hsU'
  have hublk : ∀ i j : Fin (r + 1), β i = β j →
      (B * s) i j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j := by
    intro i j hij
    rw [← hBsb, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hil : β i = β l
    · rw [hsb]
      simp only [_root_.GlobalTheory.HL.StabConj.bd, (hsame l j).2 (hil.symm.trans hij), if_true]
    · rw [hBoff i l hil, zero_mul, zero_mul]
  have hnu : _root_.GlobalTheory.HL.StabConj.Rep S.f (h⁻¹ * n) (B * s) := by
    intro j
    show h⁻¹ (n (S.f j)) = _
    rw [hns j]
    exact rep_apply_sum_smul_eq_sum_mul_smul (rep_inv_of_mul_eq_one hhR hsbB) s j
  have hfli : LinearIndependent E S.f :=
    (_root_.GlobalTheory.FrameBasic.main L r k S).1.comp Sum.inl Sum.inl_injective
  obtain ⟨B', -, hB'u, hB'U, -, -⟩ := _root_.GlobalTheory.HL.BlockStab.inv_facts _ hu

  have key : ∀ g ∈ S.St ⊓ _root_.GlobalTheory.HL.stabL L
      (Submodule.span L.O (Set.range fun b => n (S.f b))),
      (h⁻¹ * g * h) • Submodule.span L.O (Set.range S.f) ≤
          Submodule.span L.O (Set.range S.f) ∧
        (h⁻¹ * g * h) • Submodule.span L.O (Set.range S.f') ≤
          Submodule.span L.O (Set.range S.f') := by
    intro g hg
    obtain ⟨hgSt, hgΛ⟩ := Subgroup.mem_inf.mp hg
    have hgΛ' : g • Submodule.span L.O (Set.range fun b => n (S.f b)) =
        Submodule.span L.O (Set.range fun b => n (S.f b)) := hgΛ
    have hg'St : h⁻¹ * g * h ∈ S.St :=
      mul_mem (mul_mem (inv_mem hhSt) hgSt) hhSt
    obtain ⟨t, htU, ht⟩ :=
      (_root_.GlobalTheory.HL.FrameOnto.unipotent_onto L r k S).1 _ (Subgroup.mem_inf.mp hg'St).1
    obtain ⟨t', ht'U, ht'⟩ :=
      (_root_.GlobalTheory.HL.FrameOnto.unipotent_onto L r k S).2.1 _ (Subgroup.mem_inf.mp hg'St).2
    have heq := ((_root_.GlobalTheory.HL.FrameStab.stab_eq L r k S).2 t t' htU
      ht'U).mpr ⟨_, hg'St, ht, ht'⟩
    obtain ⟨htblk, htint⟩ := (_root_.GlobalTheory.HL.BlockStab.stabiliser_blockDiag L r k S).1 t t' htU
      ht'U heq
    have htU' : _root_.GlobalTheory.HL.IsUni t := htU
    have htR : _root_.GlobalTheory.HL.StabConj.Rep S.f (h⁻¹ * g * h) t := ht
    have htoff : ∀ i j : Fin (r + 1), β i ≠ β j → t i j = 0 :=
      fun i j hij => (htblk i j (hfalse i j hij)).1

    have hcoef : ∀ j, ∃ c : Fin (r + 1) → L.O,
        ∑ i, c i • n (S.f i) = g (n (S.f j)) := by
      intro j
      have hmem : g • n (S.f j) ∈
          g • Submodule.span L.O (Set.range fun b => n (S.f b)) :=
        Submodule.smul_mem_pointwise_smul _ g _ (Submodule.subset_span ⟨j, rfl⟩)
      rw [hgΛ'] at hmem
      exact (Submodule.mem_span_range_iff_exists_fun L.O).mp hmem
    choose c hc using hcoef
    obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) E, C = fun i j => (c j i : E) :=
      ⟨_, rfl⟩
    have hhh : ∀ x, h (h⁻¹ x) = x := fun x => h.apply_symm_apply x
    have hlin : ∀ j, ∑ i, (t * (B * s)) i j • S.f i =
        ∑ i, ((B * s) * C) i j • S.f i := by
      intro j
      rw [← rep_apply_sum_smul_eq_sum_mul_smul htR, ← rep_apply_sum_smul_eq_sum_mul_smul hnu, ← hnu j]
      show h⁻¹ (g (h (h⁻¹ (n (S.f j))))) = h⁻¹ (n (∑ i, C i j • S.f i))
      rw [hhh, ← hc j]
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hC]
      rfl
    have htu := matrix_eq_of_linearIndependent_sum_smul_eq hfli hlin
    have hCeq : C = B' * (t * (B * s)) := by
      rw [htu, ← Matrix.mul_assoc, hB'u, Matrix.one_mul]
    have hCU : _root_.GlobalTheory.HL.IsUni C := by
      rw [hCeq]
      exact _root_.GlobalTheory.HL.FrameStabLat.uni_mul hB'U (_root_.GlobalTheory.HL.FrameStabLat.uni_mul htU' hu)
    have htO : _root_.GlobalTheory.HL.IsIntM L t := by
      unfold _root_.GlobalTheory.HL.IsIntM
      intro i j
      by_cases hij : β i = β j
      · have e1 : (t * (B * s)) i j = t i j := by
          rw [Matrix.mul_apply, Finset.sum_eq_single j]
          · rw [hublk j j rfl, Matrix.one_apply_eq, mul_one]
          · intro l _ hl
            by_cases hil : β i = β l
            · rw [hublk l j (hil.symm.trans hij), Matrix.one_apply_ne hl, mul_zero]
            · rw [htoff i l hil, zero_mul]
          · intro hj
            exact absurd (Finset.mem_univ j) hj
        have e2 : ((B * s) * C) i j = C i j := by
          rw [Matrix.mul_apply, Finset.sum_eq_single i]
          · rw [hublk i i rfl, Matrix.one_apply_eq, one_mul]
          · intro l _ hl
            rcases lt_trichotomy (β l) (β i) with h1 | h1 | h1
            · rw [hlower _ hu i l h1, zero_mul]
            · rw [hublk i l h1.symm, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
            · rw [hlower _ hCU l j (hij ▸ h1), mul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
        rw [← e1, htu, e2, hC]
        exact (c j i).2
      · rw [htoff i j hij]
        exact L.O.zero_mem
    exact ⟨smul_span_le_of_rep_entries_mem L htR htO, smul_span_le_of_rep_entries_mem L ht' (htint.mp htO)⟩
  have hconj : ∀ (g : S.GLV) (K : Subgroup S.GLV), g ∈ MulAut.conj h • K ↔ h⁻¹ * g * h ∈ K := by
    intro g K
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  have hstab : ∀ (x : S.GLV) (M : Submodule L.O S.V), x • M ≤ M → x⁻¹ • M ≤ M → x • M = M := by
    intro x M h1 h2
    refine le_antisymm h1 fun v hv => ?_
    have hv' : x⁻¹ • v ∈ M := h2 (Submodule.smul_mem_pointwise_smul v x⁻¹ M hv)
    simpa using Submodule.smul_mem_pointwise_smul _ x M hv'
  refine ⟨h, hhSt, fun g hg => ?_, B * s, hu, fun i j hij => ?_, hnu⟩
  · rw [hconj]
    have hg' : h⁻¹ * g * h ∈ S.St :=
      mul_mem (mul_mem (inv_mem hhSt) (Subgroup.mem_inf.mp hg).1) hhSt
    obtain ⟨h1, h2⟩ := key g hg
    obtain ⟨h3, h4⟩ := key g⁻¹ (inv_mem hg)
    have hinv : h⁻¹ * g⁻¹ * h = (h⁻¹ * g * h)⁻¹ := by group
    rw [hinv] at h3 h4
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hg', hstab _ _ h1 h3⟩, hstab _ _ h2 h4⟩
  · rw [hublk i j ((hsame i j).1 hij), Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem

end GlobalTheory.HL.StabConj
end
end

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∃ h ∈ S.St, S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ≤ MulAut.conj h • S.K0 ∧ ∃ u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ ∀ j, h⁻¹ (n (S.f j)) = ∑ i, u i j • S.f i := by
  atlas_forward_decl GlobalTheory.HL.StabConj.main
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem volSt_conj_self {G : Type} [Group G] (H : Subgroup G) {h : G} (hh : h ∈ H) :
    MulAut.conj h • H = H := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

theorem volSt_inf_stab_smul {G X : Type} [Group G] [MulAction G X] (H : Subgroup G) {h : G} (hh : h ∈ H)
    (x : X) : H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  rw [Subgroup.smul_inf, volSt_conj_self H hh]
  congr 1
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, MulAction.mem_stabilizer_iff, mul_smul,
    inv_smul_eq_iff]

theorem volSt {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
    (r k : ℕ) (S : Frames L r k) :
    (∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧
      (S.St ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.K0 ≠ 0 ∧ ∀ h ∈ S.St, S.mu (h • Λ) = S.mu Λ) ∧
    ∀ C, S.IsCls C → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 ∧
      (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 ∧ 1 ≤ S.wC C ∧
      ∀ h ∈ S.St, S.wC (h • C) = S.wC C := by
  obtain ⟨Λ1, hΛ1, hK0, -⟩ := GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup L r k S 1 S.N.one_mem 1 S.N'.one_mem
  have hK : S.K0 = S.St ⊓ stabL L Λ1 := hK0.symm
  have hc : ∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ stabL L Λ) ≠ 0 ∧
      (S.St ⊓ stabL L Λ).relIndex S.K0 ≠ 0 := by
    intro Λ hΛ
    rw [hK]
    exact ⟨(GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ1 hΛ hΛ1 S.St).1, (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ1 Λ hΛ1 hΛ S.St).1⟩
  have hconj : ∀ h ∈ S.St, S.K0.relIndex (MulAut.conj h • S.K0) ≠ 0 ∧
      (MulAut.conj h • S.K0).relIndex S.K0 ≠ 0 := by
    intro h hh
    have e : MulAut.conj h • S.K0 = S.St ⊓ stabL L (h • Λ1) := by
      rw [hK]; exact (volSt_inf_stab_smul S.St hh Λ1).symm
    rw [e]
    exact hc _ ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ1 Λ1 hΛ1 hΛ1 S.St).2 h).1
  have hle : S.K0 ≤ S.St := by rw [hK]; exact inf_le_left
  have hmod := (GlobalTheory.T.haarInvVolume_conj_modular_character S.St S.K0 hle hconj).2.2.2
  have hone : ∀ h ∈ S.St, invVol S.K0 (MulAut.conj h • S.K0) = 1 := by
    intro h hh
    obtain ⟨Λ, hΛ, hs⟩ := GlobalTheory.T.unipotent_stabilizes_some_lattice L h _ (GlobalTheory.T.pow_eq_zero_of_mem_hermitianFrameUnipotent L r k S h hh.1)
    exact (hmod _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh).2 (volSt_conj_self _ ⟨hh, hs⟩)
  have hinv : ∀ K' : Subgroup S.GLV, S.K0.relIndex K' ≠ 0 → K'.relIndex S.K0 ≠ 0 → ∀ h ∈ S.St,
      invVol S.K0 (MulAut.conj h • K') = invVol S.K0 K' := by
    intro K' h1 h2 h hh
    rw [(hmod K' h1 h2 h hh).1, hone h hh, one_mul]
  refine ⟨fun Λ hΛ => ⟨(hc Λ hΛ).1, (hc Λ hΛ).2, fun h hh => ?_⟩, ?_⟩
  · unfold Frames.mu
    rw [volSt_inf_stab_smul S.St hh Λ]
    exact hinv _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh
  rintro C ⟨n, hn, n', hn', hC⟩
  obtain ⟨Λ, hΛ, e1, e2, e3⟩ := GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup L r k S n hn n' hn'
  rw [← hC] at e2 e3
  obtain ⟨⟨K, hKm, hKi, -⟩, -⟩ := GlobalTheory.T.congruence_subgroup_lattice_stabilizer L S.ϖ S.ϖ_irr Λ hΛ 1
  have a1 : S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 :=
    fun h0 => (hc Λ hΛ).1 (Subgroup.relIndex_eq_zero_of_le_right e2 h0)
  have b1 : K.relIndex (S.St ⊓ stabL L Λ) ≠ 0 :=
    fun h0 => hKi (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  have b2 : (K ⊓ (S.St ⊓ stabL L Λ)) ≤ S.St ⊓ MulAction.stabilizer S.GLV C :=
    fun g hg => ⟨hg.2.1, e3 g hg.2 ((hKm g).1 hg.1).2⟩
  have b3 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex (S.St ⊓ stabL L Λ) ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_eq_zero_of_le_left b2 h0
    rw [Subgroup.inf_relIndex_right] at this
    exact b1 this
  have a2 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans b3 (hc Λ hΛ).2
  refine ⟨a1, a2, ?_, fun h hh => ?_⟩
  · obtain ⟨h, hh, hw, -⟩ := GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup L r k S n hn
    have c1 : S.St ⊓ MulAction.stabilizer S.GLV C ≤ MulAut.conj h • S.K0 :=
      e2.trans (e1.le.trans (inf_le_left.trans hw))
    have c2 := (invVol_mul_pos_le_conj S.K0 (MulAut.conj h • S.K0) _ (hconj h hh).1 (hconj h hh).2
      a1 a2).2.2.1 c1
    have c3 := Subgroup.relIndex_ne_zero_trans a2 (hconj h hh).1
    unfold Frames.wC
    rw [c2, hone h hh, one_mul]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 c3
  · unfold Frames.wC
    rw [volSt_inf_stab_smul S.St hh C]
    exact hinv _ a1 a2 h hh

end GlobalTheory.HL
end
