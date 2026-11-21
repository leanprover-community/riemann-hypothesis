import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosurePointsIsGroup
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatMemRatZariskiClosurePoints
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsFiniteAdeleLikePairElementary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftTranslationReynoldsOperator
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTranspose
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyTensorFormProperties
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyCompletelyReducible
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsReynoldsOfCompletelyReducible
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRational
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteIntegralClassesClosedOrbit

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open MvPolynomial

variable {ι : Type}

theorem evC_aeval_invariants {κ : Type} (Φ : κ → MvPolynomial (ι × ι) ℂ) (P : MvPolynomial κ ℂ)
    (y : Matrix ι ι ℂ) : evC (aeval Φ P) y = eval (fun k => evC (Φ k) y) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq => simp only [evC, map_add] at *; rw [hp, hq]
  | mul_X p n hp => simp only [evC, map_mul, aeval_X, eval_X] at *; rw [hp]

theorem evC_det_generic [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) :
    evC (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det y = y.det := by
  unfold evC
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem exists_evC_eq_of_relations [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ]
    (Φ : κ → MvPolynomial (ι × ι) ℂ) (hR : IsReynolds Γ Rey) (hΦ : ∀ k, IsInv Γ (Φ k))
    (hgen : ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) (z : κ → ℂ)
    (hz : ∀ P : MvPolynomial κ ℂ, aeval Φ P = 0 → eval z P = 0) :
    ∃ y : Matrix ι ι ℂ, z = fun k => evC (Φ k) y := by
  set I : Ideal (MvPolynomial (ι × ι) ℂ) := Ideal.span (Set.range fun k => Φ k - C (z k)) with hI
  have hne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ I := h ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have hinv : ∀ k, IsInv Γ (Φ k - C (z k)) := by
      intro k g hg y
      have := hΦ k g hg y
      simp only [evC, map_sub, eval_C] at *
      rw [this]
    have hone : Rey 1 = 1 := hR.fix 1 (fun g hg y => by simp [evC])
    have h2 : ∑ k, (Φ k - C (z k)) * Rey (a k) = 1 := by
      rw [← hone, ← ha, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm (a k), hR.mul _ _ (hinv k)]
    have h3 : ∀ k, ∃ P : MvPolynomial κ ℂ, aeval Φ P = Rey (a k) := by
      intro k
      have := hgen _ (hR.inv (a k))
      rw [Algebra.adjoin_range_eq_range_aeval] at this
      exact this
    choose P hP using h3
    have h4 := hz (∑ k, (X k - C (z k)) * P k - 1) (by
      simp only [map_sub, map_sum, map_mul, aeval_X, aeval_C, map_one, hP, algebraMap_eq]
      rw [h2, sub_self])
    simp at h4
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨Matrix.of fun i j => x (i, j), funext fun k => ?_⟩
  have hk : Φ k - C (z k) ∈ M := hIM (Ideal.subset_span ⟨k, rfl⟩)
  rw [hx, mem_vanishingIdeal_singleton_iff] at hk
  simp only [map_sub, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, coe_aeval_eq_eval] at hk
  have : evC (Φ k) (Matrix.of fun i j => x (i, j)) = aeval x (Φ k) := rfl
  rw [this]
  exact (sub_eq_zero.1 hk).symm

theorem isClosed_image_invariants :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ] (Φ : κ → MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → (∀ g ∈ Γ, g.det = 1) → (∀ k, IsInv Γ (Φ k)) → (∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) → IsClosed {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} := by
  intro ι _ _ Γ Rey κ _ Φ hR hdet hΦ hgen
  have hD : IsInv Γ (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det := by
    intro g hg y
    rw [evC_det_generic, evC_det_generic, det_mul, hdet g hg, one_mul]
  have hD' := hgen _ hD
  rw [Algebra.adjoin_range_eq_range_aeval] at hD'
  obtain ⟨Q, hQ⟩ := hD'
  have hQ' : ∀ y : Matrix ι ι ℂ, eval (fun k => evC (Φ k) y) Q = y.det := by
    intro y
    rw [← evC_aeval_invariants, ← evC_det_generic y, ← hQ]
    rfl
  have hset : {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} =
      {z | eval z Q = 1} ∩ ⋂ P : MvPolynomial κ ℂ, ⋂ _ : aeval Φ P = 0, {z | eval z P = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨by rw [hQ', hy], fun P hP => ?_⟩
      rw [← evC_aeval_invariants, hP]
      simp [evC]
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := exists_evC_eq_of_relations Γ Rey κ Φ hR hΦ hgen z h2
      exact ⟨y, by rw [← hQ', h1], rfl⟩
  rw [hset]
  exact (isClosed_eq (MvPolynomial.continuous_eval Q) continuous_const).inter
    (isClosed_iInter fun P => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval P) continuous_const)

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_image_SL_under_generating_invariants : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ] (Φ : κ → MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → (∀ g ∈ Γ, g.det = 1) → (∀ k, IsInv Γ (Φ k)) → (∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) → IsClosed {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} := by
  atlas_forward_decl GlobalTheory.ClassFin.isClosed_image_invariants
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.CosetSep

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def vanC (S : Set (Matrix ι ι ℂ)) : Ideal (MvPolynomial (ι × ι) ℂ) where
  carrier := {f | ∀ g ∈ S, evC f g = 0}
  add_mem' := by
    intro a b ha hb g hg
    have h1 := ha g hg
    have h2 := hb g hg
    simp only [evC] at h1 h2 ⊢
    rw [map_add, h1, h2, add_zero]
  zero_mem' := by
    intro g _
    simp [evC]
  smul_mem' := by
    intro c a ha g hg
    have h1 := ha g hg
    simp only [evC] at h1 ⊢
    rw [smul_eq_mul, map_mul, h1, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma mem_vanC {S : Set (Matrix ι ι ℂ)} {f : MvPolynomial (ι × ι) ℂ} :
    f ∈ vanC S ↔ ∀ g ∈ S, evC f g = 0 := Iff.rfl

omit [DecidableEq ι] in
lemma evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC] at hp hq ⊢
    rw [map_add, map_add, map_add, hp, hq]
  | mul_X p ij hp =>
    simp only [evC] at hp ⊢
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    simp [ltr, Matrix.mul_apply]

omit [DecidableEq ι] in
lemma exists_rtr (h : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    ∃ f' : MvPolynomial (ι × ι) ℂ, ∀ z, evC f' z = evC f (z * h) := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, fun z => by simp [evC]⟩
  | add p q hp hq =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨q', hq⟩ := hq
    refine ⟨p' + q', fun z => ?_⟩
    have h1 := hp z
    have h2 := hq z
    simp only [evC] at h1 h2 ⊢
    rw [map_add, map_add, h1, h2]
  | mul_X p ij hp =>
    obtain ⟨p', hp⟩ := hp
    refine ⟨p' * ∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (h k ij.2), fun z => ?_⟩
    have h1 := hp z
    simp only [evC] at h1 ⊢
    rw [map_mul, map_mul, h1]
    congr 1
    simp [Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_map (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  simp only [evC, ev]
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

lemma mem_of_forall_vanC {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsQGroup Γ) {z : Matrix ι ι ℂ}
    (hz : ∀ f ∈ vanC Γ, evC f z = 0) : z ∈ Γ := by
  apply hΓ.closed
  intro f hf
  rw [← evC_map]
  apply hz
  intro g hg
  rw [evC_map]
  exact hf g hg

lemma vanC_sup_eq_top {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsQGroup Γ) {y : Matrix ι ι ℂ} (hy : y.det = 1)
    (hyΓ : y ∉ Γ) : vanC Γ ⊔ vanC ((fun g => g * y) '' Γ) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨x, rfl⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  set z : Matrix ι ι ℂ := Matrix.of fun i j => x (i, j) with hz
  have key : ∀ f ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ), evC f z = 0 := by
    intro f hf
    have h1 := (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).1 (hle hf)
    simpa [evC, hz] using h1
  have hzΓ : z ∈ Γ := mem_of_forall_vanC hΓ fun f hf => key f (Ideal.mem_sup_left hf)
  have hyy : y * y.adjugate = 1 := by rw [Matrix.mul_adjugate, hy, one_smul]
  have hyy' : y.adjugate * y = 1 := by rw [Matrix.adjugate_mul, hy, one_smul]
  have hwΓ : z * y.adjugate ∈ Γ := by
    refine mem_of_forall_vanC hΓ fun f hf => ?_
    obtain ⟨f', hf'⟩ := exists_rtr y.adjugate f
    rw [← hf']
    refine key f' (Ideal.mem_sup_right ?_)
    rintro _ ⟨g, hg, rfl⟩
    rw [hf', mul_assoc, hyy, mul_one]
    exact hf g hg
  apply hyΓ
  have h1 : (z * y.adjugate).adjugate * (z * y.adjugate) = 1 := by
    rw [Matrix.adjugate_mul, hΓ.det_eq _ hwΓ, one_smul]
  have h2 : y = (z * y.adjugate).adjugate * z := by
    calc y = (z * y.adjugate).adjugate * (z * y.adjugate) * y := by rw [h1, one_mul]
      _ = (z * y.adjugate).adjugate * (z * (y.adjugate * y)) := by simp only [mul_assoc]
      _ = _ := by rw [hyy', mul_one]
  rw [h2]
  exact hΓ.mul_mem _ (hΓ.adj_mem _ hwΓ) _ hzΓ

end GlobalTheory.ClassFin.CosetSep

namespace GlobalTheory.ClassFin

open CosetSep in

theorem exists_isInv_evC_one_ne : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsQGroup Γ → IsReynolds Γ Rey → ∀ y : Matrix ι ι ℂ, y.det = 1 → y ∉ Γ → ∃ f, IsInv Γ f ∧ evC f 1 ≠ evC f y := by
  intro ι _ _ Γ Rey hΓ hR y hy hyΓ
  have htop := vanC_sup_eq_top hΓ hy hyΓ
  have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ) := by
    rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  have hRa : Rey a ∈ vanC Γ := by
    refine hR.stable ((vanC Γ).restrictScalars ℂ) ?_ a ha
    intro g hg f hf h hh
    rw [evC_ltr]
    exact hf _ (hΓ.mul_mem _ hg _ hh)
  have hRb : Rey b ∈ vanC ((fun g => g * y) '' Γ) := by
    refine hR.stable ((vanC ((fun g => g * y) '' Γ)).restrictScalars ℂ) ?_ b hb
    rintro g hg f hf _ ⟨h, hh, rfl⟩
    rw [evC_ltr, ← mul_assoc]
    exact hf _ ⟨g * h, hΓ.mul_mem _ hg _ hh, rfl⟩
  have hR1 : Rey 1 = 1 := hR.fix 1 (fun g _ z => by simp [evC])
  have hsum : Rey a + Rey b = 1 := by rw [← map_add, hab, hR1]
  refine ⟨Rey a, hR.inv a, ?_⟩
  have e1 : evC (Rey a) 1 = 0 := hRa 1 hΓ.one_mem
  have e2 : evC (Rey b) y = 0 := hRb y ⟨1, hΓ.one_mem, one_mul y⟩
  have e3 : evC (Rey a) y = 1 := by
    have h := congrArg (fun f => evC f y) hsum
    simp only [evC] at h e2 ⊢
    rw [map_add, e2, add_zero, map_one] at h
    exact h
  rw [e1, e3]
  exact zero_ne_one

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leftInvariantPoly_separating_coset : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsQGroup Γ → IsReynolds Γ Rey → ∀ y : Matrix ι ι ℂ, y.det = 1 → y ∉ Γ → ∃ f, IsInv Γ f ∧ evC f 1 ≠ evC f y := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_isInv_evC_one_ne
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.HilbertFin

open MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    evC (ltr g f) y = evC f (g * y) := by
  unfold evC ltr
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp]
    simp [Matrix.mul_apply]

omit [DecidableEq ι] in
theorem isInv_iff (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f := by
  constructor
  · intro h g hg
    apply MvPolynomial.funext
    intro x
    have := h g hg (Matrix.of fun i j => x (i, j))
    rw [← evC_ltr] at this
    exact this
  · intro h g hg y
    rw [← evC_ltr, h g hg]

omit [DecidableEq ι] in
theorem ltr_homog (g : Matrix ι ι ℂ) {f : MvPolynomial (ι × ι) ℂ} {n : ℕ}
    (hf : f.IsHomogeneous n) : (ltr g f).IsHomogeneous n := by
  have := hf.aeval (fun ij : ι × ι => ∑ k, MvPolynomial.C (g ij.1 k) * (MvPolynomial.X (k, ij.2) : MvPolynomial (ι × ι) ℂ))
    (n := 1) (fun ij => IsHomogeneous.sum _ _ _ fun k _ => by
      simpa using (isHomogeneous_C (ι × ι) (g ij.1 k)).mul (isHomogeneous_X ℂ (k, ij.2)))
  rw [one_mul] at this
  exact this

omit [DecidableEq ι] in
theorem ltr_comp (g : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) (n : ℕ) :
    ltr g (homogeneousComponent n f) = homogeneousComponent n (ltr g f) := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  conv_rhs => rw [← sum_homogeneousComponent f]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := homogeneousComponent_isHomogeneous i f
  rw [homogeneousComponent_of_mem h1, homogeneousComponent_of_mem (ltr_homog g h1)]
  split_ifs <;> simp

omit [DecidableEq ι] in
theorem isInv_comp {Γ : Set (Matrix ι ι ℂ)} {f : MvPolynomial (ι × ι) ℂ} (hf : IsInv Γ f) (n : ℕ) :
    IsInv Γ (homogeneousComponent n f) := by
  rw [isInv_iff] at hf ⊢
  intro g hg
  rw [ltr_comp, hf g hg]

theorem hilbert_finiteness : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → ∃ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ F ∈ s, IsInv Γ F ∧ ∃ n, F.IsHomogeneous n) ∧ ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
  intro ι _ _ Γ Rey hR
  classical
  set S : Set (MvPolynomial (ι × ι) ℂ) := {F | IsInv Γ F ∧ ∃ n, 0 < n ∧ F.IsHomogeneous n} with hS
  have hfg : (Submodule.span (MvPolynomial (ι × ι) ℂ) S).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).1 hfg
  refine ⟨s, fun F hF => ⟨(hsS hF).1, (hsS hF).2.imp fun n h => h.2⟩, ?_⟩
  have key : ∀ n : ℕ, ∀ f, IsInv Γ f → f.IsHomogeneous n →
      f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have : f = C (coeff 0 f) := by
          rw [← homogeneousComponent_zero, homogeneousComponent_of_mem hn, if_pos rfl]
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      · have hmem : f ∈ Submodule.span (MvPolynomial (ι × ι) ℂ) (s : Set (MvPolynomial (ι × ι) ℂ)) := by
          rw [← hs]
          exact Submodule.subset_span ⟨hf, n, hpos, hn⟩
        obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hmem
        have h1 : f = ∑ F ∈ s, F * Rey (c F) := by
          conv_lhs => rw [← hR.fix f hf, ← hc, map_sum]
          refine Finset.sum_congr rfl fun F hF => ?_
          rw [smul_eq_mul, mul_comm, hR.mul _ _ (hsS hF).1]
        have h2 : f = homogeneousComponent n f := by
          rw [homogeneousComponent_of_mem hn, if_pos rfl]
        rw [h2, h1, map_sum]
        refine Subalgebra.sum_mem _ fun F hF => ?_
        obtain ⟨-, d, hd, hFd⟩ := hsS hF
        rw [← sum_homogeneousComponent (Rey (c F)), Finset.mul_sum, map_sum]
        refine Subalgebra.sum_mem _ fun i _ => ?_
        have h3 := homogeneousComponent_isHomogeneous i (Rey (c F))
        rw [homogeneousComponent_of_mem (hFd.mul h3)]
        split_ifs with h
        · exact Subalgebra.mul_mem _ (Algebra.subset_adjoin hF)
            (ih i (by omega) _ (isInv_comp (hR.inv _) i) h3)
        · exact Subalgebra.zero_mem _
  intro f hf
  rw [← sum_homogeneousComponent f]
  exact Subalgebra.sum_mem _ fun i _ =>
    key i _ (isInv_comp hf i) (homogeneousComponent_isHomogeneous i f)

end GlobalTheory.ClassFin.HilbertFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_finiteness_leftInvariantMatrixPoly : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → ∃ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ F ∈ s, IsInv Γ F ∧ ∃ n, F.IsHomogeneous n) ∧ ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
  atlas_forward_decl GlobalTheory.ClassFin.HilbertFin.hilbert_finiteness
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem invariant_form_eq_sum_invariant_tensors : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ (n : ℕ) (F : MvPolynomial (ι × ι) ℂ), IsInv Γ F → F.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, (∀ b, ∀ g ∈ Γ, l b ᵥ* tpow n g = l b) ∧ ∀ y : Matrix ι ι ℂ, evC F y = ∑ b, (l b ᵥ* tpow n y) b := by
  intro ι _ _ Γ hP hS n F hF hhom
  obtain ⟨-, hinv, -, hp⟩ := GlobalTheory.T.leftTranslateMatrixPoly_tensorForm_properties ι
  obtain ⟨p, hpev, hpl, hpsurj⟩ := hp n
  obtain ⟨l, hl⟩ := hpsurj F hhom
  obtain ⟨R₁, h1a, -, -, h1d, -, -⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' ((Fin n → ι) → ℂ)
    ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.completelyReducible_kroneckerPower_transpose ι Γ hP hS n U (by
        rintro _ ⟨g, hg, rfl⟩ v hv
        simpa [Matrix.toLin'_apply] using hU _ ⟨g, hg, rfl⟩ v hv)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ v hv
      simpa [Matrix.toLin'_apply] using hU' _ ⟨g, hg, rfl⟩ v hv)
  obtain ⟨R₂, -, h2b, h2c, -, -, -⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' (MvPolynomial (ι × ι) ℂ)
    ((fun g => (ltr g).toLinearMap) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.leftTranslateMatrixPoly_completelyReducible ι Γ hP hS U (fun g hg f hf => hU _ ⟨g, hg, rfl⟩ f hf)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ v hv
      exact hU' g hg v hv)
  have hfix : ∀ v, ∀ g ∈ Γ, R₁ v ᵥ* tpow n g = R₁ v := by
    intro v g hg
    have := h1a v _ ⟨g, hg, rfl⟩
    simpa [Matrix.toLin'_apply, Matrix.mulVec_transpose] using this
  have hkill : ∀ b, ∀ x ∈ Submodule.span ℂ
      {x | ∃ s ∈ ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ), ∃ w, x = s w - w}, R₂ (p b x) = 0 := by
    intro b x hx
    have hle : Submodule.span ℂ
        {x | ∃ s ∈ ((fun g => Matrix.toLin' (tpow n g)ᵀ) '' Γ), ∃ w, x = s w - w}
        ≤ LinearMap.ker (R₂ ∘ₗ p b) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨g, hg, rfl⟩, w, rfl⟩
      have h := h2c (p b w) _ ⟨g, hg, rfl⟩
      simp only [AlgHom.toLinearMap_apply, hpl] at h
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, map_sub,
        Matrix.toLin'_apply, Matrix.mulVec_transpose, h, sub_self]
    exact hle hx
  have hb : ∀ b v, R₂ (p b v) = p b (R₁ v) := by
    intro b v
    have h0 := hkill b _ (h1d v)
    rw [map_sub, map_sub, sub_eq_zero] at h0
    rw [h0]
    apply h2b
    rintro _ ⟨g, hg, rfl⟩
    simp only [AlgHom.toLinearMap_apply, hpl, hfix v g hg]
  have hRF : R₂ F = F := by
    apply h2b
    rintro _ ⟨g, hg, rfl⟩
    exact (hinv Γ F).1 hF g hg
  have hF' : F = ∑ b, p b (R₁ (l b)) := by
    rw [← hRF, hl, map_sum]
    exact Finset.sum_congr rfl fun b _ => hb b _
  refine ⟨fun b => R₁ (l b), fun b g hg => hfix _ g hg, fun y => ?_⟩
  rw [hF']
  simp only [← hpev]
  unfold evC
  rw [map_sum]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_form_eq_sum_invariant_tensors' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ (n : ℕ) (F : MvPolynomial (ι × ι) ℂ), IsInv Γ F → F.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, (∀ b, ∀ g ∈ Γ, l b ᵥ* tpow n g = l b) ∧ ∀ y : Matrix ι ι ℂ, evC F y = ∑ b, (l b ᵥ* tpow n y) b := by
  atlas_forward_decl GlobalTheory.ClassFin.invariant_form_eq_sum_invariant_tensors
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RationalInvariants

def invSub {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (n : ℕ) :
    Submodule ℂ ((Fin n → ι) → ℂ) where
  carrier := {μ | ∀ g ∈ Γ, μ ᵥ* tpow n g = μ}
  add_mem' := by
    intro a b ha hb g hg
    rw [Matrix.add_vecMul, ha g hg, hb g hg]
  zero_mem' := by
    intro g _
    exact Matrix.zero_vecMul _
  smul_mem' := by
    intro c a ha g hg
    rw [Matrix.smul_vecMul, ha g hg]

theorem mem_span_rational :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ (n : ℕ) (l : (Fin n → ι) → ℂ), (∀ g ∈ Γ, l ᵥ* tpow n g = l) → l ∈ Submodule.span ℂ {μ : (Fin n → ι) → ℂ | (∀ g ∈ Γ, μ ᵥ* tpow n g = μ) ∧ ∀ a, ∃ q : ℚ, μ a = q} := by
  intro ι _ _ Γ hΓ n l hl
  have h := GlobalTheory.T.galoisStable_submodule_le_span_rational _ _ (Pi.basisFun ℂ (Fin n → ι)) (invSub Γ n) (by
    intro σ w hw
    refine ⟨fun a => σ (w a), ?_, fun k => by simp⟩
    intro g hg
    funext b
    have h1 := congrArg σ (congrFun (hw _ (hΓ σ.symm g hg)) b)
    rw [← h1]
    simp [Matrix.vecMul, dotProduct, tpow, map_sum, map_prod])
  have h2 := h (show l ∈ invSub Γ n from hl)
  simp only [Pi.basisFun_repr] at h2
  exact h2

end GlobalTheory.ClassFin.RationalInvariants
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_rational_kroneckerInvariants : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ (n : ℕ) (l : (Fin n → ι) → ℂ), (∀ g ∈ Γ, l ᵥ* tpow n g = l) → l ∈ Submodule.span ℂ {μ : (Fin n → ι) → ℂ | (∀ g ∈ Γ, μ ᵥ* tpow n g = μ) ∧ ∀ a, ∃ q : ℚ, μ a = q} := by
  atlas_forward_decl GlobalTheory.ClassFin.RationalInvariants.mem_span_rational
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatInvTensor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def coordAlg (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Subalgebra ℂ (Matrix ι ι ℂ → ℂ) :=
  Algebra.adjoin ℂ {φ | ∃ p ∈ S, ∃ b, φ = fun y => ((fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 y) b}

def AllFixed (Γ : Set (Matrix ι ι ℂ)) (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Prop :=
  ∀ p ∈ S, ∀ g ∈ Γ, (fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 g = fun a => ((p.2 a : ℚ) : ℂ)

def Good (Γ : Set (Matrix ι ι ℂ)) (φ : Matrix ι ι ℂ → ℂ) : Prop :=
  ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧ φ ∈ coordAlg S

theorem coordAlg_mono {S T : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))} (h : S ⊆ T) : coordAlg S ≤ coordAlg T := by
  apply Algebra.adjoin_mono
  rintro φ ⟨p, hp, b, rfl⟩
  exact ⟨p, h hp, b, rfl⟩

theorem good_zero (Γ : Set (Matrix ι ι ℂ)) : Good Γ 0 :=
  ⟨∅, Set.finite_empty, fun _ h => h.elim, Subalgebra.zero_mem _⟩

theorem Good.add {Γ : Set (Matrix ι ι ℂ)} {φ ψ : Matrix ι ι ℂ → ℂ} (h1 : Good Γ φ) (h2 : Good Γ ψ) :
    Good Γ (φ + ψ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  obtain ⟨T, hT, fT, mT⟩ := h2
  refine ⟨S ∪ T, hS.union hT, ?_, Subalgebra.add_mem _ (coordAlg_mono Set.subset_union_left mS)
    (coordAlg_mono Set.subset_union_right mT)⟩
  rintro p (hp | hp)
  · exact fS p hp
  · exact fT p hp

theorem Good.smul {Γ : Set (Matrix ι ι ℂ)} {φ : Matrix ι ι ℂ → ℂ} (c : ℂ) (h1 : Good Γ φ) :
    Good Γ (c • φ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  exact ⟨S, hS, fS, Subalgebra.smul_mem _ mS c⟩

theorem good_sum {Γ : Set (Matrix ι ι ℂ)} {β : Type} (s : Finset β) (φ : β → Matrix ι ι ℂ → ℂ)
    (h : ∀ b, Good Γ (φ b)) : Good Γ (∑ b ∈ s, φ b) :=
  Finset.sum_induction φ (Good Γ) (fun _ _ => Good.add) (good_zero Γ) (fun b _ => h b)

theorem good_coord {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (n : ℕ) (l : (Fin n → ι) → ℂ)
    (hl : ∀ g ∈ Γ, l ᵥ* tpow n g = l) (b : Fin n → ι) : Good Γ (fun y => (l ᵥ* tpow n y) b) := by
  have h := GlobalTheory.T.mem_span_rational_kroneckerInvariants ι Γ hΓ.aut_mem n l hl
  clear hl
  induction h using Submodule.span_induction with
  | mem μ hμ =>
    obtain ⟨h1, h2⟩ := hμ
    choose q hq using h2
    have hμ : μ = fun a => ((q a : ℚ) : ℂ) := funext hq
    subst hμ
    refine ⟨{⟨n, q⟩}, Set.finite_singleton _, ?_, Algebra.subset_adjoin ⟨⟨n, q⟩, rfl, b, rfl⟩⟩
    rintro p rfl
    exact h1
  | zero =>
    have : (fun y : Matrix ι ι ℂ => ((0 : (Fin n → ι) → ℂ) ᵥ* tpow n y) b) = 0 := by
      funext y; simp
    rw [this]; exact good_zero Γ
  | add u v _ _ hu hv =>
    have : (fun y : Matrix ι ι ℂ => ((u + v) ᵥ* tpow n y) b) =
        (fun y => (u ᵥ* tpow n y) b) + fun y => (v ᵥ* tpow n y) b := by
      funext y; simp [Matrix.add_vecMul]
    rw [this]; exact hu.add hv
  | smul c u _ hu =>
    have : (fun y : Matrix ι ι ℂ => ((c • u) ᵥ* tpow n y) b) =
        c • (fun y => (u ᵥ* tpow n y) b) := by
      funext y; simp [Matrix.smul_vecMul]
    rw [this]; exact hu.smul c

theorem good_homog {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) (n : ℕ)
    (F : MvPolynomial (ι × ι) ℂ) (hF : IsInv Γ F) (hn : F.IsHomogeneous n) : Good Γ (evC F) := by
  obtain ⟨l, hl, hev⟩ := GlobalTheory.T.invariant_form_eq_sum_invariant_tensors' ι Γ hΓ hS n F hF hn
  have : evC F = ∑ b, fun y => (l b ᵥ* tpow n y) b := by
    funext y; rw [hev, Finset.sum_apply]
  rw [this]
  exact good_sum _ _ fun b => good_coord hΓ n (l b) (hl b) b

theorem exists_finite_family {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) :
    ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧
      ∀ f, IsInv Γ f → evC f ∈ coordAlg S := by
  obtain ⟨Rey, hR⟩ := GlobalTheory.T.exists_leftTranslation_reynoldsOperator ι Γ hΓ hS
  obtain ⟨s, hs, hgen⟩ := GlobalTheory.T.hilbert_finiteness_leftInvariantMatrixPoly ι Γ Rey hR
  have hg : ∀ F : s, Good Γ (evC F.1) := fun F => by
    obtain ⟨h1, n, h2⟩ := hs F.1 F.2
    exact good_homog hΓ hS n F.1 h1 h2
  choose S hfin hfix hmem using hg
  refine ⟨⋃ F, S F, Set.finite_iUnion hfin, ?_, ?_⟩
  · intro p hp
    obtain ⟨F, hF⟩ := Set.mem_iUnion.1 hp
    exact hfix F p hF
  · intro f hf
    have h := hgen f hf
    clear hf
    induction h using Algebra.adjoin_induction with
    | mem F hF => exact coordAlg_mono (Set.subset_iUnion S ⟨F, hF⟩) (hmem ⟨F, hF⟩)
    | algebraMap c =>
      have : evC (algebraMap ℂ (MvPolynomial (ι × ι) ℂ) c) = algebraMap ℂ (Matrix ι ι ℂ → ℂ) c := by
        funext y; simp [evC]
      rw [this]; exact Subalgebra.algebraMap_mem _ c
    | add u v _ _ hu hv =>
      have : evC (u + v) = evC u + evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv =>
      have : evC (u * v) = evC u * evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.mul_mem _ hu hv

theorem exists_rational_invariant_tensor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ ∀ f, IsInv Γ f → ∃ P : MvPolynomial (TIdx ι d) ℂ, ∀ y : Matrix ι ι ℂ, evC f y = MvPolynomial.eval (act d (fun k => ((t k : ℚ) : ℂ)) y) P := by
  intro ι _ _ Γ hΓ hS
  obtain ⟨S, hfin, hfix, hmem⟩ := exists_finite_family hΓ hS
  obtain ⟨m, e, -, he⟩ := hfin.fin_param
  refine ⟨m, fun i => (e i).1, fun k => (e k.1).2 k.2, ?_, ?_⟩
  · intro g hg
    funext k
    exact congrFun (hfix (e k.1) (he ▸ Set.mem_range_self _) g hg) k.2
  · intro f hf
    have h := hmem f hf
    generalize evC f = φ at h
    induction h using Algebra.adjoin_induction with
    | mem φ hφ =>
      obtain ⟨p, hp, b, rfl⟩ := hφ
      rw [← he] at hp
      obtain ⟨i, rfl⟩ := hp
      exact ⟨MvPolynomial.X ⟨i, b⟩, fun y => by rw [MvPolynomial.eval_X]; rfl⟩
    | algebraMap c => exact ⟨MvPolynomial.C c, fun y => by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P + Q, fun y => by rw [map_add, ← hP, ← hQ]; rfl⟩
    | mul u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P * Q, fun y => by rw [map_mul, ← hP, ← hQ]; rfl⟩

end GlobalTheory.ClassFin.RatInvTensor
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_invariant_tensor' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ ∀ f, IsInv Γ f → ∃ P : MvPolynomial (TIdx ι d) ℂ, ∀ y : Matrix ι ι ℂ, evC f y = MvPolynomial.eval (act d (fun k => ((t k : ℚ) : ℂ)) y) P := by
  atlas_forward_decl GlobalTheory.ClassFin.RatInvTensor.exists_rational_invariant_tensor
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_mvPolynomial_ev_eq_act : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), ∃ Φ : TIdx ι d → MvPolynomial (ι × ι) ℚ, ∀ (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) (k : TIdx ι d), ev (Φ k) y = act d (fun k => algebraMap ℚ R (t k)) y k := by
  intro ι _ _ m d t
  refine ⟨fun k => ∑ a : Fin (d k.1) → ι,
    MvPolynomial.C (t ⟨k.1, a⟩) * ∏ i, MvPolynomial.X (a i, k.2 i), ?_⟩
  intro R _ _ y k
  simp [ev, act, tpow, Matrix.vecMul, dotProduct, map_sum, map_prod,
    MvPolynomial.aeval_X]

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratPoly_eval_eq_tensorPowerSumRightAction : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), ∃ Φ : TIdx ι d → MvPolynomial (ι × ι) ℚ, ∀ (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) (k : TIdx ι d), ev (Φ k) y = act d (fun k => algebraMap ℚ R (t k)) y k := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_mvPolynomial_ev_eq_act
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_tensor_stabiliser_closed_orbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ (∀ y : Matrix ι ι ℂ, y.det = 1 → act d (fun k => ((t k : ℚ) : ℂ)) y = (fun k => ((t k : ℚ) : ℂ)) → y ∈ Γ) ∧ IsClosed (orb d (fun k => ((t k : ℚ) : ℂ))) := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨Rey, hRey⟩ := GlobalTheory.T.exists_leftTranslation_reynoldsOperator ι Γ hΓ.toIsPre hss
  obtain ⟨m, d, t, hfix, hgen⟩ := GlobalTheory.T.exists_rational_invariant_tensor' ι Γ hΓ.toIsPre hss
  obtain ⟨h1, hmul, -⟩ := (GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℂ).2 m d (fun k => ((t k : ℚ) : ℂ))
  refine ⟨m, d, t, hfix, ?_, ?_⟩
  · intro y hy hyt
    by_contra hn
    obtain ⟨f, hf, hne⟩ := GlobalTheory.T.exists_leftInvariantPoly_separating_coset ι Γ Rey hΓ hRey y hy hn
    obtain ⟨P, hP⟩ := hgen f hf
    apply hne
    rw [hP, hP, h1, hyt]
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_ratPoly_eval_eq_tensorPowerSumRightAction ι m d t
    have hev : ∀ (y : Matrix ι ι ℂ) (k : TIdx ι d),
        evC (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) y = act d (fun k => ((t k : ℚ) : ℂ)) y k := by
      intro y k
      have h := hΦ ℂ y k
      simp only [eq_ratCast] at h
      rw [← h, evC, ev, MvPolynomial.eval_map, MvPolynomial.aeval_def]
    have hcl := GlobalTheory.T.isClosed_image_SL_under_generating_invariants ι Γ Rey (TIdx ι d) (fun k => MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) hRey
      hΓ.det_eq (fun k g hg y => by rw [hev, hev, hmul, hfix g hg]) (fun f hf => by
        obtain ⟨P, hP⟩ := hgen f hf
        rw [Algebra.adjoin_range_eq_range_aeval]
        refine ⟨P, ?_⟩
        apply MvPolynomial.funext
        intro x
        have h := hP (Matrix.of fun i j => x (i, j))
        have hx : (fun ij : ι × ι => (Matrix.of fun i j => x (i, j)) ij.1 ij.2) = x := rfl
        have h2 : act d (fun k => ((t k : ℚ) : ℂ)) (Matrix.of fun i j => x (i, j)) =
            fun k => MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) := by
          funext k
          rw [← hev, evC, hx]
        rw [evC, hx, h2] at h
        rw [h]
        show MvPolynomial.eval x (MvPolynomial.aeval _ P) = _
        clear hP h
        induction P using MvPolynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p n hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X])
    have : orb d (fun k => ((t k : ℚ) : ℂ)) = {z : TIdx ι d → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧
        z = fun k => evC (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) y} := by
      ext z
      simp only [orb, hev]
    rw [this]
    exact hcl

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_stabiliser_closed_SL_orbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ (∀ y : Matrix ι ι ℂ, y.det = 1 → act d (fun k => ((t k : ℚ) : ℂ)) y = (fun k => ((t k : ℚ) : ℂ)) → y ∈ Γ) ∧ IsClosed (orb d (fun k => ((t k : ℚ) : ℂ))) := by
  atlas_forward_decl GlobalTheory.ClassFin.exists_tensor_stabiliser_closed_orbit
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_matrix_span_of_smul_mem {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) (N : ℤ)
    (hN : N ≠ 0) (hL : ∀ v : ι → ℤ, N • v ∈ L) :
    ∃ H : Matrix ι ι ℤ, (∀ j, (fun i => H i j) ∈ L) ∧ ∀ v ∈ L, ∃ c : ι → ℤ, v = H *ᵥ c := by
  have hr : Module.finrank ℤ L = Fintype.card ι := by
    apply le_antisymm
    · simpa using Submodule.finrank_le L
    · let f : (ι → ℤ) →ₗ[ℤ] L := LinearMap.codRestrict L (N • LinearMap.id) hL
      have hf : Function.Injective f := by
        intro a b hab
        have : N • a = N • b := congrArg Subtype.val hab
        exact smul_right_injective _ hN this
      simpa using LinearMap.finrank_le_finrank_of_injective hf
  let b : Module.Basis ι ℤ L := (Module.finBasisOfFinrankEq ℤ L hr).reindex (Fintype.equivFin ι).symm
  refine ⟨Matrix.of fun i j => (b j : ι → ℤ) i, fun j => (b j).2, fun v hv => ⟨b.repr ⟨v, hv⟩, ?_⟩⟩
  have := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
  funext i
  have h2 := congrFun this i
  simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem exists_matrix_basis_of_lattice {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℚ)) (M : ℕ)
    (hM : 0 < M) (h1 : ∀ v ∈ L, ∀ i, ∃ z : ℤ, (M : ℚ) * v i = z)
    (h2 : ∀ z : ι → ℤ, (fun i => (M : ℚ) * z i) ∈ L) :
    ∃ h g : Matrix ι ι ℚ, h * g = 1 ∧ (∀ j, (fun i => h i j) ∈ L) ∧ ∀ v ∈ L, ∀ i, ∃ z : ℤ, (g *ᵥ v) i = z := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  let φ : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) :=
    { toFun := fun z i => (M : ℚ)⁻¹ * z i
      map_add' := fun a b => by funext i; simp [mul_add]
      map_smul' := fun a b => by funext i; simp; ring }
  obtain ⟨H, hH, hc⟩ := exists_matrix_span_of_smul_mem (L.comap φ) ((M : ℤ) * M)
    (by have := hM.ne'; positivity) (fun v => by
      have : φ (((M : ℤ) * M) • v) = fun i => (M : ℚ) * v i := by
        funext i
        simp [φ]
        field_simp
      simp only [Submodule.mem_comap, this]
      exact h2 v)
  let h : Matrix ι ι ℚ := Matrix.of fun i j => (M : ℚ)⁻¹ * H i j
  have key : ∀ v ∈ L, ∃ c : ι → ℤ, v = h *ᵥ fun i => (c i : ℚ) := by
    intro v hv
    choose z hz using h1 v hv
    have hφ : φ z = v := by
      funext i
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, ← hz]
      field_simp
    obtain ⟨c, hc'⟩ := hc z (by simpa [hφ] using hv)
    refine ⟨c, ?_⟩
    rw [← hφ, hc']
    funext i
    simp [φ, h, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  choose C hC using fun j => key _ (h2 (Pi.single j 1))
  let g : Matrix ι ι ℚ := Matrix.of fun i j => (M : ℚ)⁻¹ * C j i
  have hg : h * g = 1 := by
    ext i j
    have := congrFun (hC j) i
    simp only [Matrix.mulVec, dotProduct] at this
    have e : (h * g) i j = (M : ℚ)⁻¹ * ∑ k, h i k * (C j k : ℚ) := by
      simp only [Matrix.mul_apply, g, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, ← this]
    by_cases hij : i = j
    · subst hij; simp [hM']
    · simp [hij]
  refine ⟨h, g, hg, fun j => hH j, fun v hv i => ?_⟩
  obtain ⟨c, rfl⟩ := key v hv
  refine ⟨c i, ?_⟩
  rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp hg, Matrix.one_mulVec]

theorem det_mem_subring_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R] (R₀ : Subring R)
    (k : Matrix ι ι R) (hk : ∀ i j, k i j ∈ R₀) : k.det ∈ R₀ := by
  rw [Matrix.det_apply']
  exact R₀.sum_mem fun σ _ => R₀.mul_mem (intCast_mem R₀ _) (R₀.prod_mem fun i _ => hk _ _)

theorem sl_class_number_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), AdelicPair R R₀ → ∀ x : Matrix ι ι R, x.det = 1 → ∃ (h : Matrix ι ι ℚ) (k : Matrix ι ι R), h.det = 1 ∧ k.det = 1 ∧ (∀ i j, k i j ∈ R₀) ∧ x = h.map (algebraMap ℚ R) * k := by
  intro ι _ _ R _ _ R₀ hp x hx
  obtain ⟨-, hden, hinj⟩ := adelicPair_elementary R R₀ hp
  set y := x.adjugate with hy
  have hxy : x * y = 1 := by rw [hy, Matrix.mul_adjugate, hx, one_smul]
  have hyx : y * x = 1 := mul_eq_one_comm.mp hxy
  obtain ⟨M, hM, hMr⟩ := hden ((ι × ι) ⊕ (ι × ι)) (Sum.elim (fun p => x p.1 p.2) (fun p => y p.1 p.2))
  have hMx : ∀ i j, (M : R) * x i j ∈ R₀ := fun i j => hMr (Sum.inl (i, j))
  have hMy : ∀ i j, (M : R) * y i j ∈ R₀ := fun i j => hMr (Sum.inr (i, j))
  let L : Submodule ℤ (ι → ℚ) := AddSubgroup.toIntSubmodule
    { carrier := {v | ∀ i, ∑ k, y i k * algebraMap ℚ R (v k) ∈ R₀}
      add_mem' := fun {a b} ha hb i => by
        simpa [mul_add, Finset.sum_add_distrib] using R₀.add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      neg_mem' := fun {a} ha i => by simpa using R₀.neg_mem (ha i) }
  have hLm : ∀ v, v ∈ L ↔ ∀ i, ∑ k, y i k * algebraMap ℚ R (v k) ∈ R₀ := fun v => Iff.rfl
  have h2 : ∀ z : ι → ℤ, (fun i => (M : ℚ) * z i) ∈ L := by
    intro z
    rw [hLm]
    intro i
    refine R₀.sum_mem fun k _ => ?_
    have : y i k * algebraMap ℚ R ((M : ℚ) * z k) = (M : R) * y i k * z k := by simp; ring
    rw [this]
    exact R₀.mul_mem (hMy _ _) (intCast_mem R₀ _)
  have h1 : ∀ v ∈ L, ∀ i, ∃ z : ℤ, (M : ℚ) * v i = z := by
    intro v hv i
    apply hp.int_of_mem
    have e : (fun k => algebraMap ℚ R (v k)) = x *ᵥ (y *ᵥ fun k => algebraMap ℚ R (v k)) := by
      rw [Matrix.mulVec_mulVec, hxy, Matrix.one_mulVec]
    have e' := congrFun e i
    rw [map_mul, map_natCast, e']
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine R₀.sum_mem fun k _ => ?_
    rw [← mul_assoc]
    exact R₀.mul_mem (hMx _ _) ((hLm v).1 hv k)
  obtain ⟨h, g, hg, hh, hgL⟩ := exists_matrix_basis_of_lattice L M hM h1 h2
  have hMg : ∀ i j, (M : R) * algebraMap ℚ R (g i j) ∈ R₀ := by
    intro i j
    obtain ⟨z, hz⟩ := hgL _ (h2 (Pi.single j 1)) i
    have : (M : ℚ) * g i j = z := by
      rw [← hz]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j]
      · simp [mul_comm]
      · intro b _ hb; simp [hb]
      · simp
    have e : (M : R) * algebraMap ℚ R (g i j) = (z : R) := by
      rw [← map_natCast (algebraMap ℚ R), ← map_mul, this, map_intCast]
    rw [e]
    exact intCast_mem R₀ _
  have hk : ∀ i j, (g.map (algebraMap ℚ R) * x) i j ∈ R₀ := by
    intro i j
    choose q a ha hqa using fun k => hp.approx M hM (x k j)
    have hq : q ∈ L := by
      rw [hLm]
      intro l
      have e : ∑ k, y l k * algebraMap ℚ R (q k) = (y * x) l j - ∑ k, (M : R) * y l k * a k := by
        rw [Matrix.mul_apply, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [hqa k]; ring
      rw [e, hyx]
      refine R₀.sub_mem ?_ (R₀.sum_mem fun k _ => R₀.mul_mem (hMy _ _) (ha k))
      rw [Matrix.one_apply]
      split_ifs
      exacts [R₀.one_mem, R₀.zero_mem]
    obtain ⟨z, hz⟩ := hgL q hq i
    have e : (g.map (algebraMap ℚ R) * x) i j =
        algebraMap ℚ R ((g *ᵥ q) i) + ∑ k, (M : R) * algebraMap ℚ R (g i k) * a k := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, map_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [hqa k]; ring
    rw [e, hz, map_intCast]
    exact R₀.add_mem (intCast_mem R₀ _) (R₀.sum_mem fun k _ => R₀.mul_mem (hMg _ _) (ha k))
  have hk' : ∀ i j, (y * h.map (algebraMap ℚ R)) i j ∈ R₀ := fun i j => (hLm _).1 (hh j) i
  have hmd : ∀ t : Matrix ι ι ℚ, (t.map (algebraMap ℚ R)).det = algebraMap ℚ R t.det := fun t =>
    ((algebraMap ℚ R).map_det t).symm
  have hdy : y.det = 1 := by
    have := congrArg Matrix.det hxy
    rwa [Matrix.det_mul, hx, one_mul, Matrix.det_one] at this
  obtain ⟨zg, hzg⟩ := hp.int_of_mem g.det (by
    have := det_mem_subring_of_entries R₀ _ hk
    rwa [Matrix.det_mul, hx, mul_one, hmd] at this)
  obtain ⟨zh, hzh⟩ := hp.int_of_mem h.det (by
    have := det_mem_subring_of_entries R₀ _ hk'
    rwa [Matrix.det_mul, hdy, one_mul, hmd] at this)
  have hdd : h.det * g.det = 1 := by rw [← Matrix.det_mul, hg, Matrix.det_one]
  have hz : zh * zg = 1 := by
    rw [hzg, hzh] at hdd
    exact_mod_cast hdd
  have hxe : x = h.map (algebraMap ℚ R) * (g.map (algebraMap ℚ R) * x) := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, hg]
    simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hz with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨h, _, by simp [hzh, e1], ?_, hk, hxe⟩
    rw [Matrix.det_mul, hx, hmd, hzg, e2]
    simp
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · rw [Matrix.det_isEmpty, e1] at hzh
      norm_num at hzh
    · let d : ι → ℚ := fun i => if i = i₀ then -1 else 1
      have hd : (Matrix.diagonal d).det = -1 := by simp [d]
      have hdd2 : Matrix.diagonal d * Matrix.diagonal d = 1 := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        by_cases hi : i = i₀ <;> simp [d, hi]
      refine ⟨h * Matrix.diagonal d, (Matrix.diagonal d).map (algebraMap ℚ R) * (g.map (algebraMap ℚ R) * x),
        ?_, ?_, ?_, ?_⟩
      · rw [Matrix.det_mul, hd, hzh, e1]
        simp
      · rw [Matrix.det_mul, Matrix.det_mul, hx, hmd, hmd, hd, hzg, e2]
        simp
      · intro i j
        rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
        refine R₀.mul_mem ?_ (hk i j)
        by_cases hi : i = i₀
        · simpa [d, hi] using R₀.neg_mem R₀.one_mem
        · simpa [d, hi] using R₀.one_mem
      · rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_assoc h, hdd2, Matrix.mul_one]
        exact hxe

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialLinear_classNumber_one_adelic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), AdelicPair R R₀ → ∀ x : Matrix ι ι R, x.det = 1 → ∃ (h : Matrix ι ι ℚ) (k : Matrix ι ι R), h.det = 1 ∧ k.det = 1 ∧ (∀ i j, k i j ∈ R₀) ∧ x = h.map (algebraMap ℚ R) * k := by
  atlas_forward_decl GlobalTheory.ClassFin.sl_class_number_one
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem adjugate_entry_mem_subring {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]
    (S : Subring R) (k : Matrix ι ι R) (hk : ∀ i j, k i j ∈ S) : ∀ i j, k.adjugate i j ∈ S := by
  intro i j
  let k' : Matrix ι ι S := Matrix.of fun i j => ⟨k i j, hk i j⟩
  have h1 : k = S.subtype.mapMatrix k' := by ext i j; rfl
  rw [h1, ← RingHom.map_adjugate]
  exact (k'.adjugate i j).2

theorem mul_entry_mem_subring {ι : Type} [Fintype ι] {R : Type} [CommRing R]
    (S : Subring R) (k l : Matrix ι ι R) (hk : ∀ i j, k i j ∈ S) (hl : ∀ i j, l i j ∈ S) :
    ∀ i j, (k * l) i j ∈ S := by
  intro i j
  rw [Matrix.mul_apply]
  exact S.sum_mem fun a _ => S.mul_mem (hk _ _) (hl _ _)

theorem cf_of_ss : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → SS Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  intro ι _ _ Γ R _ _ R₀ hΓ hss hA
  classical
  obtain ⟨m, d, t, hfix, hstab, hcl⟩ := GlobalTheory.T.exists_tensor_stabiliser_closed_SL_orbit ι Γ hΓ hss
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_ratPoly_eval_eq_tensorPowerSumRightAction ι m d t
  obtain ⟨-, hmul, hadj, hdet⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι Γ hΓ.toIsPre R
  obtain ⟨hrat, hratR⟩ := GlobalTheory.T.rat_mem_ratZariskiClosurePoints ι Γ
  obtain ⟨D, hD, hDt⟩ := (adelicPair_elementary R R₀ hA).2.1 (TIdx ι d) (fun k => algebraMap ℚ R (t k))
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.finite_integral_classes_closedOrbit ι m d t hcl D hD
  have hone : ∀ (S : Type) [CommRing S] (s : TIdx ι d → S), act d s 1 = s :=
    fun S _ s => ((tpow_act_algebra ι S).2 m d s).1
  have hact : ∀ (S : Type) [CommRing S] (s : TIdx ι d → S) (y z : Matrix ι ι S),
      act d s (y * z) = act d (act d s y) z :=
    fun S _ s => ((tpow_act_algebra ι S).2 m d s).2.1
  have hmap : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (s : TIdx ι d → ℚ) (y : Matrix ι ι ℚ),
      act d (fun k => algebraMap ℚ S (s k)) (y.map (algebraMap ℚ S)) = fun k => algebraMap ℚ S (act d s y k) :=
    fun S _ _ s y => ((tpow_act_algebra ι ℚ).2 m d s).2.2.2.2.2 S (algebraMap ℚ S) y

  have hfixR : ∀ x ∈ pts Γ R, act d (fun k => algebraMap ℚ R (t k)) x = fun k => algebraMap ℚ R (t k) := by
    intro x hx
    funext k
    have hv : Φ k - MvPolynomial.C (t k) ∈ vanI Γ := by
      intro g hg
      have h1 := hΦ ℂ g k
      have h2 := congrFun (hfix g hg) k
      simp only [ev, map_sub, MvPolynomial.aeval_C] at h1 ⊢
      rw [h1, sub_eq_zero]
      exact h2
    have h3 := hx _ hv
    have h1 := hΦ R x k
    simp only [ev, map_sub, MvPolynomial.aeval_C] at h1 h3
    rw [← h1]
    exact sub_eq_zero.1 h3
  let P : (TIdx ι d → ℚ) → Matrix ι ι ℚ × Matrix ι ι R → Prop := fun z p =>
    p.1.det = 1 ∧ p.2.det = 1 ∧ (∀ i j, p.2 i j ∈ R₀) ∧ p.1.map (algebraMap ℚ R) * p.2 ∈ pts Γ R ∧
      act d t p.1 = z
  have key : ∀ x ∈ pts Γ R, ∃ z ∈ Z, ∃ p, P z p ∧ x = p.1.map (algebraMap ℚ R) * p.2 := by
    intro x hx
    obtain ⟨h, k, hh, hk, hkint, rfl⟩ := GlobalTheory.T.specialLinear_classNumber_one_adelic ι R R₀ hA x (hdet x hx)
    have hkk : k * k.adjugate = 1 := by rw [Matrix.mul_adjugate, hk, one_smul]
    have e1 : act d (fun k => algebraMap ℚ R (t k)) k.adjugate = fun k => algebraMap ℚ R (act d t h k) := by
      rw [← hmap]
      conv_lhs => rw [← hfixR _ hx, ← hact, Matrix.mul_assoc, hkk, Matrix.mul_one]
    have e2 : ∀ j, ∃ z : ℤ, (D : ℚ) * act d t h j = z := by
      intro j
      apply hA.int_of_mem
      have h1 := ((tpow_act_algebra ι R).2 m d ((D : R) • fun k => algebraMap ℚ R (t k))).2.2.2.1 R₀
        k.adjugate (fun k => hDt k) (adjugate_entry_mem_subring R₀ k hkint) j
      rw [((tpow_act_algebra ι R).2 m d (fun k => algebraMap ℚ R (t k))).2.2.2.2.1, e1] at h1
      rw [map_mul, map_natCast]
      exact h1
    obtain ⟨γ, hγ, hγZ⟩ := hZ h hh e2
    have hγγ : γ * γ.adjugate = 1 := by rw [Matrix.mul_adjugate, hγ, one_smul]
    have hγR : (γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) * γ.adjugate.map (Int.castRingHom R) = 1 := by
      have : (γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) = γ.map (Int.castRingHom R) := by
        ext i j; simp
      rw [this, ← Matrix.map_mul, hγγ, Matrix.map_one _ (map_zero _) (map_one _)]
    have e3 : (h * γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) * (γ.adjugate.map (Int.castRingHom R) * k)
        = h.map (algebraMap ℚ R) * k := by
      rw [Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ k, hγR, Matrix.one_mul]
    refine ⟨_, hγZ, (h * γ.map (Int.cast : ℤ → ℚ), γ.adjugate.map (Int.castRingHom R) * k),
      ⟨?_, ?_, ?_, ?_, rfl⟩, e3.symm⟩
    · have : (γ.map (Int.cast : ℤ → ℚ)).det = 1 := by
        have h1 := (Int.castRingHom ℚ).map_det γ
        rw [hγ, map_one] at h1
        exact h1.symm
      simp only [Matrix.det_mul, hh, this, one_mul]
    · have : (γ.adjugate.map (Int.castRingHom R)).det = 1 := by
        have h1 := (Int.castRingHom R).map_det γ.adjugate
        rw [Matrix.det_adjugate, hγ, one_pow, map_one] at h1
        exact h1.symm
      simp only [Matrix.det_mul, hk, this, one_mul]
    · exact mul_entry_mem_subring R₀ _ _ (fun i j => intCast_mem R₀ _) hkint
    · simp only
      rw [e3]; exact hx
  let c : (TIdx ι d → ℚ) → Matrix ι ι ℚ × Matrix ι ι R := fun z =>
    if hz : ∃ p, P z p then hz.choose else (1, 1)
  have hc : ∀ z, (∃ p, P z p) → P z (c z) := by
    intro z hz
    simp only [c, dif_pos hz]
    exact hz.choose_spec
  refine ⟨(Z.filter fun z => ∃ p, P z p).image fun z => (c z).1.map (algebraMap ℚ R) * (c z).2, ?_, ?_⟩
  · intro s hs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hs
    exact (hc z (Finset.mem_filter.1 hz).2).2.2.2.1
  · intro x hx
    obtain ⟨z, hz, ⟨h, k⟩, hp, rfl⟩ := key x hx
    have hz' : z ∈ Z.filter fun z => ∃ p, P z p := Finset.mem_filter.2 ⟨hz, _, hp⟩
    have hq := hc z ⟨_, hp⟩
    have hs := Finset.mem_image_of_mem (fun z => (c z).1.map (algebraMap ℚ R) * (c z).2) hz'
    generalize (Z.filter fun z => ∃ p, P z p).image (fun z => (c z).1.map (algebraMap ℚ R) * (c z).2) = T at hs ⊢
    generalize c z = q at hq hs
    obtain ⟨h', k'⟩ := q
    obtain ⟨hh, hk, hkint, hxx, hhz⟩ := hp
    obtain ⟨hh', hk', hkint', hxx', hhz'⟩ := hq
    simp only at hh hk hkint hxx hhz hh' hk' hkint' hxx' hhz' hs ⊢
    have a1 : h' * h'.adjugate = 1 := by rw [Matrix.mul_adjugate, hh', one_smul]
    have a2 : h'.adjugate * h' = 1 := by rw [Matrix.adjugate_mul, hh', one_smul]
    have a3 : k' * k'.adjugate = 1 := by rw [Matrix.mul_adjugate, hk', one_smul]
    have g1 : act d t (h * h'.adjugate) = t := by
      rw [hact, hhz, ← hhz', ← hact, a1, hone]
    have g2 : h * h'.adjugate ∈ pts Γ ℚ := by
      apply hrat
      apply hstab
      · have h1 := (algebraMap ℚ ℂ).map_det (h * h'.adjugate)
        rw [Matrix.det_mul, Matrix.det_adjugate, hh, hh', one_pow, one_mul, map_one] at h1
        exact h1.symm
      · have h1 := hmap ℂ t (h * h'.adjugate)
        rw [g1] at h1
        exact h1
    have g3 := hratR R _ g2
    have e : h.map (algebraMap ℚ R) * k = (h * h'.adjugate).map (algebraMap ℚ R) *
        (h'.map (algebraMap ℚ R) * k') * (k'.adjugate * k) := by
      rw [← Matrix.mul_assoc _ _ k', ← Matrix.map_mul, Matrix.mul_assoc h, a2, Matrix.mul_one,
        Matrix.mul_assoc, ← Matrix.mul_assoc k', a3, Matrix.one_mul]
    refine ⟨_, g2, _, hs, k'.adjugate * k, ?_,
      mul_entry_mem_subring R₀ _ _ (adjugate_entry_mem_subring R₀ k' hkint') hkint, e⟩
    have g4 := hmul _ g3 _ hxx'
    have g5 := hmul _ (hadj _ g4) _ hxx
    rw [e, ← Matrix.mul_assoc, Matrix.adjugate_mul, hdet _ g4, one_smul, Matrix.one_mul] at g5
    exact g5

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFiniteness_completelyReducible : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → SS Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  atlas_forward_decl GlobalTheory.ClassFin.cf_of_ss
end
