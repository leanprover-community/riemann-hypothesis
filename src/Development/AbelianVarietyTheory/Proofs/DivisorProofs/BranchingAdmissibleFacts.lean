import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsBasisAtBlock
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColAddGenRenameCastSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingListCharacterProduct

section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

theorem rowDiv_succ_rec (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) (k : ℕ) :
    ((k : MvPolynomial (Fin r × Fin m) R) + 1) * rowDiv R a b (k + 1) f +
      (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) R) * rowDiv R a b k f =
      rowE R r m a b (rowDiv R a b k f) := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on generalizing k with
  | C c =>
    have h : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c) := by
      simp [rowGen]
    rw [h]
    cases k with
    | zero => simp [rowE_C, Polynomial.coeff_C]
    | succ k => simp
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, ← hp, ← hq]
    ring
  | mul_X p v hp =>
    obtain ⟨c, s⟩ := v
    set y : MvPolynomial (Fin r × Fin m) R := if b = c then X (a, s) else 0 with hy
    have hX : rowGen R a b (X (c, s) : MvPolynomial (Fin r × Fin m) R) =
        Polynomial.C (X (c, s)) + Polynomial.C y * Polynomial.X := by
      rw [rowGen, aeval_X, hy]
      by_cases h : b = c
      · rw [if_pos h, if_pos h.symm, mul_comm]
      · rw [if_neg h, if_neg (Ne.symm h), map_zero, zero_mul]
    have hx : rowE R r m a b (X (c, s)) = y := rowE_X R r m a b c s
    have hy' : rowE R r m a b y = (if a = b then 1 else 0) * y := by
      rw [hy]
      split_ifs with h1 h2 h2
      · rw [rowE_X, if_pos h2.symm, one_mul]
      · rw [rowE_X, if_neg (Ne.symm h2), zero_mul]
      · simp
      · simp
    have hs : ∀ j, (rowGen R a b (p * X (c, s))).coeff (j + 1) =
        (rowGen R a b p).coeff (j + 1) * X (c, s) + (rowGen R a b p).coeff j * y := by
      intro j
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C,
        Polynomial.coeff_mul_C]
    have h0 : (rowGen R a b (p * X (c, s))).coeff 0 = (rowGen R a b p).coeff 0 * X (c, s) := by
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_C,
        add_zero]
    cases k with
    | zero =>
      rw [hs, h0, rowE_mul, hx, ← hp]
      push_cast
      ring
    | succ k =>
      rw [hs, hs, map_add, rowE_mul, rowE_mul, hx, hy', ← hp, ← hp]
      push_cast
      ring

theorem rowDiv_mem_of_rowE {K : Type} [Field K] [CharZero K] {r m : ℕ} (a b : Fin r)
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K)) (h : ∀ f ∈ M, rowE K r m a b f ∈ M) (k : ℕ)
    {f : MvPolynomial (Fin r × Fin m) K} (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  induction k with
  | zero => rw [(rowE_eq_rowDiv K r m a b f).2]; exact hf
  | succ k ih =>
    have hrec := rowDiv_succ_rec K a b f k
    have h1 : (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) K) * rowDiv K a b k f ∈ M := by
      split_ifs
      · rw [one_mul, ← nsmul_eq_mul]; exact nsmul_mem ih k
      · simp
    have h2 : ((k + 1 : ℕ) : K) • rowDiv K a b (k + 1) f ∈ M := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_succ, eq_sub_of_add_eq hrec]
      exact M.sub_mem (h _ ih) h1
    exact (M.smul_mem_iff (Nat.cast_ne_zero.2 k.succ_ne_zero)).1 h2

theorem dualWeyl_le_of_rowE_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M →
      (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  intro K _ _ n ν hν M h0 hE
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K le_rfl ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact h0
  | cons x w ih => exact rowDiv_mem_of_rowE x.1 x.2.1 M (hE _ _) x.2.2 ih

end GlobalTheory.BrCompare
end

section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_le_of_highest_vector_rowOperator_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M → (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  first | exact @GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable | exact GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable | (intros; apply GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable <;> assumption)
end

section
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

theorem monomial_eq_zmon_mul_emb {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) (μ : Fin (n + 1) × Fin n →₀ ℕ)
    (hμ : ∀ s, μ (Fin.last n, s) = b s) (c : K) :
    ∃ f, (monomial μ c : BP K n) = zmon K n b * emb K n f := by
  refine ⟨C c * ∏ a : Fin n, ∏ s : Fin n, X (a, s) ^ μ (a.castSucc, s), ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_castSucc]
  simp only [hμ, zmon, emb, map_mul, map_prod, map_pow, rename_X, rename_C]
  ring

theorem eq_zmon_mul_emb_of_homogeneous {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) (H : BP K n)
    (hH : IsWeightedHomogeneous (zW n) H (fun s => (b s : ℤ))) : ∃ f, H = zmon K n b * emb K n f := by
  have h : ∀ μ ∈ H.support, ∃ f, (monomial μ (coeff μ H) : BP K n) = zmon K n b * emb K n f := by
    intro μ hμ
    refine monomial_eq_zmon_mul_emb b μ (fun s => ?_) _
    have h1 := congrFun (hH (mem_support_iff.1 hμ)) s
    rw [bm_weight_zW] at h1
    exact_mod_cast h1
  choose! g hg using h
  refine ⟨∑ μ ∈ H.support, g μ, ?_⟩
  rw [map_sum, Finset.mul_sum, ← Finset.sum_congr rfl hg]
  exact H.as_sum

theorem zmon_mul_emb_injective {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) {f g : MvPolynomial (Fin n × Fin n) K}
    (h : zmon K n b * emb K n f = zmon K n b * emb K n g) : f = g := by
  have hz : zmon K n b ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => pow_ne_zero _ (X_ne_zero _)
  refine rename_injective (fun v : Fin n × Fin n => ((v.1.castSucc, v.2) : Fin (n + 1) × Fin n)) ?_
    (mul_left_cancel₀ hz h)
  exact (Fin.castSucc_injective n).prodMap Function.injective_id

theorem zcomp_top_eq_zmon_mul_emb (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℕ) (G : BP K n)
    (hG : G ∈ dualWeyl K (n + 1) n lam) (b : Fin n → ℕ) (hb : ∀ s, b s ≤ lam s)
    (hmax : ∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg fun s => (b s : ℤ)) :
    ∃ f ∈ dualWeyl K n n (fun s => lam s - b s), zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  obtain ⟨f, hf⟩ := eq_zmon_mul_emb_of_homogeneous b _ (bmD_zcomp_isWH (fun s => (b s : ℤ)) G)
  refine ⟨f, bm_mem_dualWeyl_iff.2 ⟨fun s => ?_, fun l j hlj => ?_⟩, hf⟩
  · have h := bmD_weight lam G hG (fun s => (b s : ℤ)) s
    rw [hf, bmE_lead, bm_ndE_self] at h
    apply zmon_mul_emb_injective b
    rw [h, map_smul, mul_smul_comm, Nat.cast_sub (hb s)]
    push_cast
    rfl
  · have h := bmD_raise lam G hG (fun s => (b s : ℤ)) hmax l j hlj
    rw [hf, bmE_lead] at h
    apply zmon_mul_emb_injective b
    rw [h, map_zero, mul_zero]

end GlobalTheory.BrCompare
end

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_top_component_dualWeyl_eq_monomial_mul : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℕ) (G : BP K n), G ∈ dualWeyl K (n + 1) n lam → ∀ b : Fin n → ℕ, (∀ s, b s ≤ lam s) → (∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg fun s => (b s : ℤ)) → ∃ f ∈ dualWeyl K n n (fun s => lam s - b s), zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  atlas_forward_decl GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb
end

section
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare.LiftGen

open GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

theorem telescope {n : ℕ} (f : Fin (n + 1) → ℤ) (t : Fin (n + 1)) :
    ∑ i : Fin n, (if t.val < i.val + 1 then f i.castSucc - f i.succ else 0) = f t - f (Fin.last n) := by
  induction n with
  | zero => simp [Fin.eq_zero t, Fin.last]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    induction t using Fin.lastCases with
    | last =>
      rw [Finset.sum_eq_zero, if_neg (by simp)]
      · simp
      · intro i _
        rw [if_neg]
        have := i.isLt
        simp only [Fin.val_last, Fin.val_castSucc]
        omega
    | cast t =>
      have h := ih (fun j => f j.castSucc) t
      have ht := t.isLt
      simp only [Fin.val_castSucc, Fin.succ_castSucc, Fin.val_last, Fin.succ_last] at h ⊢
      rw [h, if_pos (by omega)]
      simp

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

theorem aNum_cast (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (i : Fin n) :
    (aNum lam sg i : ℤ) = sg.w i - lam.w i.succ :=
  Int.toNat_of_nonneg (sub_nonneg.2 (h i).1)

theorem bNum_cast (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (i : Fin n) :
    (bNum lam sg i : ℤ) = lam.w i.castSucc - sg.w i :=
  Int.toNat_of_nonneg (sub_nonneg.2 (h i).2)

theorem sum_ab (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (t : Fin n) :
    ((∑ i : Fin n, (aNum lam sg i * initW n (i.val + 1) t) + ∑ i : Fin n, (bNum lam sg i * initW n (i.val + 1) t) : ℕ) : ℤ)
      = lam.w t.castSucc - lam.w (Fin.last n) := by
  rw [← telescope lam.w t.castSucc, ← Finset.sum_add_distrib, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ha := aNum_cast h i
  have hb := bNum_cast h i
  simp only [initW, Fin.val_castSucc]
  split_ifs
  · push_cast; linarith
  · simp

theorem sum_b_succ (b : Fin n → ℕ) (t : Fin n) :
    ∑ i : Fin n, b i * initW n (i.val + 1) t = ∑ i : Fin n, b i * initW n i.val t + b t := by
  have : b t = ∑ i : Fin n, if i = t then b i else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [initW, Fin.ext_iff]
  split_ifs <;> omega

theorem lamN_eq (t : Fin n) : lamN lam t = (lam.w t.castSucc - lam.w (Fin.last n)).toNat := by
  simp only [lamN, DomWeight.natW, DomWeight.detShift, Nat.succ_pos, dif_pos]
  rfl

theorem natW_eq (he : EqualLast lam sg) (t : Fin n) : sg.natW t = (sg.w t - lam.w (Fin.last n)).toNat := by
  have hn : 0 < n := t.pos
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn]
  rw [he ⟨n - 1, by omega⟩ (by simp only; omega)]

theorem shape_lam (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), initW n (i.val + 1)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), initW n (i.val + 1)) = lamN lam := by
  funext t
  have := sum_ab h t
  rw [lamN_eq, ← this, Int.toNat_natCast]
  simp [Finset.sum_apply]

theorem shape_sg (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), initW n (i.val + 1)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), initW n i.val) = sg.natW := by
  funext t
  have h1 := sum_ab h t
  rw [sum_b_succ (bNum lam sg)] at h1
  have hb := bNum_cast h t
  rw [natW_eq he]
  simp only [Pi.add_apply, Finset.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Pi.smul_apply]
  omega

theorem shape_b (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), (0 : Fin n → ℕ)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), (Pi.single i 1 : Fin n → ℕ)) = fun s => lamN lam s - sg.natW s := by
  funext t
  have h1 := sum_ab h t
  rw [sum_b_succ (bNum lam sg)] at h1
  have hb := bNum_cast h t
  have h2 : ((∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), (0 : Fin n → ℕ)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), (Pi.single i 1 : Fin n → ℕ))) t = bNum lam sg t := by
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h2, natW_eq he, lamN_eq]
  omega

theorem prod_mem (K : Type) [Field K] {r n : ℕ} {ι : Type} (S : Finset ι) (w : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) K) (hg : ∀ k, g k ∈ dualWeyl K r n (w k)) :
    ∏ k ∈ S, g k ∈ dualWeyl K r n (∑ k ∈ S, w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (dualWeylMul K r n 0 0 0 0).2
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (dualWeylMul K r n _ _ _ _).1 (hg a) ih

theorem incl_initMinor (K : Type) [Field K] {s : ℕ} (I : Fin s → Fin (n + 1)) (hs : s ≤ n) (hs' : s ≤ n + 1) :
    incl K n (initMinor K I hs) = initMinor K I hs' := by
  unfold initMinor
  rw [algHom_det_of]
  simp only [incl, rename_X]
  rfl

theorem piGen_mem_and_lift (K : Type) [Field K] (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) (t : Gen lam sg) :
    piGen K lam sg t ∈ dualWeyl K n n sg.natW ∧
      ∃ G : BP K n, bmLift K n (lamN lam) (fun s => lamN lam s - sg.natW s) (piGen K lam sg t) G ∧
        phiGen K lam sg t = incl K n G := by
  refine ⟨?_, ?_⟩
  · rw [← shape_sg h he]
    exact (dualWeylMul K n n _ _ _ _).1
      (prod_mem K _ _ _ fun i => prod_mem K _ _ _ fun k => initMinor_mem _ _)
      (prod_mem K _ _ _ fun i => prod_mem K _ _ _ fun k => initMinor_mem _ _)
  · have h0 := bmG_prod (Finset.univ : Finset (Fin n)) _ _ _ _ fun i _ =>
      bmG_prod (Finset.univ : Finset (Fin (aNum lam sg i))) _ _ _ _ fun k _ =>
        bmLift_minor0 K n (t.1 i k) (Nat.succ_le_of_lt i.isLt)
    have h1 := bmG_prod (Finset.univ : Finset (Fin n)) _ _ _ _ fun i _ =>
      bmG_prod (Finset.univ : Finset (Fin (bNum lam sg i))) _ _ _ _ fun k _ =>
        bmLift_minor1 K n (t.2 i k) (Nat.succ_le_of_lt i.isLt)
    refine ⟨_, bmG_cast (bmLift_mul h0 h1) (shape_lam h) (shape_b h he) rfl rfl, ?_⟩
    unfold phiGen
    simp only [map_mul, map_prod]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
      exact (incl_initMinor K _ _ _).symm
    · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
      rw [incl_initMinor K _ _ (Nat.succ_le_succ i.isLt.le)]
      refine congrArg (fun I => initMinor K I (Nat.succ_le_succ i.isLt.le)) ?_
      funext p
      induction p using Fin.lastCases with
      | last => simp
      | cast p => simp

end GlobalTheory.BrCompare.LiftGen
end

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generators_in_dual_weyl_module : ∀ (K : Type) [Field K] (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Gen lam sg, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.piGen K lam sg t ∈ dualWeyl K n n sg.natW ∧ ∃ G : BP K n, bmLift K n (lamN lam) (fun s => lamN lam s - sg.natW s) (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.piGen K lam sg t) G ∧ GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.phiGen K lam sg t = incl K n G := by
  atlas_forward_decl GlobalTheory.BrCompare.LiftGen.piGen_mem_and_lift
end

section
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCompare.Surj

open GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

variable {K : Type} [Field K]

theorem rowAct_initMinor_mem {r m s : ℕ} (g : Matrix (Fin r) (Fin r) K) (I : Fin s → Fin r) (hs : s ≤ m) :
    rowAct K g (initMinor K I hs) ∈ Submodule.span K (Set.range fun J : Fin s → Fin r => initMinor K J hs) := by
  classical
  have h1 : rowAct K g (initMinor K I hs) =
      (Matrix.detRowAlternating (n := Fin s) (R := MvPolynomial (Fin r × Fin m) K)).toMultilinearMap
        (fun p => ∑ b : Fin r, (C (g (I p) b) : MvPolynomial (Fin r × Fin m) K) •
          fun q : Fin s => (X (b, Fin.castLE hs q) : MvPolynomial (Fin r × Fin m) K)) := by
    unfold initMinor
    rw [AlgHom.map_det]
    change Matrix.det _ = Matrix.det _
    congr 1
    ext p q : 2
    simp [rowAct, Finset.sum_apply]
  rw [h1, MultilinearMap.map_sum]
  refine Submodule.sum_mem _ fun J _ => ?_
  rw [MultilinearMap.map_smul_univ, ← map_prod, smul_eq_mul, ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, rfl⟩)

theorem prod_mem_span_range {A ι : Type} [CommRing A] [Algebra K A] [Fintype ι] {J : ι → Type}
    (f : ∀ i, J i → A) (x : ι → A) (hx : ∀ i, x i ∈ Submodule.span K (Set.range (f i))) :
    ∏ i, x i ∈ Submodule.span K (Set.range fun t : ∀ i, J i => ∏ i, f i (t i)) := by
  classical
  refine Submodule.span_mono ?_ (GlobalTheory.OrbitSpan.prod_mem_span_prod Finset.univ _ x hx)
  intro y hy
  rw [Set.mem_fintype_prod] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  choose t ht using hz
  exact ⟨t, Finset.prod_congr rfl fun i _ => ht i⟩

theorem rowAct_piGen_mem {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) (g : Matrix (Fin n) (Fin n) K)
    (t : Gen lam sg) : rowAct K g (piGen K lam sg t) ∈ Submodule.span K (Set.range (piGen K lam sg)) := by
  unfold piGen
  simp only [map_mul, map_prod]
  have h1 := prod_mem_span_range (K := K) _ _ fun i : Fin n => prod_mem_span_range _ _
    fun k : Fin (aNum lam sg i) => rowAct_initMinor_mem g (t.1 i k) (Nat.succ_le_of_lt i.isLt)
  have h2 := prod_mem_span_range (K := K) _ _ fun i : Fin n => prod_mem_span_range _ _
    fun k : Fin (bNum lam sg i) => rowAct_initMinor_mem g (t.2 i k) i.isLt.le
  have h3 := Submodule.mul_mem_mul h1 h2
  rw [Submodule.span_mul_span] at h3
  refine Submodule.span_mono ?_ h3
  rintro _ ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, rfl⟩
  exact ⟨(u, v), rfl⟩

theorem prod_shift {A : Type} [CommMonoid A] {n : ℕ} (D : ℕ → A) (h0 : D 0 = 1) (b : Fin n → ℕ) :
    ∏ i : Fin n, D i.val ^ b i = ∏ i : Fin n, D (i.val + 1) ^ nuNext b i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
    have h1 : nuNext b (Fin.last m) = 0 := by simp [nuNext]
    rw [h1, pow_zero, mul_one, Fin.val_zero, h0, one_pow, one_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h2 : nuNext b i.castSucc = b i.succ := by
      unfold nuNext
      rw [dif_pos (by simp)]
      rfl
    rw [h2]
    rfl

theorem aNum_add_bNext {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n} (h : Interlace lam sg)
    (he : EqualLast lam sg) (i : Fin n) :
    aNum lam sg i + nuNext (bNum lam sg) i = sg.natW i - nuNext sg.natW i := by
  have hn : 0 < n := Fin.pos i
  unfold nuNext
  simp only [aNum, bNum, DomWeight.natW, DomWeight.detShift, dif_pos hn]
  have h1 := (h i).1
  split_ifs with hi
  · have h2 := (h ⟨i.val + 1, hi⟩).2
    have h3 : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := rfl
    have h4 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w ⟨i.val + 1, hi⟩ := sg.anti (by simp [Fin.le_def]; omega)
    rw [h3] at h2 ⊢
    omega
  · have h2 := he i (by omega)
    have h3 : i.succ = Fin.last n := Fin.ext (by simp; omega)
    have h4 : (⟨n - 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
    rw [h3, h4]
    omega

theorem hw_eq_piGen {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n} (h : Interlace lam sg)
    (he : EqualLast lam sg) :
    hw K le_rfl sg.natW = piGen K lam sg
      (fun i _ => Fin.castLE (Nat.succ_le_of_lt i.isLt), fun i _ => Fin.castLE i.isLt.le) := by
  let D : ℕ → MvPolynomial (Fin n × Fin n) K := fun k => if hk : k ≤ n then lpMinor K k hk hk else 1
  have hD : ∀ k (hk : k ≤ n), initMinor K (Fin.castLE hk) hk = D k := fun k hk => by
    simp only [D, dif_pos hk]; rfl
  have hD' : ∀ k (hk : k ≤ n), lpMinor K k hk hk = D k := hD
  have h0 : D 0 = 1 := by
    rw [← hD' 0 (Nat.zero_le _)]; simp [lpMinor]
  unfold piGen hw
  simp only [hD, hD', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [prod_shift D h0, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add, aNum_add_bNext h he]

theorem dualWeyl_le_span_piGen (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight (n + 1))
    (sg : DomWeight n) (h : Interlace lam sg) (he : EqualLast lam sg) :
    dualWeyl K n n sg.natW ≤ Submodule.span K (Set.range (piGen K lam sg)) := by
  refine (GlobalTheory.OrbitSpan.dualWeyl_le_span_orbit K le_rfl sg.natW (Formalism.L2.Col.natW_anti sg)).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  beta_reduce
  rw [hw_eq_piGen h he]
  exact rowAct_piGen_mem lam sg _ _

end GlobalTheory.BrCompare.Surj
end
end

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weyl_spanned_by_interlacing : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → dualWeyl K n n sg.natW ≤ Submodule.span K (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.piGen K lam sg)) := by
  atlas_forward_decl GlobalTheory.BrCompare.Surj.dualWeyl_le_span_piGen
end

section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

open GlobalTheory.Branching.AddColumn in

theorem exists_eq_incl_of_last_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → ∀ x ∈ dualWeyl K (n + 1) (n + 1) ν, ∃ x' ∈ dualWeyl K (n + 1) n (fun i => ν i.castSucc), x = incl K n x' := by
  intro K _ _ n ν hν x hx
  have hinj : Function.Injective
      (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1)) :=
    Function.injective_id.prodMap (Fin.castSucc_injective n)
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hx ⊢
  obtain ⟨x', rfl⟩ := exists_rename_eq_of_vars_subset_range x _ hinj (by
    rintro ⟨a, s⟩ hv
    induction s using Fin.lastCases with
    | cast s => exact ⟨(a, s), rfl⟩
    | last =>
      exfalso
      obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support _).1 (Finset.mem_coe.1 hv)
      have h := congrFun (hx.1 (mem_support_iff.1 hd)) (Fin.last n)
      rw [hν, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff] at h
      have h2 := h _ hvd
      simp [colW] at h2
      exact Finsupp.mem_support_iff.1 hvd h2)
  refine ⟨x', ⟨fun u hu => ?_, fun l j hlj => ?_⟩, rfl⟩
  · rw [← coeff_rename_mapDomain _ hinj] at hu
    funext i
    rw [← (weight_mapDomain (n + 1) n u).1, hx.1 hu]
  · have h := hx.2 l.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.2 hlj)
    rw [colAddGen_rename_castSucc] at h
    apply rename_injective _ (Option.map_injective hinj)
    rw [h, rename_rename, rename_rename]
    rfl

end GlobalTheory.BrCompare
end

section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weyl_last_zero_inclusion : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → ∀ x ∈ dualWeyl K (n + 1) (n + 1) ν, ∃ x' ∈ dualWeyl K (n + 1) n (fun i => ν i.castSucc), x = incl K n x' := by
  first | exact @GlobalTheory.BrCompare.exists_eq_incl_of_last_eq_zero | exact GlobalTheory.BrCompare.exists_eq_incl_of_last_eq_zero | (intros; apply GlobalTheory.BrCompare.exists_eq_incl_of_last_eq_zero <;> assumption)
end

section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCoefFock

variable {K : Type} [Field K] {n : ℕ}

def spl (K : Type) [Field K] (n : ℕ) : BP K n →+* MvPolynomial (Unit × Fin n) (MvPolynomial (Fin n × Fin n) K) :=
  (map (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n) :
      MvPolynomial (Unit × Fin n × Fin n) K →ₐ[K] MvPolynomial (Fin n × Fin n) K).toRingHom).comp
    ((GlobalTheory.BranchFormula.splitLast K Unit (rfl : n + 1 = n + 1)).toRingHom.comp
      ((rename (fun v : Fin (n + 1) × Fin (n + 1) => (((), v) : Unit × Fin (n + 1) × Fin (n + 1))) :
        _ →ₐ[K] _).toRingHom.comp (incl K n).toRingHom))

theorem coefOne_eq (b : Fin n → ℕ) (x : BP K n) :
    coefOne K n b (incl K n x) = coeff (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) (spl K n x) := by
  unfold coefOne
  rw [GlobalTheory.BranchFormula.coefLast_eq_coeff]
  simp [spl, coeff_map]

theorem spl_C (a : K) : spl K n (C a) = C (C a) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_up (a s : Fin n) : spl K n (X (a.castSucc, s)) = C (X (a, s)) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_last (s : Fin n) : spl K n (X (Fin.last n, s)) = X ((), s) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

def lastV (n : ℕ) (p : Unit × Fin n) : Fin (n + 1) × Fin n := (Fin.last n, p.2)

theorem lastV_inj : Function.Injective (lastV n) := fun _ _ h =>
  Prod.ext rfl (Prod.ext_iff.1 h).2

theorem pderiv_rename_of_ne {σ τ : Type} (e : σ → τ) (v : τ) (h : ∀ u, e u ≠ v) (f : MvPolynomial σ K) :
    pderiv v (rename e f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p u hp => simp [hp, pderiv_X_of_ne (h u)]

theorem fockB_C_left {σ : Type} (a : K) (g : MvPolynomial σ K) : fockB (C a) g = a * constantCoeff g :=
  @fockL_C_left K _ starRingOfComm _ a g

theorem emb_inj : Function.Injective (fun v : Fin n × Fin n => ((v.1.castSucc, v.2) : Fin (n + 1) × Fin n)) :=
  (Fin.castSucc_injective n).prodMap Function.injective_id

theorem key (x : BP K n) (β : Unit × Fin n →₀ ℕ) (p : MvPolynomial (Fin n × Fin n) K) :
    fockB x (rename (lastV n) (monomial β (1 : K)) * emb K n p) =
      ((∏ u, (β u).factorial : ℕ) : K) * fockB (coeff β (spl K n x)) p := by
  classical
  induction x using MvPolynomial.induction_on generalizing β p with
  | C a =>
    rw [fockB_C_left, spl_C, coeff_C, map_mul, constantCoeff_rename, constantCoeff_monomial, emb, constantCoeff_rename]
    by_cases h : β = 0
    · subst h; simp [fockB_C_left]
    · rw [if_neg h, if_neg (Ne.symm h), ← fockBL_apply]; simp
  | add f g hf hg =>
    simp only [← fockBL_apply, map_add, LinearMap.add_apply, coeff_add] at *
    rw [hf, hg, mul_add]
  | mul_X f v hf =>
    obtain ⟨a, s⟩ := v
    rw [mul_comm f, fockB_X_mul, map_mul (spl K n), Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | cast a =>
      rw [pderiv_rename_of_ne (lastV n) (a.castSucc, s) (fun u h => (Fin.castSucc_lt_last a).ne' (Prod.ext_iff.1 h).1),
        mul_zero, add_zero, spl_up, coeff_C_mul, fockB_X_mul, ← hf]
      congr 2
      exact pderiv_rename emb_inj (a, s) p
    | last =>
      have h1 : pderiv (Fin.last n, s) (emb K n p) = 0 :=
        pderiv_rename_of_ne _ _ (fun u h => (Fin.castSucc_lt_last u.1).ne (congrArg Prod.fst h)) p
      have h2 : pderiv (Fin.last n, s) (rename (lastV n) (monomial β (1 : K))) =
          (β ((), s) : K) • rename (lastV n) (monomial (β - Finsupp.single ((), s) 1) (1 : K)) := by
        have := pderiv_rename (R := K) lastV_inj ((), s) (monomial β (1 : K))
        rw [pderiv_monomial] at this
        rw [← map_smul, smul_monomial, smul_eq_mul, mul_comm]
        exact this
      rw [h1, mul_zero, zero_add, h2, mul_comm, smul_mul_assoc, ← fockBL_apply, map_smul, fockBL_apply, hf,
        spl_last, coeff_X_mul', smul_eq_mul]
      split_ifs with h
      · rw [← mul_assoc, ← Nat.cast_mul]
        congr 2
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ((), s)),
          ← Finset.mul_prod_erase _ (fun u => (β u).factorial) (Finset.mem_univ ((), s)), ← mul_assoc]
        congr 1
        · simpa using Nat.mul_factorial_pred (Finsupp.mem_support_iff.1 h)
        · refine Finset.prod_congr rfl fun u hu => ?_
          simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hu)]
      · rw [Finsupp.notMem_support_iff.1 h, ← fockBL_apply (0 : MvPolynomial (Fin n × Fin n) K)]
        simp

theorem zmon_eq (b : Fin n → ℕ) :
    zmon K n b = rename (lastV n) (monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) (1 : K)) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, Fintype.prod_prod_type]
  simp [zmon, lastV]

theorem spl_zmon (b : Fin n → ℕ) :
    spl K n (zmon K n b) = monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  simp [zmon, spl_last]

theorem spl_emb (q : MvPolynomial (Fin n × Fin n) K) : spl K n (emb K n q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [emb, rename_C, spl_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => rw [map_mul, map_mul, hp, bmF_emb_X, spl_up, map_mul]

theorem fockB_zmon_emb : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  intro K _ n b
  have h1 : ∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) =
      (bfact b : K) * fockB (coefOne K n b (incl K n x)) p := by
    intro x p
    rw [zmon_eq, key, coefOne_eq, Fintype.prod_prod_type]
    simp [bfact]
  refine ⟨h1, fun p q => ?_⟩
  rw [h1, coefOne_eq, map_mul, spl_zmon, spl_emb, mul_comm (monomial _ _), coeff_C_mul]
  simp

end GlobalTheory.BrCoefFock
end
end

section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPairing_lastRow_monomial_reads_coefficient : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  first | exact @GlobalTheory.BrCoefFock.fockB_zmon_emb | exact GlobalTheory.BrCoefFock.fockB_zmon_emb | (intros; apply GlobalTheory.BrCoefFock.fockB_zmon_emb <;> assumption)
end

section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branching_list_character_product : ∀ (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) ∧ (∀ u ∈ bmList (lamN lam) sg.natW, u ∈ zList lam sg) ∧ ((zList lam sg).map (bmChi (lamN lam) fun s => ((lamN lam s - sg.natW s : ℕ) : ℤ))).prod = Formalism.L2.Col.Br.cBr rfl lam sg ∧ (∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s) ∧ ∀ (K : Type) [Field K], Formalism.L2.Col.Br.xiBr K rfl lam sg = incl K n (xiB K (lamN lam) sg.natW) := by
  first | exact @GlobalTheory.BrCompare.shifted_branching_list_character | exact GlobalTheory.BrCompare.shifted_branching_list_character | (intros; apply GlobalTheory.BrCompare.shifted_branching_list_character <;> assumption)
end

section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCompare

section Core

variable {K : Type} [Field K] [CharZero K] {n : ℕ}

theorem hw_raise (ν : Fin n → ℕ) (l j : Fin n) (h : l < j) : rowE K n n l j (hw K le_rfl ν) = 0 := by
  rw [(rowE_eq_rowDiv K n n l j _).1]
  exact hwRaise K n n le_rfl ν l j 1 h le_rfl

theorem hw_weight {ν : Fin n → ℕ} (hν : Antitone ν) (s : Fin n) :
    rowE K n n s s (hw K le_rfl ν) = (ν s : K) • hw K le_rfl ν := by
  have h := (rowWeight_iff _ _).1 (hwRowWeight K n n le_rfl ν hν) s
  simpa [rowNu] using h

theorem capDet_dualWeyl {μ : Fin n → ℕ} (hμ : Antitone μ) (u : ℤ) {f : MvPolynomial (Fin n × Fin n) K}
    (hf : f ∈ dualWeyl K n n μ) :
    capDet (fun i j => rowE K n n i j) u f = ((∏ j : Fin n, (u + ((j : ℕ) : ℤ) - (μ j : ℤ)) : ℤ) : K) • f := by
  have h := GlobalTheory.T.dualWeyl_le_of_highest_vector_rowOperator_stable K n μ hμ (Module.End.eigenspace (capDet (fun i j => rowE K n n i j) u)
    ((∏ j : Fin n, (u + ((j : ℕ) : ℤ) - (μ j : ℤ)) : ℤ) : K)) ?_ ?_ hf
  · exact Module.End.mem_eigenspace_iff.1 h
  · exact Module.End.mem_eigenspace_iff.2 (capDet_eigen _ u _ (fun j => (μ j : ℤ)) (hw_raise μ)
      (fun s => by simpa using hw_weight hμ s))
  · intro a b g hg
    rw [Module.End.mem_eigenspace_iff] at hg ⊢
    have hc := capDet_central (fun i j => rowE K n n i j) u (fun i j k l => by
      simpa only [eq_comm (a := l)] using glRel_rowE K n n i j k l) end_two a b
    rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hg, map_smul]

theorem branchingAdmissible_facts {lam : Fin n → ℕ} {d : ℕ} {β : Fin n → ℤ} (h : bmAdm lam d β) :
    ∃ b : Fin n → ℕ, β = (fun s => (b s : ℤ)) ∧ (∀ s, b s ≤ lam s) ∧ Antitone fun s => lam s - b s := by
  lift β to Fin n → ℕ using h.1 with b
  have h2 := h.2.2
  have hb : ∀ s, b s ≤ lam s := fun s => by
    have h3 := (h2 s).2
    rw [bmH_lamZ_succ] at h3
    simp only [Function.comp] at h3
    omega
  refine ⟨b, rfl, hb, bmK_antitone lam (fun s => lam s - b s) (bm_IL_of lam _ ?_)⟩
  simpa only [Nat.cast_sub (hb _)] using h2

theorem rCap_top {lam : Fin n → ℕ} {d : ℕ} (G : BP K n) (hG : G ∈ bmW K n lam d) (β : Fin n → ℤ)
    (hβ : zcomp K n β G ≠ 0) (hmax : ∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg β) :
    bmAdm lam d β ∧ ∀ u, rCap K n n u (zcomp K n β G) = ((bmChi lam β u : ℤ) : K) • zcomp K n β G := by
  have hA := (bm_eig lam d G (bmK_mem_alt.1 hG).1 (bmK_mem_alt.1 hG).2 β hβ hmax).1
  refine ⟨hA, fun u => ?_⟩
  obtain ⟨b, rfl, hb, ha⟩ := branchingAdmissible_facts hA
  obtain ⟨f, hf, e⟩ := GlobalTheory.T.lastRow_top_component_dualWeyl_eq_monomial_mul K n lam G (bmK_mem_alt.1 hG).1 b hb hmax
  rw [e, rCap_lead, capDet_dualWeyl ha u hf, map_smul, mul_smul_comm, bmChi]
  simp only [Nat.cast_sub (hb _)]

theorem rCap_kill {lam sg : Fin n → ℕ} (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (ℓ : List ℤ)
    (hℓ : ∀ u ∈ bmList lam sg, u ∈ ℓ) (G : BP K n) (hG : G ∈ bmW K n lam (∑ s, (lam s - sg s)))
    (h0 : zcomp K n (fun s => ((lam s - sg s : ℕ) : ℤ)) G = 0) : (ℓ.map (rCap K n n)).prod G = 0 :=
  bm_kill (zW n) omg (rCap K n n) (bmW K n lam (∑ s, (lam s - sg s))) (bmChi lam)
    (bmAdm lam (∑ s, (lam s - sg s))) (rCap_comm n n) (fun u β => zcomp_comm_rCap n β u) (fun u _ h => capelliDeterminantFirstRows_mem_bmW u h)
    (fun G hG β h1 h2 => rCap_top G hG β h1 h2) (bm_sep lam _) ℓ _
    (fun β h1 h2 => by
      obtain ⟨u, hu, e⟩ := bm_list_kills lam sg hI β h1 h2
      exact ⟨u, hℓ u hu, e⟩) G hG h0

theorem dual_tri {M : Type} [AddCommGroup M] [Module K M] (ψ : M →ₗ[K] K) : ∀ {m : ℕ} (g : Fin m → Module.End K M)
    (c : Fin m → K) (F : Fin m → Prop), (∀ k, F k → ∀ x, ψ (g k x) = c k * ψ x) →
    (∀ k, ¬ F k → (∀ j, j < k → F j) → ∀ x, ψ (g k x) = 0) → ∀ x,
    ((∀ k, F k) → ψ ((List.ofFn g).prod x) = (∏ k, c k) * ψ x) ∧ ((¬ ∀ k, F k) → ψ ((List.ofFn g).prod x) = 0)
  | 0, g, c, F, _, _, x => ⟨fun _ => by simp, fun h => absurd (fun k : Fin 0 => k.elim0) h⟩
  | m + 1, g, c, F, h1, h2, x => by
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, Fin.prod_univ_succ]
    by_cases h0 : F 0
    · obtain ⟨ih1, ih2⟩ := dual_tri ψ (fun i : Fin m => g i.succ) (fun i => c i.succ) (fun i => F i.succ)
        (fun k hk => h1 _ hk) (fun k hk hj => h2 _ hk (fun j hkj => by
          induction j using Fin.cases with
          | zero => exact h0
          | succ j => exact hj j (Fin.succ_lt_succ_iff.1 hkj))) x
      rw [h1 0 h0]
      refine ⟨fun h => by rw [ih1 fun k => h _, mul_assoc], fun h => ?_⟩
      rw [ih2 fun h' => h fun k => Fin.cases h0 h' k, mul_zero]
    · exact ⟨fun h => absurd (h 0) h0, fun _ => h2 0 h0 (fun j hj => absurd hj (Fin.not_lt_zero j)) _⟩

theorem capDet_dual {M : Type} [AddCommGroup M] [Module K M] (E : Fin n → Fin n → Module.End K M) (u : ℤ)
    (ψ : M →ₗ[K] K) (μ : Fin n → ℤ) (hr : ∀ l j, l < j → ∀ x, ψ (E j l x) = 0)
    (hw : ∀ s x, ψ (E s s x) = ((μ s : ℤ) : K) * ψ x) (x : M) :
    ψ (capDet E u x) = ((∏ j : Fin n, (u + ((j : ℕ) : ℤ) - μ j) : ℤ) : K) * ψ x := by
  have key := fun α : Equiv.Perm (Fin n) => dual_tri ψ (fun k => bmF E u k (α k) k)
    (fun j => ((u + ((j : ℕ) : ℤ) - μ j : ℤ) : K)) (fun k => α k = k)
    (fun k hk x => by
      simp only [bmF, hk, if_true, LinearMap.sub_apply, Module.End.intCast_apply, map_sub, map_zsmul, hw, zsmul_eq_mul]
      push_cast; ring)
    (fun k hk hj x => by
      have hlt : k < α k := by
        rcases lt_trichotomy k (α k) with h | h | h
        · exact h
        · exact absurd h.symm hk
        · exact absurd (α.injective (hj _ h)) hk
      simp [bmF, hk, hr k _ hlt]) x
  simp only [capDet, bmPi, bmM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, id]
  rw [Finset.sum_eq_single 1]
  · rw [(key 1).1 fun _ => rfl]; simp
  · intro α _ hα
    rw [(key α).2 fun h => hα (Equiv.ext h), smul_zero]
  · simp

theorem rowGen_initMinor {r m s : ℕ} (a b : Fin r) (I : Fin s → Fin r) (hs : s ≤ m) (hI : Function.Injective I)
    (h : ∀ p, I p = b → ∃ p', p ≠ p' ∧ I p' = a) :
    rowGen K a b (initMinor K I hs) = Polynomial.C (initMinor K I hs) := by
  unfold initMinor
  rw [AlgHom.map_det, RingHom.map_det]
  by_cases hb : ∃ p, I p = b
  · obtain ⟨i, hi⟩ := hb
    obtain ⟨j, hij, hj⟩ := h i hi
    rw [← Matrix.det_updateRow_add_smul_self (Polynomial.C.mapMatrix _) hij Polynomial.X]
    congr 1
    ext1 p q
    by_cases hp : p = i
    · subst hp
      simp [rowGen_X, hi, hj]
    · have e1 : I p ≠ b := fun h' => hp (hI (h'.trans hi.symm))
      simp [Matrix.updateRow_apply, rowGen_X, hp, e1]
  · congr 1
    ext1 p q
    have e1 : I p ≠ b := fun h' => hb ⟨p, h'⟩
    simp [rowGen_X, e1]

theorem xi_raise (lam sg : Fin n → ℕ) (l j : Fin n) (h : l < j) : rE K n n l j (xiB K lam sg) = 0 := by
  have h' : l.val < j.val := h
  have key : rowGen K l.castSucc j.castSucc (xiB K lam sg) = Polynomial.C (xiB K lam sg) := by
    unfold xiB
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, rowGen_initMinor, rowGen_initMinor]
    · intro p q e
      have := p.2; have := q.2; have := i.2
      simp only [rowsB, Fin.ext_iff] at e ⊢
      split_ifs at e <;> simp at e <;> omega
    · intro p e
      have := p.2; have := i.2; have := j.2
      have hp : p.val = j.val ∧ p.val < i.val := by
        simp only [rowsB, Fin.ext_iff] at e
        split_ifs at e <;> simp at e <;> omega
      refine ⟨⟨l.val, by omega⟩, fun e' => ?_, ?_⟩
      · have := congrArg Fin.val e'
        simp at this; omega
      · simp only [rowsB]
        rw [if_pos (by omega)]; rfl
    · intro p q e
      simpa [rowsA, Fin.ext_iff] using e
    · intro p e
      have := p.2
      have hp : p.val = j.val := by simpa [rowsA, Fin.ext_iff] using e
      refine ⟨⟨l.val, by omega⟩, fun e' => ?_, rfl⟩
      have := congrArg Fin.val e'
      simp at this; omega
  rw [rE, (rowE_eq_rowDiv K _ _ _ _ _).1, rowDiv, key, Polynomial.coeff_C, if_neg one_ne_zero]

theorem zcomp_lift {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) K} {G : BP K n} (h : bmLift K n lam b f G) :
    zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  have h1 := (bm_isLow_iff _ _).1 h.2.2 _ le_rfl
  rw [map_sub, sub_eq_zero] at h1
  rw [h1]
  exact (bmF_lead_WH K n b f).weightedHomogeneousComponent_same

theorem coeff_zcomp (β : Fin n → ℤ) (G : BP K n) (μ : Fin (n + 1) × Fin n →₀ ℕ) :
    coeff μ (zcomp K n β G) = if Finsupp.weight (zW n) μ = β then coeff μ G else 0 := by
  classical
  unfold zcomp
  rw [coeff_weightedHomogeneousComponent]

theorem fockB_zcomp (β : Fin n → ℤ) (G A : BP K n) (hA : IsWeightedHomogeneous (zW n) A β) :
    fockB G A = fockB (zcomp K n β G) A := by
  rw [← sub_eq_zero, ← fockBL_apply, ← fockBL_apply, ← LinearMap.sub_apply, ← map_sub]
  refine fockB_eq_zero _ _ fun μ hμ => ?_
  by_contra h0
  rw [coeff_sub, coeff_zcomp, if_pos (hA h0), sub_self] at hμ
  exact hμ rfl

theorem lead_inj (b : Fin n → ℕ) {f g : MvPolynomial (Fin n × Fin n) K}
    (h : zmon K n b * emb K n f = zmon K n b * emb K n g) : f = g := by
  have h0 : zmon K n b ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => pow_ne_zero _ (X_ne_zero _)
  exact rename_injective _ (fun v w e => Prod.ext (Fin.castSucc_injective n (Prod.mk.inj e).1) (Prod.mk.inj e).2)
    (mul_left_cancel₀ h0 h)

theorem chi_eq {lam sg : Fin n → ℕ} (hIL : bmIL lam sg) (u : ℤ) :
    bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ)) u = ∏ j : Fin n, (u + ((j : ℕ) : ℤ) - (sg j : ℤ)) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  beta_reduce
  rw [Nat.cast_sub (hIL j).1]
  ring

theorem list_dual {M : Type} [AddCommGroup M] [Module K M] (C : ℤ → Module.End K M) (χ : ℤ → ℤ) (ψ : M →ₗ[K] K)
    (h : ∀ u x, ψ (C u x) = (χ u : K) * ψ x) (ℓ : List ℤ) (x : M) :
    ψ ((ℓ.map C).prod x) = (((ℓ.map χ).prod : ℤ) : K) * ψ x := by
  induction ℓ with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, h, ih, Int.cast_mul, mul_assoc]

theorem psi_eq_zero {lam sg : Fin n → ℕ} (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (ψ : BP K n →ₗ[K] K)
    (hr : ∀ l j, l < j → ∀ x, ψ (rE K n n j l x) = 0)
    (hwt : ∀ a x, ψ (rowE K (n + 1) n a a x) = (bmRho lam sg a : K) * ψ x) (hxi : ψ (xiB K lam sg) = 0)
    (x : BP K n) (hx : x ∈ dualWeyl K (n + 1) n lam) : ψ x = 0 := by
  classical
  have hIL := bm_IL_of lam sg hI
  have hρ : ∀ s : Fin n, bmRho lam sg s.castSucc = sg s := fun s => by simp [bmRho]
  have hC : ∀ u x, ψ (rCap K n n u x) = ((bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ)) u : ℤ) : K) * ψ x := fun u x => by
    rw [chi_eq hIL]
    exact capDet_dual _ u ψ (fun s => (sg s : ℤ)) hr (fun s x => by rw [rE, hwt, hρ]; simp) x
  have hAdm : bmAdm lam (∑ s, (lam s - sg s)) fun s => ((lam s - sg s : ℕ) : ℤ) := by
    refine ⟨fun s => Int.natCast_nonneg _, by simp, ?_⟩
    simpa only [Nat.cast_sub (hIL _).1, sub_sub_cancel] using hI
  have key : ∀ (k : ℕ) (y : BP K n), y ∈ bmW K n lam (∑ s, (lam s - sg s)) →
      (∀ s, rE K n n s s y = (sg s : K) • y) → ∀ S : Finset (Fin n → ℤ), S.card ≤ k →
      (∀ β, zcomp K n β y ≠ 0 → β ∈ S) → ψ y = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro y hy hs S hS hsub
    by_cases h0 : y = 0
    · rw [h0, map_zero]
    obtain ⟨μ, hμ⟩ := ne_zero_iff.1 h0
    have hne : (S.filter fun β => zcomp K n β y ≠ 0).Nonempty := by
      have : zcomp K n (Finsupp.weight (zW n) μ) y ≠ 0 := ne_zero_iff.2 ⟨μ, by rw [coeff_zcomp, if_pos rfl]; exact hμ⟩
      exact ⟨_, Finset.mem_filter.2 ⟨hsub _ this, this⟩⟩
    obtain ⟨β, hβ, hmax⟩ := Finset.exists_max_image _ omg hne
    obtain ⟨hβS, hβ⟩ := Finset.mem_filter.1 hβ
    have hmax' : ∀ β', zcomp K n β' y ≠ 0 → omg β' ≤ omg β := fun β' h => hmax β' (Finset.mem_filter.2 ⟨hsub _ h, h⟩)
    by_cases hb : β = fun s => ((lam s - sg s : ℕ) : ℤ)
    · subst hb
      obtain ⟨f, hf, e⟩ := GlobalTheory.T.lastRow_top_component_dualWeyl_eq_monomial_mul K n lam y (bmK_mem_alt.1 hy).1 (fun s => lam s - sg s) (fun s => Nat.sub_le _ _) hmax'
      simp only [Nat.sub_sub_self (hIL _).1] at hf
      have hfw : IsWeightedHomogeneous (rowW n n) f sg := (rowWeight_iff _ _).2 fun s => by
        refine lead_inj (fun s => lam s - sg s) ?_
        rw [← rE_lead, map_smul, mul_smul_comm, ← e, ← Module.End.mul_apply, ← (zcomp_comm_rE n _ s s).eq,
          Module.End.mul_apply, hs, map_smul]
      obtain ⟨a, ha⟩ : ∃ a : K, f = a • hw K le_rfl sg :=
        ⟨_, GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight K n sg (bmK_antitone lam sg hIL) f hf hfw⟩
      have hl := bmLift_xi (R := K) lam sg hIL
      have hk := rCap_kill hI (bmList lam sg) (fun _ h => h) (y - a • xiB K lam sg)
        (Submodule.sub_mem _ hy (Submodule.smul_mem _ _ (bmK_liftW hl)))
        (by rw [map_sub, map_smul, e, zcomp_lift hl, ha, map_smul, mul_smul_comm, sub_self])
      have h1 := list_dual _ _ ψ hC (bmList lam sg) (y - a • xiB K lam sg)
      rw [hk, map_zero, bm_list_prod lam sg hI, map_sub, map_smul, hxi, smul_zero, sub_zero] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left (Int.cast_ne_zero.2 (capConst n _ _ hI).1)
    · obtain ⟨hA, hE⟩ := rCap_top y hy β hβ hmax'
      obtain ⟨u, hu⟩ := bm_sep lam _ _ _ hA hAdm hb
      have hcard := Finset.card_erase_lt_of_mem hβS
      have h1 := ih (S.erase β).card (by omega) (rCap K n n u y - ((bmChi lam β u : ℤ) : K) • y)
        (Submodule.sub_mem _ (capelliDeterminantFirstRows_mem_bmW u hy) (Submodule.smul_mem _ _ hy))
        (fun s => by
          rw [map_sub, map_smul, ← Module.End.mul_apply, (rE_comm_rCap n n u s s).eq, Module.End.mul_apply, hs, map_smul,
            smul_sub, smul_comm])
        (S.erase β) le_rfl (fun β' h => by
          rw [map_sub, map_smul, ← Module.End.mul_apply, (zcomp_comm_rCap n β' u).eq, Module.End.mul_apply] at h
          refine Finset.mem_erase.2 ⟨fun e => h ?_, hsub _ fun e => h ?_⟩
          · rw [e, hE, sub_self]
          · rw [e, map_zero, smul_zero, sub_zero])
      rw [map_sub, map_smul, hC, smul_eq_mul, ← sub_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 fun e => hu (Int.cast_injective e).symm)
  rw [← sum_weightedHomogeneousComponent (rowW (n + 1) n) x,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := rowW (n + 1) n) x), map_sum]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  have hy := (rowWeight_iff ρ _).1 (weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW (n + 1) n) ρ x)
  have hm := dualWeylRowGraded K (n + 1) n lam ρ x hx
  by_cases hρ' : ρ = bmRho lam sg
  · subst hρ'
    refine key _ _ (bmK_mem_alt.2 ⟨hm, fun μ hμ => ?_⟩) (fun s => by rw [rE, hy, hρ])
      ((weightedHomogeneousComponent (rowW (n + 1) n) (bmRho lam sg) x).support.image (Finsupp.weight (zW n))) le_rfl
      fun β h => ?_
    · rw [bm_weight_lastW, ← bm_weight_rowW,
        weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW (n + 1) n) _ x hμ]
      simp [bmRho]
    · obtain ⟨μ, hμ⟩ := ne_zero_iff.1 h
      rw [coeff_zcomp] at hμ
      split_ifs at hμ with e
      · exact Finset.mem_image.2 ⟨μ, mem_support_iff.2 hμ, e⟩
      · exact absurd rfl hμ
  · obtain ⟨a, ha⟩ := Function.ne_iff.1 hρ'
    have h1 := hwt a (weightedHomogeneousComponent (rowW (n + 1) n) ρ x)
    rw [hy, map_smul, smul_eq_mul, ← sub_eq_zero, ← sub_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 fun e => ha (Nat.cast_injective e))

theorem fock_xi {lam sg : Fin n → ℕ} (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (x : BP K n)
    (hx : x ∈ dualWeyl K (n + 1) n lam) :
    fockB x (xiB K lam sg) * (fockB (hw K le_rfl sg) (hw K le_rfl sg) * (bfact fun s => lam s - sg s : K)) =
      fockB (xiB K lam sg) (xiB K lam sg) * fockB x (zmon K n (fun s => lam s - sg s) * emb K n (hw K le_rfl sg)) := by
  have hIL := bm_IL_of lam sg hI
  have hl := bmLift_xi (R := K) lam sg hIL
  have hw1 := bm_xi_row (R := K) lam sg hIL
  have hw2 : IsWeightedHomogeneous (rowW (n + 1) n) (zmon K n (fun s => lam s - sg s) * emb K n (hw K le_rfl sg))
      (bmRho lam sg) := fun μ hμ => by
    rw [← zcomp_lift hl, coeff_zcomp] at hμ
    split_ifs at hμ
    · exact hw1 hμ
    · exact absurd rfl hμ
  have h := psi_eq_zero hI
    ((fockB (hw K le_rfl sg) (hw K le_rfl sg) * (bfact fun s => lam s - sg s : K)) • fockBL.flip (xiB K lam sg) -
      fockB (xiB K lam sg) (xiB K lam sg) • fockBL.flip (zmon K n (fun s => lam s - sg s) * emb K n (hw K le_rfl sg)))
    (fun l j hlj x => by
      have h1 := xi_raise (K := K) lam sg l j hlj
      have h2 := rE_lead n l j (fun s => lam s - sg s) (hw K le_rfl sg)
      rw [hw_raise sg l j hlj, map_zero, mul_zero] at h2
      simp only [rE] at h1 h2
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, fockBL_apply, rE, fockB_rowE, h1, h2]
      simp [← fockBL_apply])
    (fun a x => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, fockBL_apply, fockB_rowE,
        (rowWeight_iff _ _).1 hw1 a, (rowWeight_iff _ _).1 hw2 a]
      simp only [← fockBL_apply, map_smul, smul_eq_mul]
      ring)
    (by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, fockBL_apply, smul_eq_mul]
      rw [fockB_zcomp _ _ _ (bmF_lead_WH K n _ _), zcomp_lift hl, (GlobalTheory.T.fockPairing_lastRow_monomial_reads_coefficient K n _).2]
      ring) x hx
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, fockBL_apply, smul_eq_mul] at h
  linear_combination h

theorem lift_rowE {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) K} {G : BP K n} (h : bmLift K n lam b f G)
    (i j : Fin n) : bmLift K n lam b (rowE K n n i j f) (rE K n n i j G) := by
  have h1 := bmK_mem_alt.1 (glOperatorFirstRows_mem_bmW i j (bmK_liftW h))
  refine ⟨h1.1, h1.2, ?_⟩
  rw [← rE_lead, ← map_sub, bm_isLow_iff]
  intro β hβ
  rw [← Module.End.mul_apply, (zcomp_comm_rE n β i j).eq, Module.End.mul_apply, (bm_isLow_iff _ _).1 h.2.2 β hβ, map_zero]

theorem fock_lift {lam sg : Fin n → ℕ} (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (ℓ : List ℤ)
    (hℓ : ∀ u ∈ bmList lam sg, u ∈ ℓ) {f : MvPolynomial (Fin n × Fin n) K} (hf : f ∈ dualWeyl K n n sg) {G : BP K n}
    (hG : bmLift K n lam (fun s => lam s - sg s) f G) (x : BP K n) (hx : x ∈ dualWeyl K (n + 1) n lam) :
    fockB x ((ℓ.map (rCap K n n)).prod G) * (fockB (hw K le_rfl sg) (hw K le_rfl sg) * (bfact fun s => lam s - sg s : K)) =
      (((ℓ.map (bmChi lam fun s => ((lam s - sg s : ℕ) : ℤ))).prod : ℤ) : K) * fockB (xiB K lam sg) (xiB K lam sg) *
        fockB x (zmon K n (fun s => lam s - sg s) * emb K n f) := by
  have hIL := bm_IL_of lam sg hI
  let M : Submodule K (MvPolynomial (Fin n × Fin n) K) :=
    { carrier := {f | ∃ G, bmLift K n lam (fun s => lam s - sg s) f G ∧ ∀ x ∈ dualWeyl K (n + 1) n lam,
        fockB x ((ℓ.map (rCap K n n)).prod G) *
          (fockB (hw K le_rfl sg) (hw K le_rfl sg) * (bfact fun s => lam s - sg s : K)) =
        (((ℓ.map (bmChi lam fun s => ((lam s - sg s : ℕ) : ℤ))).prod : ℤ) : K) * fockB (xiB K lam sg) (xiB K lam sg) *
          fockB x (zmon K n (fun s => lam s - sg s) * emb K n f)}
      add_mem' := by
        rintro f f' ⟨G, hG, e⟩ ⟨G', hG', e'⟩
        refine ⟨G + G', bmLift_add hG hG', fun x hx => ?_⟩
        have h1 := e x hx
        have h2 := e' x hx
        simp only [map_add, mul_add, ← fockBL_apply] at h1 h2 ⊢
        linear_combination h1 + h2
      zero_mem' := ⟨0, bmG_zero _ _ _ _, fun x _ => by simp [← fockBL_apply]⟩
      smul_mem' := by
        rintro c f ⟨G, hG, e⟩
        refine ⟨c • G, bmLift_smul c hG, fun x hx => ?_⟩
        have h1 := e x hx
        simp only [map_smul, mul_smul_comm, smul_eq_mul, ← fockBL_apply] at h1 ⊢
        linear_combination c * h1 }
  obtain ⟨G', hG', e⟩ : f ∈ M := GlobalTheory.T.dualWeyl_le_of_highest_vector_rowOperator_stable K n sg (bmK_antitone lam sg hIL) M
    ⟨_, bmLift_xi lam sg hIL, fun x hx => by
      rw [bm_list_eigen (rCap K n n) (bmChi lam fun s => ((lam s - sg s : ℕ) : ℤ)) _ (fun u => by
        rw [chi_eq hIL]
        exact capDet_eigen _ u _ (fun j => (sg j : ℤ)) (xi_raise lam sg) fun s => by
          rw [rE, (rowWeight_iff _ _).1 (bm_xi_row lam sg hIL)]; simp [bmRho]), ← fockBL_apply, map_smul, fockBL_apply,
        smul_eq_mul, mul_assoc, fock_xi hI x hx, mul_assoc]⟩
    (by
      rintro a b f ⟨G, hG, e⟩
      refine ⟨_, lift_rowE hG a b, fun x hx => ?_⟩
      rw [← rE_lead, ← Module.End.mul_apply, ← (bmK_list_comm _ _ (fun u => rE_comm_rCap n n u a b) ℓ).eq,
        Module.End.mul_apply, rE, ← fockB_rowE, ← fockB_rowE]
      exact e _ (rowE_mem _ _ hx)) hf
  have hk := rCap_kill hI ℓ hℓ (G - G') (Submodule.sub_mem _ (bmK_liftW hG) (bmK_liftW hG'))
    (by rw [map_sub, zcomp_lift hG, zcomp_lift hG', sub_self])
  rw [map_sub, sub_eq_zero] at hk
  rw [hk]
  exact e x hx

end Core

section One

open GlobalTheory.IndefiniteRowSideFullHecke Formalism.L2.Col

variable {K : Type} [Field K] {n : ℕ}

theorem capelli_eq (u : ℤ) : InterlacingNumerators.capelli K n u = rCap K n (n + 1) (u + 1) := by
  unfold InterlacingNumerators.capelli rCap capDet bmPi bmM
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 3
  funext j
  unfold InterlacingNumerators.fOp bmF
  congr 1
  simp only [id]
  split_ifs
  · rw [zsmul_one]; congr 1; ring
  · rfl

theorem zOp_eq (lam : DomWeight (n + 1)) (sg : DomWeight n) :
    InterlacingNumerators.zOp K lam sg = ((zList lam sg).map (rCap K n (n + 1))).prod := by
  unfold InterlacingNumerators.zOp zList
  rw [List.map_flatten, List.prod_flatten, List.map_ofFn, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp, List.map_map]
  congr 2
  funext v
  rw [capelli_eq, Function.comp]
  congr 1
  ring

theorem list_incl (ℓ : List ℤ) (G : BP K n) :
    (ℓ.map (rCap K n (n + 1))).prod (incl K n G) = incl K n ((ℓ.map (rCap K n n)).prod G) := by
  induction ℓ with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, rCap_incl]

theorem detShift_succ (lam : DomWeight (n + 1)) : lam.detShift = lam.w (Fin.last n) := by
  unfold DomWeight.detShift
  rw [dif_pos (Nat.succ_pos n)]
  rfl

theorem fock_gen [CharZero K] {lam : DomWeight (n + 1)} {sg : DomWeight n} (hI : InterlacingNumerators.Interlace lam sg)
    (hE : InterlacingNumerators.EqualLast lam sg) (t : InterlacingNumerators.Gen lam sg) {x : MvPolynomial (Fin (n + 1) × Fin (n + 1)) K}
    (hx : x ∈ nablaSq K (n + 1) lam) :
    fockB x (InterlacingNumerators.zOp K lam sg (InterlacingNumerators.phiGen K lam sg t)) * fockB (extremal K n sg) (extremal K n sg) =
      ((Br.cBr rfl lam sg : ℤ) : K) * fockB (Br.xiBr K rfl lam sg) (Br.xiBr K rfl lam sg) *
        fockB (coefOne K n (fun s => (Br.bBr rfl lam sg s).toNat) x) (InterlacingNumerators.piGen K lam sg t) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.T.branching_list_character_product n lam sg hI hE
  obtain ⟨h6, G, hG, e⟩ := GlobalTheory.T.generators_in_dual_weyl_module K n lam sg hI hE t
  obtain ⟨x', hx', rfl⟩ := GlobalTheory.T.dual_weyl_last_zero_inclusion K n lam.natW (by simp [DomWeight.natW, detShift_succ]) x hx
  have h := fock_lift h1 _ h2 h6 hG x' hx'
  rw [h3, (GlobalTheory.T.fockPairing_lastRow_monomial_reads_coefficient K n _).1] at h
  have hb : ((bfact fun s => lamN lam s - sg.natW s : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun s _ => Nat.factorial_ne_zero _)
  rw [e, zOp_eq, list_incl, fockB_incl, h5, fockB_incl, funext h4]
  refine mul_right_cancel₀ hb ?_
  unfold extremal
  linear_combination h

end One

section Tensor

open GlobalTheory.IndefiniteRowSideFullHecke Formalism.L2.Col Formalism.L2.Col.Br GlobalTheory.BranchFormula
open scoped Pointwise

theorem coeff_prod_rename {A ι : Type} [CommRing A] [Fintype ι] {n : ℕ} (b : ι → Fin n → ℕ)
    (P : ι → MvPolynomial (Unit × Fin n) A) :
    coeff (expOf b) (∏ τ, rename (fun p : Unit × Fin n => (τ, p.2)) (P τ)) =
      ∏ τ, coeff (expOf fun _ : Unit => b τ) (P τ) := by
  classical
  have hinj : ∀ τ : ι, Function.Injective (fun p : Unit × Fin n => (τ, p.2)) :=
    fun τ p q h => Prod.ext rfl (Prod.mk.inj h).2
  have h1 : ∀ τ, rename (fun p : Unit × Fin n => (τ, p.2)) (P τ) =
      ∑ m ∈ (P τ).support, monomial (m.mapDomain fun p : Unit × Fin n => (τ, p.2)) (coeff m (P τ)) := by
    intro τ
    conv_lhs => rw [(P τ).as_sum]
    simp only [map_sum, rename_monomial]
  have h2 : ∀ τ, coeff (expOf fun _ : Unit => b τ) (P τ) =
      ∑ m ∈ (P τ).support, if m = expOf (fun _ : Unit => b τ) then coeff m (P τ) else 0 := by
    intro τ
    conv_lhs => rw [(P τ).as_sum]
    simp only [coeff_sum, coeff_monomial]
  simp only [h1]
  rw [Finset.prod_congr rfl fun τ _ => h2 τ, Finset.prod_univ_sum, Finset.prod_univ_sum, coeff_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← monomial_sum_prod, coeff_monomial, Finset.prod_ite_zero]
  have h3 : ∀ τ s, (∑ τ', (p τ').mapDomain fun q : Unit × Fin n => (τ', q.2)) (τ, s) = p τ ((), s) := by
    intro τ s
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
    · exact Finsupp.mapDomain_apply (hinj τ) (p τ) ((), s)
    · intro τ' _ h
      refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨q, hq⟩
      exact h (Prod.mk.inj hq).1
    · simp
  congr 1
  apply propext
  constructor
  · intro h τ _
    ext q
    rw [← h3 τ q.2, h]
    rfl
  · intro h
    ext q
    rw [h3 q.1 q.2, h q.1 (Finset.mem_univ _)]
    rfl

theorem splitLast_blockEmb {K ι : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (τ : ι) (f : MvPolynomial (Fin N × Fin N) K) :
    splitLast K ι hN (Formalism.GradedWeylDivisibility.blockEmb K τ f) =
      rename (fun p : Unit × Fin n => (τ, p.2))
        (map (rename (R := K) (fun v : Unit × Fin n × Fin n => (τ, v.2))).toRingHom
          (splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) f))) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [Formalism.GradedWeylDivisibility.blockEmb, rename_C, splitLast_C, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have : splitLast K ι hN (Formalism.GradedWeylDivisibility.blockEmb K τ (X v)) =
      rename (fun p : Unit × Fin n => (τ, p.2))
        (map (rename (R := K) (fun v : Unit × Fin n × Fin n => (τ, v.2))).toRingHom
          (splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (X v)))) := by
      obtain ⟨a, s⟩ := v
      rw [fk_blockEmb_X, rename_X]
      rcases cases_idx hN s with rfl | ⟨s, rfl⟩
      · simp only [splitLast_X_lastCol, map_zero]
      · rcases cases_idx hN a with rfl | ⟨a, rfl⟩
        · simp only [splitLast_X_lastRow, map_X, rename_X]
        · simp only [splitLast_X_up, map_C, rename_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
    rw [map_mul, map_mul, hp, this, map_mul, map_mul, map_mul, map_mul]

theorem coefLast_ten {K ι : Type} [Field K] [Fintype ι] {N n : ℕ} (hN : N = n + 1) (b : ι → Fin n → ℕ)
    (f : ι → MvPolynomial (Fin N × Fin N) K) :
    coefLast hN b (ten f) = ten fun τ => rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)
      (coefLast hN (fun _ : Unit => b τ) (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (f τ))) := by
  rw [coefLast_eq_coeff, ten, ten, map_prod]
  simp only [splitLast_blockEmb]
  rw [coeff_prod_rename]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [coeff_map, coefLast_eq_coeff, Formalism.GradedWeylDivisibility.blockEmb, rename_rename]
  rfl

theorem fockB_ten {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) K) :
    fockB (ten f) (ten g) = ∏ τ, fockB (f τ) (g τ) :=
  @fockSymTensor_holds K _ starRingOfComm ι _ n f g

variable {K : Type} [Field K] [CharZero K] {n : ℕ} {ι : Type} [Fintype ι]
  {lam : ι → DomWeight (n + 1)} {sg : ι → DomWeight n}

theorem piAll_mem (hI : ∀ τ, InterlacingNumerators.Interlace (lam τ) (sg τ)) (hE : ∀ τ, InterlacingNumerators.EqualLast (lam τ) (sg τ))
    (t : (∀ τ, InterlacingNumerators.Gen (lam τ) (sg τ)) →₀ K) : InterlacingNumerators.piAll K lam sg t ∈ VV K sg := by
  rw [InterlacingNumerators.piAll, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨_, fun τ => (GlobalTheory.T.generators_in_dual_weyl_module K n _ _ (hI τ) (hE τ) (g τ)).1, rfl⟩)

theorem piAll_surj (hI : ∀ τ, InterlacingNumerators.Interlace (lam τ) (sg τ)) (hE : ∀ τ, InterlacingNumerators.EqualLast (lam τ) (sg τ)) :
    VV K sg ≤ LinearMap.range (InterlacingNumerators.piAll K lam sg) := by
  classical
  rw [InterlacingNumerators.piAll, Finsupp.range_linearCombination]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  have h := GlobalTheory.OrbitSpan.prod_mem_span_prod (K := K) Finset.univ
    (fun τ => Set.range fun g => blockEmb K τ (InterlacingNumerators.piGen K (lam τ) (sg τ) g)) (fun τ => blockEmb K τ (f τ)) fun τ => by
      have h1 := Submodule.mem_map_of_mem (f := (blockEmb K τ).toLinearMap) (GlobalTheory.T.dual_weyl_spanned_by_interlacing K n _ _ (hI τ) (hE τ) (hf τ))
      rw [Submodule.map_span, ← Set.range_comp] at h1
      exact h1
  refine Submodule.span_mono ?_ h
  intro y hy
  obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_prod _ _).1 hy
  choose g' hg' using hg
  exact ⟨g', Finset.prod_congr rfl fun τ _ => hg' τ⟩

theorem fock_extremal_ne (w : DomWeight n) : fockB (extremal K n w) (extremal K n w) ≠ 0 := by
  simpa [extNormB] using pb_extNormB_ne K (fun _ : Unit => w)

theorem pair_gen (hI : ∀ τ, InterlacingNumerators.Interlace (lam τ) (sg τ)) (hE : ∀ τ, InterlacingNumerators.EqualLast (lam τ) (sg τ))
    {F : Pol K ι (n + 1)} (hF : F ∈ VV K lam) (t : (∀ τ, InterlacingNumerators.Gen (lam τ) (sg τ)) →₀ K) :
    pairB lam F (InterlacingNumerators.zPhiAll K lam sg t) =
      pairB sg (brStdP rfl lam sg F : Pol K ι n) (InterlacingNumerators.piAll K lam sg t) := by
  induction t using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single g c =>
    have hm := piAll_mem (K := K) hI hE (Finsupp.single g 1)
    simp only [InterlacingNumerators.zPhiAll, InterlacingNumerators.piAll, Finsupp.linearCombination_single, map_smul, one_smul] at hm ⊢
    congr 1
    induction hF using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      change pairB lam (ten f) _ = pairB sg (brStdP rfl lam sg (ten f) : Pol K ι n) _
      simp only [pairB_apply, brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]
      rw [← fockBL_apply (_ • _), map_smul, LinearMap.smul_apply, fockBL_apply, fockB_projVV sg _ hm, coefLast_ten,
        fockB_ten, fockB_ten, brConst, extNormB, extNormB, smul_eq_mul, ← Finset.prod_inv_distrib,
        ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      have h := fock_gen (hI τ) (hE τ) (g τ) (hf τ)
      have h1 := fock_extremal_ne (K := K) (lam τ)
      have h2 := fock_extremal_ne (K := K) (sg τ)
      unfold coefOne at h
      unfold kapBr bExp
      field_simp
      linear_combination h
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hy, hz]
    | smul a y _ hy => simp only [map_smul, LinearMap.smul_apply, Submodule.coe_smul, hy]

theorem branchT_eq (hI : ∀ τ, InterlacingNumerators.Interlace (lam τ) (sg τ)) (hE : ∀ τ, InterlacingNumerators.EqualLast (lam τ) (sg τ)) :
    InterlacingNumerators.branchT K lam sg = brStd rfl lam sg := by
  ext1 x
  rw [← sub_eq_zero]
  refine (pairingBNondegenerate_holds K ι n sg).1 _ fun y => ?_
  obtain ⟨t, ht⟩ := piAll_surj hI hE y.2
  have h := (InterlacingNumerators.exists_section (InterlacingNumerators.piAll K lam sg)).choose_spec t
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero, InterlacingNumerators.pair_branchT, pairBK_apply]
  simp only [InterlacingNumerators.branch, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [pair_gen hI hE x.2, ← ht, h]
  rfl

theorem pTilde_eq (hI : ∀ τ, InterlacingNumerators.Interlace (lam τ) (sg τ)) (hE : ∀ τ, InterlacingNumerators.EqualLast (lam τ) (sg τ)) (t : ι → K) :
    InterlacingNumerators.pTilde lam sg t = brAt rfl lam sg t := by
  rw [InterlacingNumerators.pTilde, branchT_eq hI hE]
  rfl

end Tensor

section Compare

open GlobalTheory.IndefiniteRowSideFullHecke Formalism.L2.Col Formalism.L2.Col.Br GlobalTheory.BranchFormula NumberField IsDedekindDomain

theorem interlace_iff {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) :
    Br.Interlace rfl lam sg ↔ InterlacingNumerators.Interlace lam sg := by
  refine forall_congr' fun i => ?_
  change 0 ≤ sg.w i - lam.w i.succ ∧ 0 ≤ lam.w i.castSucc - sg.w i ↔ _
  omega

theorem sameShift_iff {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) :
    SameShift lam sg ↔ InterlacingNumerators.EqualLast lam sg ∧ (n = 0 → lam.w (Fin.last n) = 0) := by
  unfold SameShift InterlacingNumerators.EqualLast
  rw [detShift_succ]
  unfold DomWeight.detShift
  split_ifs with h
  · refine ⟨fun e => ⟨fun i hi => ?_, by omega⟩, fun e => e.1 _ (by simp only; omega)⟩
    rw [← e]
    congr 1
    exact Fin.ext (by simp only; omega)
  · exact ⟨fun e => ⟨fun i _ => absurd i.pos h, fun _ => e.symm⟩, fun e => (e.2 (by omega)).symm⟩

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem extLat_eq (M : Submodule (𝓞 K) (Fin n → K)) (t : K) : InterlacingNumerators.extLat M t = sumLat rfl M t := by
  ext x
  rw [InterlacingNumerators.mem_extLat, GlobalTheory.BranchBasis.mem_sumLat]
  exact and_congr Iff.rfl (exists_congr fun c => eq_comm)

omit [NumberField K] in
theorem exists_block (B : GL (Fin n) K) {t : K} (ht : t ≠ 0) : ∃ B' : GL (Fin (n + 1)) K,
    IsBlock rfl (B' : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (B : Matrix (Fin n) (Fin n) K) t := by
  have h : IsBlock rfl (Matrix.of fun a b : Fin (n + 1) => if h : a.val < n ∧ b.val < n then
      (B : Matrix (Fin n) (Fin n) K) ⟨a.val, h.1⟩ ⟨b.val, h.2⟩ else if a = b then t else 0)
      (B : Matrix (Fin n) (Fin n) K) t := by
    refine ⟨fun a b => by simp [iC], fun a => ⟨?_, ?_⟩, by simp [iL]⟩
    · have := a.2
      simp [iC, iL, Fin.ext_iff]; omega
    · have := a.2
      simp [iC, iL, Fin.ext_iff]; omega
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by
    rw [h.det]; exact mul_ne_zero (Matrix.GeneralLinearGroup.det B).ne_zero ht), h⟩

theorem lattice_guard {lam : ι → DomWeight (n + 1)} {sg : ι → DomWeight n} (P : VV K lam →ₗ[K] VV K sg) {t : ι → K}
    (ht : ∀ τ, t τ ≠ 0) :
    (∀ M : ι → Submodule (𝓞 K) (Fin n → K), ∀ x ∈ delK lam fun τ => sumLat rfl (M τ) (t τ), P x ∈ delK sg M) ↔
    (∀ M : ι → Submodule (𝓞 K) (Fin n → K), (∀ τ, Submodule.IsLattice K (M τ)) →
      ∀ x ∈ delK lam fun τ => sumLat rfl (M τ) (t τ), P x ∈ delK sg M) := by
  refine ⟨fun h M _ => h M, fun h M x hx => ?_⟩
  simp only [delK, delP, transLat, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.coe_restrictScalars,
    Submodule.subtype_apply] at hx ⊢
  intro w B hB
  choose B' hB' using fun τ => exists_block (B τ) (ht τ)
  obtain ⟨s, hs, h1⟩ := hx w B' fun τ => GlobalTheory.BranchBasis.isBasisAt_block K _ n rfl w (M τ) (t τ) (B τ) _ (hB' τ) (hB τ)
  have h2 := h (fun τ => colLat (B τ)) (fun τ => GlobalTheory.DualWeyl.isLattice_colLat (B τ)) (s • x) (by
    simp only [← GlobalTheory.BranchBasis.colLat_block rfl _ _ _ (hB' _)]
    change ((s • x : VV K lam) : Pol K ι (n + 1)) ∈ delP lam _
    rw [(GlobalTheory.TransLoc.nabDelLoc_free_leVV.2.1 K ι _ lam B').2]
    refine ⟨_, h1, ?_⟩
    rw [map_smul, LinearMap.coe_restrictScalars, ← polyAction_mul, mul_inv_cancel, polyAction_one₂]
    rfl)
  change ((P (s • x) : VV K sg) : Pol K ι n) ∈ delP sg _ at h2
  rw [(GlobalTheory.TransLoc.nabDelLoc_free_leVV.2.1 K ι _ sg B).2] at h2
  obtain ⟨y, hy, e⟩ := h2
  refine ⟨s, hs, ?_⟩
  rw [← LinearMap.map_smul_of_tower, ← Submodule.coe_smul_of_tower, ← LinearMap.map_smul_of_tower, ← e,
    LinearMap.coe_restrictScalars, ← polyAction_mul, inv_mul_cancel, polyAction_one₂]
  exact hy

variable (K) in

def PTildeAt (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n) : Prop :=
  (∀ τ, InterlacingNumerators.Interlace (lam τ) (sg τ)) → (∀ τ, InterlacingNumerators.EqualLast (lam τ) (sg τ)) →
    ∀ (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
    ∀ (t : ι → K), (∀ τ, t τ ≠ 0) →
    ∀ x : VV K lam, x ∈ delK lam (fun τ => InterlacingNumerators.extLat (M τ) (t τ)) → InterlacingNumerators.pTilde lam sg t x ∈ delK sg M


theorem conclusion_iff {lam : ι → DomWeight (n + 1)} {sg : ι → DomWeight n}
    (hI : ∀ τ, InterlacingNumerators.Interlace (lam τ) (sg τ)) (hE : ∀ τ, InterlacingNumerators.EqualLast (lam τ) (sg τ)) :
    (∀ (M' : ι → Submodule (𝓞 K) (Fin n → K)) (t : ι → K), (∀ τ, t τ ≠ 0) →
      ∀ G ∈ delK lam fun τ => sumLat rfl (M' τ) (t τ), brAt rfl lam sg t G ∈ delK sg M') ↔
    (∀ (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) →
      ∀ (t : ι → K), (∀ τ, t τ ≠ 0) →
      ∀ x : VV K lam, x ∈ delK lam (fun τ => InterlacingNumerators.extLat (M τ) (t τ)) → InterlacingNumerators.pTilde lam sg t x ∈ delK sg M) := by
  simp only [extLat_eq, pTilde_eq hI hE]
  exact ⟨fun h M _ t ht => h M t ht, fun h M t ht => (lattice_guard _ ht).2 (fun M hM => h M hM t ht) M⟩

theorem brIntegral_iff_at (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n)
    (h0 : n = 0 → ∀ τ, (lam τ).w (Fin.last n) = 0) : BrIntegral K rfl lam sg ↔ PTildeAt K lam sg := by
  unfold BrIntegral PTildeAt
  simp only [interlace_iff, sameShift_iff]
  refine forall_congr' fun hI => ⟨fun h hE => (conclusion_iff hI hE).1 (h fun τ => ⟨hE τ, fun e => h0 e τ⟩),
    fun h hS => (conclusion_iff hI fun τ => (hS τ).1).2 (h fun τ => (hS τ).1)⟩

theorem brIntegral_of_at (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n) (h : PTildeAt K lam sg) :
    BrIntegral K rfl lam sg := fun hI hS =>
  have hI' := fun τ => (interlace_iff _ _).1 (hI τ)
  have hE := fun τ => ((sameShift_iff _ _).1 (hS τ)).1
  (conclusion_iff hI' hE).2 (h hI' hE)

theorem at_of_rank_one (lam : ι → DomWeight (0 + 1)) (sg : ι → DomWeight 0)
    (h : BrIntegral K rfl (fun _ : ι => (⟨0, antitone_const⟩ : DomWeight (0 + 1))) sg) : PTildeAt K lam sg := by
  intro hI hE
  refine (conclusion_iff hI hE).1 fun M t ht x hx => ?_
  set lam0 : ι → DomWeight (0 + 1) := fun _ => ⟨0, antitone_const⟩ with hl
  have hn : ∀ τ, (lam0 τ).natW = (lam τ).natW := fun τ => by
    funext i
    obtain rfl : i = Fin.last 0 := Subsingleton.elim (α := Fin 1) _ _
    simp [DomWeight.natW, detShift_succ]
  have hV : VV K lam0 = VV K lam := by simp only [VV, nablaSq, hn]
  have hD : delStd K lam0 = delStd K lam := by simp only [delStd, delSq, hn]
  have hP : brStdP (K := K) rfl lam0 sg = brStdP rfl lam sg := by
    have e1 : brConst rfl K lam0 sg = brConst rfl K lam sg := by simp [brConst, cBr, kapBr, xiBr, extremal, hn]
    have e2 : bExp rfl lam0 sg = bExp rfl lam sg := by funext τ s; exact s.elim0
    rw [brStdP, brStdP, e1, e2]
  have h1 := h (fun τ i => i.elim0) (fun τ => by simp [SameShift, DomWeight.detShift, hl]) M t ht
    ⟨(∏ τ, t τ ^ (-nBr (lam τ) (sg τ))) • (x : Pol K ι (0 + 1)), by rw [hV]; exact Submodule.smul_mem _ _ x.2⟩ (by
      simp only [delK, delP, transLat, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.coe_restrictScalars,
        Submodule.subtype_apply] at hx ⊢
      intro w B hB
      choose B' hB' using fun τ => exists_block (1 : GL (Fin 0) K) (ht τ)
      have hb : ∀ τ, IsBasisAt w (sumLat rfl (M τ) (t τ)) (B' τ) := fun τ =>
        GlobalTheory.BranchBasis.isBasisAt_block K _ 0 rfl w (M τ) (t τ) 1 _ (hB' τ) (Subsingleton.elim _ _)
      rw [GlobalTheory.TestLat.nabIndep_and_delIndep.2 K ι _ lam0 w _ B B' hB hb, hD]
      convert hx w B' hb using 1
      simp only [actP, LinearMap.smul_apply, map_smul, smul_smul]
      congr 1
      simp only [detTwK, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      have hd : (B' τ : Matrix (Fin (0 + 1)) (Fin (0 + 1)) K) 0 0 = t τ := (hB' τ).2.2
      simp [detPow, detShift_succ, hl, nBr, Matrix.GeneralLinearGroup.val_det_apply, hd])
  convert h1 using 1
  simp only [brAt, brStd, hP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_smul]
  simp [nBr, hl]

theorem compare :
    ((∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
      (lam : ι → DomWeight N) (sg : ι → DomWeight n), BrIntegral K hN lam sg) ↔ InterlacingNumerators.PTildeIntegral) ∧
    (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ)
      (lam : ι → DomWeight (n + 1)) (sg : ι → DomWeight n),
      (PTildeAt K lam sg → BrIntegral K rfl lam sg) ∧
      ((n = 0 → ∀ τ, (lam τ).w (Fin.last n) = 0) → (BrIntegral K rfl lam sg ↔ PTildeAt K lam sg)) ∧
      (∀ τ, Br.Interlace rfl (lam τ) (sg τ) ↔ InterlacingNumerators.Interlace (lam τ) (sg τ)) ∧
      (∀ τ, SameShift (lam τ) (sg τ) ↔ InterlacingNumerators.EqualLast (lam τ) (sg τ) ∧ (n = 0 → (lam τ).w (Fin.last n) = 0)) ∧
      (∀ (M : Submodule (𝓞 K) (Fin n → K)) (t : K), InterlacingNumerators.extLat M t = sumLat rfl M t) ∧
      ((∀ τ, InterlacingNumerators.Interlace (lam τ) (sg τ)) → (∀ τ, InterlacingNumerators.EqualLast (lam τ) (sg τ)) →
        ∀ t : ι → K, InterlacingNumerators.pTilde lam sg t = brAt rfl lam sg t)) := by
  refine ⟨⟨fun h K _ _ ι _ n lam sg => ?_, fun h K _ _ ι _ N n hN lam sg => ?_⟩,
    fun K _ _ ι _ n lam sg => ⟨brIntegral_of_at lam sg, brIntegral_iff_at lam sg, fun _ => interlace_iff _ _,
      fun _ => sameShift_iff _ _, extLat_eq, pTilde_eq⟩⟩
  · rcases n with _ | n
    · exact at_of_rank_one lam sg (h K ι _ _ rfl _ sg)
    · exact (brIntegral_iff_at lam sg (by omega)).1 (h K ι _ _ rfl lam sg)
  · subst hN
    exact brIntegral_of_at lam sg (h K ι n lam sg)

end Compare

end GlobalTheory.BrCompare
end
end
