import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.DnIncInt0Of
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.IntegralityAtFormsOfIncrements
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.NaturalTranslateAdelicFunction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.UpLatLoc0Of
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.StabiliserOfLocalTransport

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

theorem integrality_at_forms_of_lattices
    (hR : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → HeckeRationalLevelZero D u)
    (hU : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → UpLatLoc0 T)
    (hD : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → DnLatLoc0 T)
    (D : D7) (u : D.what₂.Word) : Formalism.MainNotions.RT.IntegralityLevelZeroUnderForms D u :=
  integrality_at_forms_of_increments hR (fun D u T hC hA hS => upIncInt0_of T hC (hU D u T hC hA hS))
    (fun D u T hC hA hS => dnIncInt0_of T hC (hD D u T hC hA hS)) D u

end PI.UnitaryGroupMassFormula.IAT

end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField Classical IsDedekindDomain Formalism.UG

def ratO (D : D7) : Subring ℂ := (⊤ : Subring D.what₂.LL).map D.what₂.embLL

theorem ratO_mem (D : D7) (r : D.what₂.LL) : D.what₂.embLL r ∈ ratO D :=
  Subring.mem_map.2 ⟨r, Subring.mem_top _, rfl⟩

theorem ratO_loc (D : D7) : bwE_Loc (ratO D) := by
  intro r s c m hc hm hsum
  by_contra hno
  have h0 : ∀ i ∈ s, m i = 0 := by
    intro i hi
    by_contra hne
    obtain ⟨q, -, hq⟩ := Subring.mem_map.1 (hm i)
    refine hno ⟨i, hi, D.what₂.embLL q⁻¹, ratO_mem D _, ?_⟩
    rw [map_inv₀, hq, mul_inv_cancel₀ hne]
  rw [Finset.sum_eq_zero (fun i hi => by rw [h0 i hi, mul_zero])] at hsum
  exact zero_ne_one hsum

theorem ratGLStab (D : D7) {n : ℕ} (ν : DomWeight n) (s : ℤ) (M M' : Matrix (Fin n) (Fin n) ℂ) (hMM' : M * M' = 1)
    (hM : ∀ a b, M a b ∈ ratO D) (hM' : ∀ a b, M' a b ∈ ratO D) (g : MvPolynomial (Fin n × Fin n) ℤ)
    (hg : g ∈ delSq ℤ n ν) :
    M.det ^ s • Formalism.GradedWeylDivisibility.rowAct ℂ M (MvPolynomial.map (Int.castRingHom ℂ) g) ∈
      bwA_span (ratO D) le_rfl ν.natW := by
  have hM'M : M' * M = 1 := mul_eq_one_comm.1 hMM'
  have hEO : M ∈ bwA_EO (ratO D) n := bwE_elim (ratO_loc D) M hM ⟨M', hM', hM'M⟩
  have hg' : MvPolynomial.map (Int.castRingHom ℂ) g ∈ bwA_span (ratO D) le_rfl ν.natW :=
    Submodule.subset_span ⟨g, hg, rfl⟩
  have hrow := bwA_span_closure (ratO D) le_rfl ν.natW M hEO _ hg'
  have hdet : M.det * M'.det = 1 := by rw [← Matrix.det_mul, hMM', Matrix.det_one]
  have hdM : M.det ∈ ratO D := bwE_det_mem hM
  have hdM' : M'.det ∈ ratO D := bwE_det_mem hM'
  have hds : M.det ^ s ∈ ratO D := by
    rcases s with k | k
    · rw [Int.ofNat_eq_natCast, zpow_natCast]
      exact pow_mem hdM k
    · have e : M.det ^ (Int.negSucc k) = M'.det ^ (k + 1) := by
        rw [zpow_negSucc, ← inv_pow]
        congr 1
        exact inv_eq_of_mul_eq_one_right hdet
      rw [e]
      exact pow_mem hdM' _
  have e : M.det ^ s • Formalism.GradedWeylDivisibility.rowAct ℂ M (MvPolynomial.map (Int.castRingHom ℂ) g) =
      (⟨M.det ^ s, hds⟩ : ratO D) • Formalism.GradedWeylDivisibility.rowAct ℂ M (MvPolynomial.map (Int.castRingHom ℂ) g) := rfl
  rw [e]
  exact Submodule.smul_mem _ _ hrow

theorem ratSpan_smul (D : D7) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (r : D.what₂.LL)
    (P : MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ) (hP : P ∈ Formalism.L2.Forms.RatSpan D lam) :
    D.what₂.embLL r • P ∈ Formalism.L2.Forms.RatSpan D lam := by
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r', f, hf, rfl⟩ := hp
    exact AddSubgroup.subset_closure ⟨r * r', f, hf, by rw [smul_smul, map_mul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

open Classical in

theorem ratSpan_ten (D : D7) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (τv : D.what₂.Tau)
    (f : D.what₂.Tau → MvPolynomial (Fin N × Fin N) ℤ) (hf : ∀ τ, f τ ∈ delSq ℤ N (lam τ))
    (q : MvPolynomial (Fin N × Fin N) ℂ) (hq : q ∈ bwA_span (ratO D) le_rfl (lam τv).natW) (r : D.what₂.LL) :
    D.what₂.embLL r • Formalism.L2.Forms.ten (Function.update (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) τv q) ∈
      Formalism.L2.Forms.RatSpan D lam := by
  classical
  induction hq using Submodule.span_induction generalizing r with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨r, Function.update f τv g, fun τ => ?_, ?_⟩
    · by_cases h : τ = τv
      · subst h; rw [Function.update_self]; exact hg
      · rw [Function.update_of_ne h]; exact hf τ
    · congr 1
      congr 1
      funext τ
      by_cases h : τ = τv
      · subst h; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h, Function.update_of_ne h]
  | zero =>
    rw [bwA_ten_update]; simp
  | add x y _ _ hx hy =>
    have e : Formalism.L2.Forms.ten (Function.update (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) τv (x + y)) =
        Formalism.L2.Forms.ten (Function.update (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) τv x) +
          Formalism.L2.Forms.ten (Function.update (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) τv y) := by
      rw [bwA_ten_update, bwA_ten_update, bwA_ten_update, map_add, add_mul]
    rw [e, smul_add]
    exact AddSubgroup.add_mem _ (hx r) (hy r)
  | smul o x _ hx =>
    obtain ⟨r', -, ho⟩ := Subring.mem_map.1 o.2
    have e : Formalism.L2.Forms.ten (Function.update (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) τv (o • x)) =
        (o : ℂ) • Formalism.L2.Forms.ten (Function.update (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) τv x) := by
      rw [bwA_ten_update, bwA_ten_update]
      show MvPolynomial.rename _ ((o : ℂ) • x) * _ = _
      rw [map_smul, smul_mul_assoc]
    rw [e, smul_smul, ← ho, ← map_mul]
    exact hx (r * r')

open Classical in

theorem ratSpan_subP (D : D7) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (τv : D.what₂.Tau)
    (o : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (ho : ∀ τ, τ ≠ τv → o τ = 1) (c : ℂ)
    (hB : ∀ g ∈ delSq ℤ N (lam τv),
      c • Formalism.GradedWeylDivisibility.rowAct ℂ (o τv) (MvPolynomial.map (Int.castRingHom ℂ) g) ∈
        bwA_span (ratO D) le_rfl (lam τv).natW)
    (P : MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ) (hP : P ∈ Formalism.L2.Forms.RatSpan D lam) :
    c • subP o P ∈ Formalism.L2.Forms.RatSpan D lam := by
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    set F : D.what₂.Tau → MvPolynomial (Fin N × Fin N) ℂ := fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ) with hF
    have h1 : (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (o τ) (F τ)) = Function.update F τv (Formalism.GradedWeylDivisibility.rowAct ℂ (o τv) (F τv)) := by
      funext τ
      by_cases h : τ = τv
      · subst h; rw [Function.update_self]
      · rw [Function.update_of_ne h, ho τ h, bwA_rowAct_one]
    have e : c • subP o (D.what₂.embLL r • Formalism.L2.Forms.ten F) =
        D.what₂.embLL r • Formalism.L2.Forms.ten (Function.update F τv (c • Formalism.GradedWeylDivisibility.rowAct ℂ (o τv) (F τv))) := by
      rw [map_smul, substitution_tensor, h1, smul_comm, bwA_ten_update, bwA_ten_update, map_smul, smul_mul_assoc]
    rw [e]
    exact ratSpan_ten D lam τv f hf _ (hB (f τv) (hf τv)) r
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

theorem ratSpan_allSubP (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (N : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (s : D.what₂.Tau → ℤ)
    (hB : ∀ τ, ∀ g ∈ delSq ℤ n (lam τ), (N τ).det ^ s τ • Formalism.GradedWeylDivisibility.rowAct ℂ (N τ) (MvPolynomial.map (Int.castRingHom ℂ) g) ∈
      bwA_span (ratO D) le_rfl (lam τ).natW)
    (Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hQ : Q ∈ Formalism.L2.Forms.RatSpan D lam) :
    MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * subP N Q ∈ Formalism.L2.Forms.RatSpan D lam := by
  have key : ∀ S : Finset D.what₂.Tau, MvPolynomial.C (∏ τ ∈ S, (N τ).det ^ s τ) *
      subP (fun τ => if τ ∈ S then N τ else 1) Q ∈ Formalism.L2.Forms.RatSpan D lam := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, map_one, one_mul, Finset.notMem_empty, if_false]
      rw [substitution_one]
      exact hQ
    | insert τ0 S h0 ih =>
      set U : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := Function.update 1 τ0 (N τ0) with hU
      have hU1 : ∀ τ, τ ≠ τ0 → U τ = 1 := fun τ hτ => by rw [hU, Function.update_of_ne hτ]; rfl
      have hUτ : U τ0 = N τ0 := by rw [hU, Function.update_self]
      have hcomp : (fun τ => (if τ ∈ S then N τ else 1) * U τ) = fun τ => if τ ∈ insert τ0 S then N τ else 1 := by
        funext τ
        by_cases hτ : τ = τ0
        · subst hτ
          rw [if_neg h0, if_pos (Finset.mem_insert_self _ _), one_mul, hUτ]
        · rw [hU1 τ hτ, mul_one]
          by_cases hS : τ ∈ S
          · rw [if_pos hS, if_pos (Finset.mem_insert_of_mem hS)]
          · rw [if_neg hS, if_neg (by simp [hτ, hS])]
      have e : MvPolynomial.C (∏ τ ∈ insert τ0 S, (N τ).det ^ s τ) *
          subP (fun τ => if τ ∈ insert τ0 S then N τ else 1) Q =
          (N τ0).det ^ s τ0 • subP U (MvPolynomial.C (∏ τ ∈ S, (N τ).det ^ s τ) *
            subP (fun τ => if τ ∈ S then N τ else 1) Q) := by
        have hC : ∀ x, subP U (MvPolynomial.C x) = MvPolynomial.C x := fun x => by
          rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
        rw [map_mul, substitution_substitution, hcomp, Finset.prod_insert h0, map_mul, MvPolynomial.smul_eq_C_mul, hC, mul_assoc]
      rw [e]
      refine ratSpan_subP D lam τ0 U hU1 _ ?_ _ ih
      intro g hg
      rw [hUτ]
      exact hB τ0 g hg
  have h := key Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  exact h

variable {D : D7} {u : D.what₂.Word}

def RatC (T : Forms0 D u) (h : (D.mem u).C.Y 0 → ℂ) : Prop :=
  ∃ P ∈ Formalism.L2.Forms.RatSpan D ((D.fm u).lam 0), ∀ z, h z = fnOf _ (shiftOf (lamT u 0)) 1 P (T.val0.eY z)

theorem ratC_sum (T : Forms0 D u) {ι : Type} (s : Finset ι) (h : ι → (D.mem u).C.Y 0 → ℂ)
    (hh : ∀ i ∈ s, RatC T (h i)) : RatC T (∑ i ∈ s, h i) := by
  choose! P hP hPe using hh
  refine ⟨∑ i ∈ s, P i, AddSubgroup.sum_mem _ fun i hi => hP i hi, fun z => ?_⟩
  rw [map_sum, Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => hPe i hi z

theorem fnOf_trR (s : D.what₂.Tau → ℤ) (M : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hg : g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (y : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embT D))) :
    fnOf _ s M P (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) g hg y) =
      fnOf _ s (fun τ => M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) P y := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, frameTranslate, Matrix.mul_assoc]

theorem atInf_ratO (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) (a b : Fin (D.R.N 0)) :
    atInf (embT D) M τ a b ∈ ratO D := by
  show embT D τ (M a b) ∈ ratO D
  rw [bwA_embT_eq]
  exact ratO_mem D _

set_option maxHeartbeats 1000000 in

theorem ratC_tr (T : Forms0 D u) (hC : LocalLatticeBases.ChiFin0 T)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κ : T.cls0.lev.U)
    (h : (D.mem u).C.Y 0 → ℂ) (hh : RatC T h) :
    RatC T (fun s => ((((T.cls0.lev.chi κ)⁻¹ : ℂˣ)) : ℂ) *
      h (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
        ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) (T.val0.eY s)))) := by
  obtain ⟨P, hP, hPe⟩ := hh
  obtain ⟨n, -, hc⟩ := hC
  obtain ⟨-, r, hr⟩ := hc 0 (Nat.zero_le _) rfl κ
  set N : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    atInf (embT D) ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ with hNdef
  have hNN' : ∀ τ, N τ * atInf (embT D) ((γ.1 : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ = 1 := fun τ =>
    mul_eq_one_comm.1 (LocalLatticeBases.at_infinity_mul_inv _ γ.1 τ)
  have e1 : ∀ z, h (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
        ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) (T.val0.eY z))) =
      fnOf _ (shiftOf (lamT u 0)) (fun τ => N τ * (1 : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ) τ) P
        (T.val0.eY z) := by
    intro z
    rw [hPe, Equiv.apply_symm_apply, fnOf_trR]
    simp only [hNdef, Pi.one_apply, one_mul, mul_one]
  have e2 : ((((T.cls0.lev.chi κ)⁻¹ : ℂˣ)) : ℂ) = D.what₂.embLL r⁻¹ := by
    rw [map_inv₀, Units.val_inv_eq_inv_val]
    exact congrArg _ hr.symm
  refine ⟨D.what₂.embLL r⁻¹ • (MvPolynomial.C (∏ τ, (N τ).det ^ shiftOf (lamT u 0) τ) * subP N P),
    ratSpan_smul D _ r⁻¹ _ (ratSpan_allSubP D _ N _ (fun τ q hq => ratGLStab D _ _ (N τ) _ (hNN' τ)
      (atInf_ratO _ τ) (atInf_ratO _ τ) q hq) P hP), fun z => ?_⟩
  have e3 := e1 z
  rw [LocalLatticeBases.fnOf_mul] at e3
  change ((((T.cls0.lev.chi κ)⁻¹ : ℂˣ)) : ℂ) * h (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
        ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) (T.val0.eY z))) = _
  rw [e3, e2, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]

theorem up_operator_preserves_rational_form (T : Forms0 D u) (hC : LocalLatticeBases.ChiFin0 T) (v : (D.mem u).A.vT) (x : Vl D u 0) :
    ∃ y, (D.fm u).emb 0 y = Uop D u 0 v ((D.fm u).emb 0 x) := by
  have hx := (T.val0.rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩
  refine (T.val0.rat _).2 ⟨Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.U_op_preserves_forms_zero T v _ hx.1, fun c => ?_⟩
  show RatC T _
  rw [uop_apply]
  refine ratC_sum T _ _ fun y hy => ?_
  obtain ⟨z, rfl⟩ := T.lv0.pr_surj v c y
  obtain ⟨γ, η, κ, -, -, -, -, -, h6⟩ := T.up_natural_level_zero v c z (Finset.mem_filter.1 hy).2
  have e : (D.fm u).upT 0 v c (T.lv0.pr v c z) ((D.fm u).emb 0 x ((D.fm u).up 0 v c (T.lv0.pr v c z))) = fun s =>
      ((((T.cls0.lev.chi κ)⁻¹ : ℂˣ)) : ℂ) * (D.fm u).emb 0 x ((D.fm u).up 0 v c (T.lv0.pr v c z))
        (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
          ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) (T.val0.eY s))) :=
    funext fun s => h6 _ s _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.is_translate_inverse T γ s)
  rw [e]
  exact ratC_tr T hC γ κ _ (hx.2 _)

theorem down_operator_preserves_rational_form (T : Forms0 D u) (hC : LocalLatticeBases.ChiFin0 T) (v : (D.mem u).A.vT) (x : Vl D u 0) :
    ∃ y, (D.fm u).emb 0 y = Dop D u 0 v ((D.fm u).emb 0 x) := by
  have hx := (T.val0.rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩
  refine (T.val0.rat _).2 ⟨Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.D_op_preserves_forms_zero T v _ hx.1, fun c => ?_⟩
  show RatC T _
  rw [dop_apply]
  refine ratC_sum T _ _ fun g hg => ?_
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 := (Finset.mem_filter.1 hg).2
    rw [h0, LinearMap.zero_apply] at h1
    exact zero_ne_one h1
  obtain ⟨γ, η, κ, -, -, -, -, h5⟩ := T.down_natural_level_zero v c g hg0
  have e : (D.fm u).dnT 0 v c g ((D.fm u).emb 0 x ((D.fm u).dn 0 v c g)) = fun s =>
      ((((T.cls0.lev.chi κ)⁻¹ : ℂˣ)) : ℂ) * (D.fm u).emb 0 x ((D.fm u).dn 0 v c g)
        (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
          ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) (T.val0.eY s))) :=
    funext fun s => h5 _ s _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.is_translate_inverse T γ s)
  rw [e]
  exact ratC_tr T hC γ κ _ (hx.2 _)

theorem rationality_of_finite_character (T : Forms0 D u) (hC : LocalLatticeBases.ChiFin0 T) : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeRationalLevelZero D u :=
  fun v x => ⟨up_operator_preserves_rational_form T hC v x, down_operator_preserves_rational_form T hC v x⟩

end PI.UnitaryGroupMassFormula.IAT

end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

theorem integrality_at_forms_of_away_up
    (hA : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → AwayLat0 T)
    (hD : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → DnLatLoc0 T)
    (D : D7) (u : D.what₂.Word) : Formalism.MainNotions.RT.IntegralityLevelZeroUnderForms D u :=
  integrality_at_forms_of_lattices (fun D u T hC _ _ => rationality_of_finite_character T hC) (fun D u T hC hA' hS => upLatLoc0_of T (hA D u T hC hA' hS)) hD D u

end PI.UnitaryGroupMassFormula.IAT

end
end

section
noncomputable section

open NumberField Ideal IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cls_tLd (K : ClsTied u i hi) (c : (D.mem u).C.cls i) (y : Fin (D.R.N i) → D.host.E) (hy : y ∈ Ld D u i hi c) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y ∈ clsCrd D u i hi c := by
  have hM : clsCrd D u i hi c = Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb :=
    Formalism.L2.GlobalTheoryTheory.Comp.eq_glob_of_hat (tld_isLat i hi c) (K.y c).1 (fun w => K.y_lat c w)
  rw [dual_class_lattice_eq_global K c] at hy
  rw [hM]
  have key : Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb ≤
      K.lev.Lb.comap ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • LinearMap.id) := by
    unfold Formalism.L2.GlobalTheoryTheory.Comp.dl
    refine Submodule.span_le.mpr ?_
    intro z hz
    have h2 := K.lev.Lb_dual z hz
    simpa [Nat.cast_smul_eq_nsmul] using h2
  have hG : ∀ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb,
      ((((D.mem u).A.T : ℕ) : D.host.E) • (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)) *ᵥ x ∈
        K.lev.Lb := by
    intro x hx
    have h2 := key hx
    simp only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at h2
    have h3 : ((((D.mem u).A.T : ℕ) : D.host.E) • (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)) *ᵥ x =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • x := by
      ext j
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    rw [h3]
    exact h2
  have hy' : ((((K.y c).1)⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.vi D.host.F y ∈
      Formalism.L2.GlobalTheoryTheory.Comp.hat D.host.F (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) := hy
  have h1 := Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.hat_fwd _ hG _ hy'
  show ((((K.y c).1)⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ
      Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.vi D.host.F ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y) ∈
    Formalism.L2.GlobalTheoryTheory.Comp.hat D.host.F K.lev.Lb
  convert h1 using 1
  have hv : Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.vi D.host.F ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y) =
      ((D.mem u).A.T) • Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.vi D.host.F y := by
    ext k
    simp [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.vi, Nat.cast_smul_eq_nsmul]
  have hGm : ∀ w : Fin (D.R.N i) → TensorProduct D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      ((((D.mem u).A.T : ℕ) : D.host.E) • (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *ᵥ w = ((D.mem u).A.T) • w := by
    intro w
    ext k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, apply_ite, map_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, map_natCast, Pi.smul_apply, nsmul_eq_mul]
  rw [hv, hGm, Matrix.mulVec_smul]

set_option maxHeartbeats 1000000 in

theorem lk_locP (A : AtTTied u) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Lk A i hi v c) = Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (clsCrd D u i hi c) := by
  apply le_antisymm
  · obtain ⟨s, hs, h⟩ := unr_smul A v
    intro x hx
    obtain ⟨r, hr, hrx⟩ := (rlv_mem_locP _ _ _).1 hx
    obtain ⟨l, hl, m, hm, ex⟩ := Submodule.mem_sup.1 hrx
    obtain ⟨y, hy, ey⟩ := h (Ld D u i hi c) m hm
    refine (rlv_mem_locP _ _ _).2 ⟨s * r, fun h' => (Ideal.IsPrime.mem_or_mem inferInstance h').elim hs hr, ?_⟩
    rw [mul_smul, ← ex, smul_add, ey]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hl) (cls_tLd K c y hy)
  · intro x hx
    obtain ⟨r, hr, hrx⟩ := (rlv_mem_locP _ _ _).1 hx
    exact (rlv_mem_locP _ _ _).2 ⟨r, hr, Submodule.mem_sup_left hrx⟩

end PI.UnitaryGroupMassFormula.IAT

end
end

section
noncomputable section

open NumberField Ideal Matrix IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Host Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.UG

variable {D : D7} {u : D.what₂.Word}

theorem dnLatLoc0_of_away (T : Forms0 D u) (hA : AwayLat0 T) : DnLatLoc0 T := by
  intro w hw hs v c g hg γ η κ hη hy hP B B' B₂ hB hB' hB₂ τ
  split_ifs with hτ
  · subst hτ
    have hk := lk_locP T.atT T.cls0 v c
    refine intInv_of_loc T.atT w hw hs v B₂ B' γ.1 hB₂ hB' ?_ ?_
    · rw [hP, ← hk]
      exact le_locP' _ _
    · rw [hk, ← hP]
      exact le_locP' _ _
  · obtain ⟨v', rfl⟩ : ∃ v', (D.fm u).tauOf w v' = τ := ⟨((D.fm u).tauOf w).symm τ, by simp⟩
    have hv' : v' ≠ v := fun h => hτ (h ▸ rfl)
    have hA' := hA v v' hv' c ((D.fm u).dn 0 v c g) γ η κ hη hy
    refine intInv_of_loc T.atT w hw hs v' B₂ B γ.1 hB₂ hB ?_ ?_
    · rw [hA']
      exact le_locP' _ _
    · rw [← hA']
      exact le_locP' _ _

end PI.UnitaryGroupMassFormula.IAT

end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

theorem integrality_at_forms_of_away
    (hA : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → AwayLat0 T)
    (D : D7) (u : D.what₂.Word) : Formalism.MainNotions.RT.IntegralityLevelZeroUnderForms D u :=
  integrality_at_forms_of_away_up hA (fun D u T hC hA' hS => dnLatLoc0_of_away T (hA D u T hC hA' hS)) D u

end PI.UnitaryGroupMassFormula.IAT

end
end
