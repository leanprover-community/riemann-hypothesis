import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleTopSelfIntersectionPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefOfNonzeroSectionPowInduction
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.IntersectionNumberNonnegEffective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberNonnegOfNefAmpleAddNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberAmpleConsNefNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasNonzeroSecPowOfAmpleSubAmpleStatement

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem interNum_cons_nef_ample_nonneg :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (N : LB X) (P : Fin d → LB X), IsNef k N → (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F (Fin.cons N P : Fin (d + 1) → LB X) := by
  intro k _ _ X _ hp d
  have hf := algebraMap_eq_strHom k X
  haveI := isNoetherian_of_isProjOver hp
  induction d with
  | zero =>
    intro F _ hF N P hN _
    haveI : IsProper (strHom k X) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
    have hN' := (isNef_iff hf).1 hN
    have e : (Fin.cons N P : Fin (0 + 1) → LB X) = ![N] := by
      ext i; fin_cases i; rfl
    rw [e]
    refine SheafCycle.interNum_nonneg_of_interNumRed_nonneg k X hp 1 F (by simpa using hF) ![N]
      (fun i => by fin_cases i; exact hN'.1) fun Z hZ hd => hN'.2 Z hZ (by simpa using hd)
  | succ d ih =>
    intro F _ hF N P hN hP
    have hPb : ∀ i, (P i).IsLB := fun i => (hP i).isLB
    set A := P 0
    set Q : Fin d → LB X := Fin.tail P
    have hQ : ∀ i, IsAmpleLB (Q i) := fun i => hP _
    have hQb : ∀ i, (Q i).IsLB := fun i => (hQ i).isLB
    have hPe : P = Fin.cons A Q := (Fin.cons_self_tail P).symm
    have hL : ∀ i, (Fin.cons N P : Fin (d + 2) → LB X) i |>.IsLB := isLB_cons hN.isLB hPb
    have hsw : (Fin.cons N P : Fin (d + 2) → LB X) ∘ Equiv.swap 0 1 =
        (Fin.cons A (Fin.cons N Q) : Fin (d + 2) → LB X) := by
      rw [hPe]; ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun l => ?_) j
        · rfl
        · have h1 : l.succ.succ ≠ (1 : Fin (d + 2)) := by
            rw [← Fin.succ_zero_eq_one]; exact (Fin.succ_injective _).ne (Fin.succ_ne_zero l)
          rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) h1]
          rfl
    rw [← interNum_comp_perm k F hL (Equiv.swap 0 1), hsw]
    have hfin := finiteCohTwists_of_isProjOver hf F hp
    have hv := diffVanish_chiPic_of_isProjOver hf F hp hF
    obtain ⟨a, ha, s, hs, -⟩ := (hP 0).exists_mono_cutHom F
    have hLa := isLB_lbPow (hP 0).isLB a
    have hNQ : ∀ i, (Fin.cons N Q : Fin (d + 1) → LB X) i |>.IsLB := isLB_cons hN.isLB hQb
    have h0 := ih (cut F hLa s) (suppDim_cut_le _ hLa s hF) N Q hN hQ
    rw [← interNum_cons_eq_interNum_cut hLa s hNQ hfin] at h0
    have h := hv.interNum_update_of_cls_eq_zsmul (by simp) (isLB_cons (hP 0).isLB hNQ)
      (0 : Fin (d + 2)) hLa (hP 0).isLB (a : ℤ) (cls_lbZPow (hP 0).isLB a _)
    simp only [Fin.update_cons_zero] at h
    rw [h] at h0
    exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast ha)

end GlobalTheory
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_nef_ample_nonneg : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (N : LB X) (P : Fin d → LB X), IsNef k N → (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F (Fin.cons N P : Fin (d + 1) → LB X) := by
  atlas_forward_decl GlobalTheory.interNum_cons_nef_ample_nonneg
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefLower

theorem topSelf_lower : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (A N L : LB X) (hA : IsAmpleLB A) (hN : IsNef k N) (hL : IsAmpleLB L), (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) → ∀ a b : ℕ, cls L hL.isLB = a • cls N hN.isLB + b • cls A hA.isLB → (b : ℤ) ^ (d + 1) * topSelfIntersection k A (d + 1) ≤ topSelfIntersection k L (d + 1) := by
  intro k _ _ X _ hX d hdim A N L hA hN hL hyp a b hcls
  have hsupp : suppDim (GlobalTheory.structureModule X) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
    (QCoh.suppDim_le _).trans hdim
  have hDV : DiffVanish (d + 1 + 1) (chiPic k (GlobalTheory.structureModule X)) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) _ hX hsupp
  have hALB : A.IsLB := hA.isLB
  have hNLB : N.IsLB := hN.isLB
  have hLLB : L.IsLB := hL.isLB
  set R : Fin d → LB X := fun _ => L with hR
  have hL0 : (fun _ : Fin (d + 1) => L) = (Fin.cons L R : Fin (d + 1) → LB X) := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hconsLB : ∀ M : LB X, M.IsLB → ∀ i, ((Fin.cons M R : Fin (d + 1) → LB X) i).IsLB :=
    fun M hM i => Fin.cases hM (fun _ => hLLB) i
  have hadd := DiffVanish.interNum_update_of_cls_eq_add hDV (le_of_eq (Fintype.card_fin _).symm)
    (hconsLB L hLLB) 0 hLLB (isLB_lbPow hNLB a) (isLB_lbPow hALB b)
    (by rw [cls_lbPow hNLB, cls_lbPow hALB]; exact hcls)
  simp only [Fin.update_cons_zero] at hadd
  have hsN := DiffVanish.interNum_update_of_cls_eq_zsmul hDV (le_of_eq (Fintype.card_fin _).symm)
    (hconsLB N hNLB) 0 (isLB_lbPow hNLB a) hNLB (a : ℤ) (by rw [cls_lbPow hNLB]; simp)
  have hsA := DiffVanish.interNum_update_of_cls_eq_zsmul hDV (le_of_eq (Fintype.card_fin _).symm)
    (hconsLB A hALB) 0 (isLB_lbPow hALB b) hALB (b : ℤ) (by rw [cls_lbPow hALB]; simp)
  simp only [Fin.update_cons_zero] at hsN hsA
  have hNpos : 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons N R : Fin (d + 1) → LB X) :=
    T.intersection_nef_ample_nonneg k X hX d _ hsupp N R hN (fun _ => hL)
  have hfam : ∀ j, ((![A, N] : Fin 2 → LB X) j).IsLB := fun j => by
    fin_cases j
    · exact hALB
    · exact hNLB
  have hQLB : ∀ i, ((Fin.cons A R : Fin (d + 1) → LB X) i).IsLB := hconsLB A hALB
  let n : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![1, 0] (fun _ => ![(b : ℤ), (a : ℤ)])
  have hexp := DiffVanish.interNum_of_cls_eq_sum hDV hfam hQLB n (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [n, Fin.sum_univ_two]
    · simp only [n, Fin.sum_univ_two, Fin.cons_succ]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, natCast_zsmul]
      show cls L _ = _
      rw [hcls, add_comm])
  have hterm : ∀ α : Fin (d + 1) → Fin 2,
      0 ≤ (∏ i, n i (α i)) * interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α) := by
    intro α
    have hprod : 0 ≤ ∏ i, n i (α i) := by
      refine Finset.prod_nonneg fun i _ => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [n, Fin.cons_zero]
        generalize α 0 = t
        fin_cases t <;> simp
      · simp only [n, Fin.cons_succ]
        generalize α j.succ = t
        fin_cases t <;> simp
    rcases Fin.exists_fin_two.mp ⟨α 0, rfl⟩ with h0 | h0
    · refine mul_nonneg hprod ?_
      have hcomp : ((![A, N] : Fin 2 → LB X) ∘ α) =
          Fin.cons A (fun j : Fin d => (![A, N] : Fin 2 → LB X) (α j.succ)) := by
        funext i
        refine Fin.cases ?_ (fun j => rfl) i
        simp [h0]
      rw [hcomp]
      refine hyp _ (fun j => ?_)
      generalize α j.succ = t
      fin_cases t
      · exact hA.isNef
      · exact hN
    · have hz : (∏ i, n i (α i)) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ 0) ?_
        simp [n, h0]
      rw [hz, zero_mul]
  let α0 : Fin (d + 1) → Fin 2 := fun _ => 0
  have hsingle : (∏ i, n i (α0 i)) *
      interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α0) ≤
      interNum k (GlobalTheory.structureModule X) (Fin.cons A R : Fin (d + 1) → LB X) := by
    rw [hexp]
    exact Finset.single_le_sum (fun α _ => hterm α) (Finset.mem_univ α0)
  have hprod0 : (∏ i, n i (α0 i)) = (b : ℤ) ^ d := by
    rw [Fin.prod_univ_succ]
    simp [n, α0]
  have hA0 : interNum k (GlobalTheory.structureModule X) ((![A, N] : Fin 2 → LB X) ∘ α0) =
      topSelfIntersection k A (d + 1) := by
    rw [topSelf_def]; rfl
  rw [hprod0, hA0] at hsingle
  rw [topSelf_def k L, hL0, hadd, hsN, hsA]
  have hb : (0 : ℤ) ≤ b := by positivity
  have ha : (0 : ℤ) ≤ a := by positivity
  calc (b : ℤ) ^ (d + 1) * topSelfIntersection k A (d + 1)
      = (b : ℤ) * ((b : ℤ) ^ d * topSelfIntersection k A (d + 1)) := by ring
    _ ≤ (b : ℤ) * interNum k (GlobalTheory.structureModule X) (Fin.cons A R : Fin (d + 1) → LB X) :=
        mul_le_mul_of_nonneg_left hsingle hb
    _ ≤ (a : ℤ) * interNum k (GlobalTheory.structureModule X) (Fin.cons N R : Fin (d + 1) → LB X) +
        (b : ℤ) * interNum k (GlobalTheory.structureModule X) (Fin.cons A R : Fin (d + 1) → LB X) := by
        have := mul_nonneg ha hNpos
        linarith

end GlobalTheory.NefLower
end
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MorseNum

theorem morse_A_sq : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (A N L M : LB X) (hA : IsAmpleLB A) (hN : IsNef k N) (hL : IsAmpleLB L) (hM : M.IsLB), (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) → 0 < topSelfIntersection k A (d + 1) → ∀ q b c : ℕ, 1 ≤ q → q ≤ b → b ≤ c * q → cls L hL.isLB = q • cls N hN.isLB + b • cls A hA.isLB → cls M hM = cls N hN.isLB + c • cls A hA.isLB → 2 * ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X) < q → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons (lbPow A 2) (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) := by
  intro k _ _ X _ hproj d hd A N L M hA hN hL hM hnef htop q b c hq1 hqb hbc hLcls hMcls hlt
  have hD : DiffVanish (d + 1 + 1) (chiPic k (GlobalTheory.structureModule X)) := by
    refine diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom (k := k) (X := X)) _ hproj ?_
    rw [suppDim_structureModule]
    exact hd
  set F := GlobalTheory.structureModule X with hF
  let Lv : Fin 2 → LB X := ![A, N]
  have hLv : ∀ j, (Lv j).IsLB := by
    intro j; fin_cases j
    · exact hA.isLB
    · exact hN.isLB
  have hLvnef : ∀ j, IsNef k (Lv j) := by
    intro j; fin_cases j
    · exact hA.isNef
    · exact hN
  let nL : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![1, 0] (fun _ => ![(b : ℤ), (q : ℤ)])
  let nM : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![1, 0] (fun _ => ![(c : ℤ), 1])
  have hQL : ∀ i, ((Fin.cons A (fun _ : Fin d => L) : Fin (d + 1) → LB X) i).IsLB := by
    intro i; refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hA.isLB
    · simpa using hL.isLB
  have hQM : ∀ i, ((Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X) i).IsLB := by
    intro i; refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hA.isLB
    · simpa using hM
  have eL := DiffVanish.interNum_of_cls_eq_sum hD hLv hQL nL (by
    intro i; refine Fin.cases ?_ (fun i => ?_) i
    · simp [nL, Lv, Fin.sum_univ_two]
    · simp only [nL, Lv, Fin.sum_univ_two, Fin.cons_succ, Fin.cons_zero]
      simp [hLcls, natCast_zsmul, add_comm])
  have eM := DiffVanish.interNum_of_cls_eq_sum hD hLv hQM nM (by
    intro i; refine Fin.cases ?_ (fun i => ?_) i
    · simp [nM, Lv, Fin.sum_univ_two]
    · simp only [nM, Lv, Fin.sum_univ_two, Fin.cons_succ, Fin.cons_zero]
      simp [hMcls, natCast_zsmul, add_comm])
  have hbq : (b : ℤ) ≤ (q : ℤ) * c := by
    have : b ≤ q * c := by rw [mul_comm]; exact hbc
    exact_mod_cast this
  have hent0 : ∀ j : Fin 2, 0 ≤ (![(b : ℤ), (q : ℤ)] : Fin 2 → ℤ) j := by
    intro j; fin_cases j <;> simp
  have hent1 : ∀ j : Fin 2, (![(b : ℤ), (q : ℤ)] : Fin 2 → ℤ) j ≤ (q : ℤ) * (![(c : ℤ), 1] : Fin 2 → ℤ) j := by
    intro j; fin_cases j
    · simpa using hbq
    · simp
  have key : interNum k F (Fin.cons A (fun _ : Fin d => L) : Fin (d + 1) → LB X)
      ≤ (q : ℤ) ^ d * interNum k F (Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X) := by
    rw [eL, eM, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have h01 : a 0 = 0 ∨ a 0 = 1 := by
      generalize a 0 = j
      fin_cases j <;> simp
    rcases h01 with h0 | h0
    · have hJ : 0 ≤ interNum k F (Lv ∘ a) := by
        have hc : Lv ∘ a = Fin.cons A (fun i : Fin d => Lv (a i.succ)) := by
          funext i
          refine Fin.cases ?_ (fun i => ?_) i
          · simp [h0, Lv]
          · simp
        rw [hc]
        exact hnef _ (fun i => hLvnef _)
      have hc : (∏ i, nL i (a i)) ≤ (q : ℤ) ^ d * ∏ i, nM i (a i) := by
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        simp only [nL, nM, Fin.cons_zero, Fin.cons_succ, h0]
        simp only [Matrix.cons_val_zero, one_mul]
        calc (∏ i : Fin d, (![(b : ℤ), (q : ℤ)] : Fin 2 → ℤ) (a i.succ))
            ≤ ∏ i : Fin d, ((q : ℤ) * (![(c : ℤ), 1] : Fin 2 → ℤ) (a i.succ)) :=
              Finset.prod_le_prod (fun i _ => hent0 _) (fun i _ => hent1 _)
          _ = (q : ℤ) ^ d * ∏ i : Fin d, (![(c : ℤ), 1] : Fin 2 → ℤ) (a i.succ) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc (∏ i, nL i (a i)) * interNum k F (Lv ∘ a)
          ≤ ((q : ℤ) ^ d * ∏ i, nM i (a i)) * interNum k F (Lv ∘ a) := mul_le_mul_of_nonneg_right hc hJ
        _ = _ := by ring
    · have hz1 : (∏ i, nL i (a i)) = 0 := by
        rw [Fin.prod_univ_succ]; simp [nL, h0]
      have hz2 : (∏ i, nM i (a i)) = 0 := by
        rw [Fin.prod_univ_succ]; simp [nM, h0]
      rw [hz1, hz2]; simp
  have h2 : interNum k F (Fin.cons (lbPow A 2) (fun _ : Fin d => L) : Fin (d + 1) → LB X)
      = 2 * interNum k F (Fin.cons A (fun _ : Fin d => L) : Fin (d + 1) → LB X) := by
    have hA2 : (lbPow A 2).IsLB := isLB_lbPow hA.isLB 2
    rw [DiffVanish.interNum_cons_of_cls_eq_add hD (le_refl _) (fun _ => hL.isLB) hA2 hA.isLB hA.isLB
      (by rw [cls_lbPow hA.isLB 2 hA2, two_nsmul])]
    ring
  have hq : (0 : ℤ) < (q : ℤ) ^ d := by
    have : (0 : ℤ) < q := by exact_mod_cast hq1
    positivity
  have hlow := NefLower.topSelf_lower k X hproj d hd A N L hA hN hL hnef q b hLcls
  have hqb' : (q : ℤ) ^ (d + 1) ≤ (b : ℤ) ^ (d + 1) :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hqb) _
  have htop1 : (1 : ℤ) ≤ topSelfIntersection k A (d + 1) := htop
  have s4 : (b : ℤ) ^ (d + 1) ≤ (b : ℤ) ^ (d + 1) * topSelfIntersection k A (d + 1) :=
    le_mul_of_one_le_right (by positivity) htop1
  have s1 : ((d : ℤ) + 1) * (2 * interNum k F (Fin.cons A (fun _ : Fin d => L) : Fin (d + 1) → LB X))
      ≤ (q : ℤ) ^ d * (2 * ((d : ℤ) + 1) * interNum k F (Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X)) := by
    have := mul_le_mul_of_nonneg_left key (show (0 : ℤ) ≤ 2 * ((d : ℤ) + 1) by positivity)
    calc _ = 2 * ((d : ℤ) + 1) * interNum k F (Fin.cons A (fun _ : Fin d => L) : Fin (d + 1) → LB X) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have s2 := mul_lt_mul_of_pos_left hlt hq
  have s3 : (q : ℤ) ^ d * q = (q : ℤ) ^ (d + 1) := by ring
  rw [h2]
  linarith

end GlobalTheory.MorseNum
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_intersection_growth_bound : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (A N L M : LB X) (hA : IsAmpleLB A) (hN : IsNef k N) (hL : IsAmpleLB L) (hM : M.IsLB), (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) → 0 < topSelfIntersection k A (d + 1) → ∀ q b c : ℕ, 1 ≤ q → q ≤ b → b ≤ c * q → cls L hL.isLB = q • cls N hN.isLB + b • cls A hA.isLB → cls M hM = cls N hN.isLB + c • cls A hA.isLB → 2 * ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X) < q → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons (lbPow A 2) (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) := by
  atlas_forward_decl GlobalTheory.MorseNum.morse_A_sq
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.KleimanDim

theorem interNum_nonneg_of_ample_tens_nef : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ),
    (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) →
      ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) →
    ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) →
      (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X,
        (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) := by
  intro k _ _ d H X _ hX E _ hE P hP
  refine SheafCycle.interNum_nonneg_of_interNumRed_nonneg k X hX d E hE P (fun i => (hP i).isLB) ?_
  intro Z hZirr hZdim
  haveI := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  letI : Algebra k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
    ((redι Z).appTop.hom.comp (algebraMap k Γ(X, ⊤))).toAlgebra
  have hcompat : ∀ r : k, (redι Z).appTop.hom (algebraMap k Γ(X, ⊤) r) =
      algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r => rfl
  rw [InterModel.interNumRed_eq_interNumOn k (redι Z) Z (range_redι Z) P,
    interNumOn_eq_interNum_pull hcompat (fun i => (hP i).isLB)]
  have hYproj : IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom hcompat]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion (redι Z) hX
  have hYdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ (d : WithBot ℕ∞) := by
    have hmem : ∀ y, (redι Z) y ∈ (Z : Set X) := fun y => by
      rw [← range_redι Z]; exact Set.mem_range_self y
    have hind := ((redι Z).isClosedEmbedding.isInducing.codRestrict hmem).topologicalKrullDim_le
    rw [hZdim] at hind
    exact hind
  have hsupp : suppDim (QCoh.structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ≤ (d : WithBot ℕ∞) :=
    (QCoh.suppDim_le _).trans hYdim
  exact T.intersectionNumber_nonneg_of_nef_ample_add_nef k _ hYproj (fun A N hA hN => H _ hYproj hYdim A N hA hN) d _ hsupp
    (fun i => (P i).pull (redι Z)) (fun i => (hP i).pull_of_isClosedImmersion (redι Z) hcompat)

end GlobalTheory.KleimanDim
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_intersection_nonneg_induction : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) := by
  atlas_forward_decl GlobalTheory.KleimanDim.interNum_nonneg_of_ample_tens_nef
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem isAmpleLB_tens_lbPow_descent_step : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → topologicalKrullDim X = (d + 1 : ℕ) → ∀ (A N M : LB X) (hA : IsAmpleLB A) (hN : IsNef k N) (hM : M.IsLB) (q c : ℕ), 1 ≤ q → cls M hM = cls N hN.isLB + c • cls A hA.isLB → 2 * ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X) < q → ∀ b : ℕ, q ≤ b → b + 1 ≤ c * q → IsAmpleLB (tens (lbPow N q) (lbPow A (b + 1))) → IsAmpleLB (tens (lbPow N q) (lbPow A b)) := by
  intro k _ _ d hlow X _ _ hproj hdim A N M hA hN hM q c hq hMcls hbound b hqb hbc hL
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hdim' : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := hdim.le
  have hKl := GlobalTheory.T.nef_intersection_nonneg_induction k d hlow X hproj
  have hmix := GlobalTheory.T.lineBundleIntersectionNumber_ample_cons_nef_nonneg k X hproj d hdim' hKl A hA
  have hpos := GlobalTheory.T.ample_lineBundle_top_selfIntersection_pos k X hproj (d + 1) hdim A hA
  have hNl := isLB_lbPow hN.isLB q
  have hAl : ∀ n : ℕ, (lbPow A n).IsLB := fun n => isLB_lbPow hA.isLB n
  have hLcls : cls _ hL.isLB = q • cls N hN.isLB + (b' + 1 + 1) • cls A hA.isLB := by
    rw [cls_tens hNl (hAl _), cls_lbPow hN.isLB, cls_lbPow hA.isLB]
  have hnum := GlobalTheory.T.top_intersection_growth_bound k X hproj d hdim' A N _ M hA hN hL hM hmix hpos q (b' + 1 + 1) c hq
    (by omega) hbc hLcls hMcls hbound
  have hB : IsAmpleLB (lbPow A 2) := (isAmpleLB_pow_iff hA.isLB (by norm_num)).2 hA
  have hM'nef : IsNef k (tens (lbPow N q) (lbPow A b')) :=
    (hN.pow hA q).tens ((hA.isNef (k := k)).pow hA b') hA
  have hsplit : cls _ hL.isLB = cls _ hM'nef.isLB + cls _ hB.isLB := by
    rw [hLcls, cls_tens hNl (hAl _), cls_lbPow hN.isLB, cls_lbPow hA.isLB, cls_lbPow hA.isLB]
    simp only [add_smul, one_smul, two_smul]
    abel
  have hsec := GlobalTheory.T.exists_hasNonzeroSec_pow_of_ample_sub_ample' k X hproj d hdim' _ _ _ hL hB hM'nef.isLB hsplit hnum
  have hamp := GlobalTheory.T.isAmple_tensor_nef_of_nonzeroSectionPow_induction k d hlow X hproj hdim' A _ hA hM'nef hsec
  have hT : (tens (lbPow N q) (lbPow A (b' + 1))).IsLB := isLB_tens hNl (hAl _)
  refine hamp.of_lbIso hT ((cls_eq_iff hT hamp.isLB).1 ?_)
  rw [cls_tens hNl (hAl _), cls_tens hA.isLB hM'nef.isLB, cls_tens hNl (hAl _), cls_lbPow hN.isLB,
    cls_lbPow hA.isLB, cls_lbPow hA.isLB]
  simp only [add_smul, one_smul]
  abel
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_nef_descent : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → topologicalKrullDim X = (d + 1 : ℕ) → ∀ A N : LB X, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N) := by
  intro k _ _ d ih X _ _ hproj hdim A N hA hN
  have ampOfCls : ∀ {L M : LB X} (hL : L.IsLB) (hM : IsAmpleLB M), cls L hL = cls M hM.isLB → IsAmpleLB L :=
    fun hL hM h => IsAmpleLB.of_lbIso hM hL ((cls_eq_iff hL hM.isLB).1 h)
  obtain ⟨c, hc1, hcM⟩ := exists_isAmpleLB_tens_lbPow k X hproj A N hA hN.isLB
  have hMLB : (tens N (lbPow A c)).IsLB := isLB_tens hN.isLB (isLB_lbPow hA.isLB c)
  have hMcls : cls (tens N (lbPow A c)) hMLB = cls N hN.isLB + c • cls A hA.isLB := by
    rw [cls_tens hN.isLB (isLB_lbPow hA.isLB c), cls_lbPow hA.isLB]
  set I := interNum k (GlobalTheory.structureModule X) (Fin.cons A (fun _ : Fin d => tens N (lbPow A c)) : Fin (d + 1) → LB X)
  set q : ℕ := (2 * ((d : ℤ) + 1) * I).toNat + 1 with hqdef
  have hq1 : 1 ≤ q := by omega
  have hqlt : 2 * ((d : ℤ) + 1) * I < (q : ℤ) := by
    have := Int.self_le_toNat (2 * ((d : ℤ) + 1) * I)
    rw [hqdef]; push_cast; linarith
  have hP : ∀ b : ℕ, (tens (lbPow N q) (lbPow A b)).IsLB :=
    fun b => isLB_tens (isLB_lbPow hN.isLB q) (isLB_lbPow hA.isLB b)
  have clsP : ∀ b : ℕ, cls _ (hP b) = q • cls N hN.isLB + b • cls A hA.isLB := by
    intro b
    rw [cls_tens (isLB_lbPow hN.isLB q) (isLB_lbPow hA.isLB b), cls_lbPow hN.isLB, cls_lbPow hA.isLB]
  have base : IsAmpleLB (tens (lbPow N q) (lbPow A (c * q))) := by
    have hpow : IsAmpleLB (lbPow (tens N (lbPow A c)) q) := (isAmpleLB_pow_iff hMLB hq1).2 hcM
    refine ampOfCls (hP _) hpow ?_
    rw [clsP, cls_lbPow hMLB, hMcls, smul_add, smul_smul, mul_comm q c]
  have hcq : q ≤ c * q := by nlinarith
  have down : ∀ j : ℕ, j ≤ c * q - q → IsAmpleLB (tens (lbPow N q) (lbPow A (c * q - j))) := by
    intro j
    induction j with
    | zero => intro _; simpa using base
    | succ j hj =>
      intro hj1
      have hprev := hj (by omega)
      have e : c * q - j = (c * q - (j + 1)) + 1 := by omega
      rw [e] at hprev
      exact isAmpleLB_tens_lbPow_descent_step k d ih X hproj hdim A N (tens N (lbPow A c)) hA hN hMLB q c hq1
        hMcls hqlt (c * q - (j + 1)) (by omega) (by omega) hprev
  have hqq := down (c * q - q) le_rfl
  have e2 : c * q - (c * q - q) = q := by omega
  rw [e2] at hqq
  have hTLB : (tens A N).IsLB := isLB_tens hA.isLB hN.isLB
  have hpow : IsAmpleLB (lbPow (tens A N) q) := by
    refine ampOfCls (isLB_lbPow hTLB q) hqq ?_
    rw [cls_lbPow hTLB, cls_tens hA.isLB hN.isLB, clsP, smul_add, add_comm]
  exact (isAmpleLB_pow_iff hTLB hq1).1 hpow

end GlobalTheory
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem withBot_eq_succ_of_le_of_not_le {t : WithBot ℕ∞} {d : ℕ} (h1 : t ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (h2 : ¬ t ≤ (d : WithBot ℕ∞)) : t = ((d + 1 : ℕ) : WithBot ℕ∞) := by
  induction t using WithBot.recBotCoe with
  | bot => exact absurd bot_le h2
  | coe t =>
    induction t using ENat.recTopCoe with
    | top =>
      have h1' : (⊤ : ℕ∞) ≤ ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
      exact absurd h1' (ENat.coe_lt_top (d + 1)).not_ge
    | coe n =>
      have h1' : n ≤ d + 1 := by exact_mod_cast h1
      have h2' : ¬ n ≤ d := fun h => h2 (by exact_mod_cast h)
      have : n = d + 1 := by omega
      subst this; rfl

theorem isAmpleLB_tens_of_isNef_succ : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d + 1 : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) := by
  intro k _ _ d ih Y _ hproj hdimY A N hA hN
  refine IsAmpleLB.tens_of_forall_isPsEff k Y (strHom k Y) hproj A N hA hN.isLB ?_
  intro Z hZ
  let Z' := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme
  letI : Algebra k Γ(Z', ⊤) := ((redι Z).appTop.hom.comp (algebraMap k Γ(Y, ⊤))).toAlgebra
  have compat : ∀ r : k, (redι Z).appTop.hom (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(Z', ⊤) r :=
    fun r => rfl
  haveI hirr : IrreducibleSpace Z' := Subtype.irreducibleSpace (by simpa using hZ)
  haveI hred : IsReduced Z' := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  haveI hint : IsIntegral Z' := isIntegral_of_irreducibleSpace_of_isReduced Z'
  have hdim : topologicalKrullDim Z' ≤ topologicalKrullDim Y :=
    (redι Z).isClosedEmbedding.isInducing.topologicalKrullDim_le
  have hpZ : IsProjOver (strHom k Z') := by
    obtain ⟨n, i, hi, hcomp⟩ := hproj
    refine ⟨n, redι Z ≫ i, ?_, ?_⟩
    · exact IsClosedImmersion.comp _ _
    · rw [Category.assoc, hcomp, comp_strHom compat]
  haveI hne : Nonempty Z' := by
    obtain ⟨y, hy⟩ := hZ.nonempty
    rw [← range_redι Z] at hy
    obtain ⟨z, _⟩ := hy
    exact ⟨z⟩
  haveI hnoeth : IsNoetherian Z' := isNoetherian_of_isProjOver hpZ
  have hAZ : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
  have hNZ : IsNef k (N.pull (redι Z)) := hN.pull_of_isClosedImmersion (redι Z) compat
  refine ⟨hNZ.isLB, A.pull (redι Z), hAZ, fun m hm => ?_⟩
  have hNm : IsNef k (lbPow (N.pull (redι Z)) m) := hNZ.pow hAZ m
  have hamp : IsAmpleLB (tens (A.pull (redι Z)) (lbPow (N.pull (redι Z)) m)) := by
    by_cases hle : topologicalKrullDim Z' ≤ ((d : ℕ) : WithBot ℕ∞)
    · exact ih Z' hpZ hle _ _ hAZ hNm
    · have hle2 : topologicalKrullDim Z' ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := hdim.trans hdimY
      have heq := withBot_eq_succ_of_le_of_not_le hle2 hle
      exact isAmpleLB_tens_of_nef_descent k d ih Z' hpZ heq _ _ hAZ hNm
  have hL'LB : (tens (lbPow (N.pull (redι Z)) m) (A.pull (redι Z))).IsLB :=
    isLB_tens (isLB_lbPow hNZ.isLB m) hAZ.isLB
  have hL'amp : IsAmpleLB (tens (lbPow (N.pull (redι Z)) m) (A.pull (redι Z))) := by
    refine IsAmpleLB.of_lbIso hamp hL'LB ((cls_eq_iff hL'LB hamp.isLB).1 ?_)
    rw [cls_tens (isLB_lbPow hNZ.isLB m) hAZ.isLB, cls_tens hAZ.isLB (isLB_lbPow hNZ.isLB m), add_comm]
  obtain ⟨r, hr1, hsec⟩ := IsAmpleLB.exists_hasNonzeroSec hL'amp (isLB_lbPow hL'LB 0)
  exact ⟨r, hr1, hsec _ (isLB_lbPow hL'LB r) (by rw [cls_lbPow hL'LB, cls_lbPow hL'LB, zero_smul, zero_add])⟩

end GlobalTheory
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.ample_plus_nef_induction : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d + 1 : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) := by
  atlas_forward_decl _root_.GlobalTheory.isAmpleLB_tens_of_isNef_succ
end
