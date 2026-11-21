import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.IntSpanLeRat
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.DuCount
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.RatStab

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Classical

variable {D : D7} {u : D.what₂.Word}

def mixF (τ₀ : D.what₂.Tau) (B B' : GL (Fin (D.R.N 0)) D.host.E) : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  fun τ => if τ = τ₀ then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ
    else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ

private theorem atInf_mul' (X Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    atInf (embT D) (X * Y : GL (Fin (D.R.N 0)) D.host.E).1 τ =
      atInf (embT D) X.1 τ * atInf (embT D) Y.1 τ := by
  simp only [atInf, Units.val_mul, Matrix.map_mul]

private theorem atInf_one' (τ : D.what₂.Tau) :
    atInf (embT D) (1 : GL (Fin (D.R.N 0)) D.host.E).1 τ = 1 := by
  simp only [atInf, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mixed_change (w : D.what₂.places.Pl) (hw : OverT D u w) (τ₀ : D.what₂.Tau)
    {L L' : Set (Fin (D.R.N 0) → D.host.E)} {B B₁ B' B₁' : GL (Fin (D.R.N 0)) D.host.E}
    (hB : IsLocBasis (D.mem u).A.T L B) (hB₁ : IsLocBasis (D.mem u).A.T L B₁)
    (hB' : IsLocBasis (D.mem u).A.T L' B') (hB₁' : IsLocBasis (D.mem u).A.T L' B₁')
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ)
    (hP : P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0)) :
    ∃ P₁ ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0), ∀ y,
      fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (mixF τ₀ B B') P y =
        fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (mixF τ₀ B₁ B₁') P₁ y := by
  let N : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    if τ = τ₀ then atInf (embT D) (B'⁻¹ * B₁' : GL (Fin (D.R.N 0)) D.host.E).1 τ
    else atInf (embT D) (B⁻¹ * B₁ : GL (Fin (D.R.N 0)) D.host.E).1 τ
  let N' : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    if τ = τ₀ then atInf (embT D) (B₁'⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E).1 τ
    else atInf (embT D) (B₁⁻¹ * B : GL (Fin (D.R.N 0)) D.host.E).1 τ
  have hmul : ∀ τ, N τ * N' τ = 1 := by
    intro τ
    by_cases hτ : τ = τ₀
    · simp only [N, N', if_pos hτ]
      rw [← atInf_mul', show B'⁻¹ * B₁' * (B₁'⁻¹ * B') = 1 by group, atInf_one']
    · simp only [N, N', if_neg hτ]
      rw [← atInf_mul', show B⁻¹ * B₁ * (B₁⁻¹ * B) = 1 by group, atInf_one']
  have hN : ∀ τ a b, N τ a b ∈ bwA_Ow D w := by
    intro τ a b
    by_cases hτ : τ = τ₀
    · simp only [N, if_pos hτ]
      exact bwG_change_mem D u w hw τ hB₁' hB' a b
    · simp only [N, if_neg hτ]
      exact bwG_change_mem D u w hw τ hB₁ hB a b
  have hN' : ∀ τ a b, N' τ a b ∈ bwA_Ow D w := by
    intro τ a b
    by_cases hτ : τ = τ₀
    · simp only [N', if_pos hτ]
      exact bwG_change_mem D u w hw τ hB' hB₁' a b
    · simp only [N', if_neg hτ]
      exact bwG_change_mem D u w hw τ hB hB₁ a b
  have hfac : mixF τ₀ B B' = fun τ => N τ * mixF τ₀ B₁ B₁' τ := by
    funext τ
    by_cases hτ : τ = τ₀
    · simp only [mixF, N, if_pos hτ]
      rw [← atInf_mul', show B'⁻¹ * B₁' * B₁'⁻¹ = B'⁻¹ by group]
    · simp only [mixF, N, if_neg hτ]
      rw [← atInf_mul', show B⁻¹ * B₁ * B₁⁻¹ = B⁻¹ by group]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ shiftOf (lamT u 0) τ) * subP N P,
    bwG_intSpan_allSubP D w _ N _
      (fun τ => local_GL_stabilises_lattice D w _ _ _ (N τ) (N' τ) (hmul τ) (hN τ) (hN' τ)) P hP, fun y => ?_⟩
  rw [hfac, fnOf_mul]

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Classical

variable {D : D7} {u : D.what₂.Word}

theorem onto_Bw (hRC : RatInC D u) (hRG : RatGL D u) (T : Forms0 D u) (hA : admS D u) (w : D.what₂.places.Pl)
    (hw : OverT D u w) (hs : (D.fm u).seenP w = true) (v : (D.mem u).A.vT)
    (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (hB' : ∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c)) :
    (Submodule.pi Set.univ fun c =>
      ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))) ≤ ((D.fm u).Bw 0 w v).map (crdL T B w) := by
  intro y hy
  have hy' := fun c => hy c (Set.mem_univ c)
  choose q hq hqy using hy'
  choose Q hQ hQq using hq
  have hQI : ∀ c, Q c ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0) := fun c => mem_intSubm w _ _ (hQ c)
  let γ : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.host.E := fun c τ =>
    if τ = (D.fm u).tauOf w v then (B' c)⁻¹ * B c else 1
  have hγ : ∀ c, (fun τ => atInf (Formalism.L2.Forms.embT D) ((γ c τ : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) = bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) := by
    intro c
    funext τ
    simp only [γ]
    unfold bwA_N
    split_ifs
    · rfl
    · simp [atInf]
  have ho : ∀ c τ, τ ≠ (D.fm u).tauOf w v → bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ = 1 := by
    intro c τ h
    unfold bwA_N
    rw [if_neg h]
  have hprod : ∀ c, ∏ τ, (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ).det ^ shiftOf (lamT u 0) τ =
      (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
        ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift := by
    intro c
    rw [Fintype.prod_eq_single ((D.fm u).tauOf w v) (fun τ h => by rw [ho c τ h, Matrix.det_one, one_zpow]), lamT_zero]
    rfl
  have hyc : ∀ c, y c = MvPolynomial.C (∏ τ, (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ).det ^ shiftOf (lamT u 0) τ) *
      Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c)) (Q c) := by
    intro c
    rw [hprod c, MvPolynomial.C_mul', ← hqy c, ← hQq c]
    rfl
  have hyR : ∀ c, y c ∈ RatSpan D ((D.fm u).lam 0) := by
    intro c
    have h := hRG (γ c) (Q c) (intSpan_le_rat w _ (hQI c))
    have hpt : ∀ τ, atInf (Formalism.L2.Forms.embT D) ((γ c τ : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ = bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ :=
      fun τ => congrFun (hγ c) τ
    simp only [hpt] at h
    rw [hyc c]
    exact h
  obtain ⟨x, hx⟩ := crd_surj T hA B y fun c =>
    ⟨_, hRG (fun _ => (B c)⁻¹) _ (hyR c), hRC _ (hRG (fun _ => (B c)⁻¹) _ (hyR c)), fun z => fnOf_frame (B c) (y c) z⟩
  refine ⟨x, (T.bw0 w hw hs v x).2 fun c B₁ B₁' hB₁ hB₁' => ?_, funext fun c => crd_eq T B (hx c)⟩
  obtain ⟨P₁, hP₁, he⟩ := mixed_change w hw ((D.fm u).tauOf w v) (hB c) hB₁ (hB' c) hB₁' (Q c) (hQI c)
  refine ⟨P₁, hP₁, fun z => ?_⟩
  rw [hx c z, hyc c, ← fnOf_mul, bwA_N_mul]
  exact he _

theorem ontoAll_of (hRC : RatInC D u) (hRG : RatGL D u) : OntoAll D u :=
  fun T hA w hw hs v _ B B' hB hB' => ⟨onto_Bw hRC hRG T hA w hw hs v B B' hB hB', onto_tL hRC hRG T hA w hw B hB _⟩

theorem second_branch_of_rationality (hRC : ∀ (D : D7) (u : D.what₂.Word), RatInC D u) (hRG : ∀ (D : D7) (u : D.what₂.Word), RatGL D u) :
    ∀ (D : D7) (u : D.what₂.Word), Formalism.MainNotions.RT.SecondBranchIntegralityUnderForms D u :=
  second_branch_of_surjectivity (fun D u => ontoAll_of (hRC D u) (hRG D u)) duCount_holds

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

section
namespace Formalism.L2.GlobalTheoryTheory.LemB

theorem second_branch_all_members : ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word), Formalism.MainNotions.RT.SecondBranchIntegralityUnderForms D u :=
  second_branch_of_rationality ratInC_holds ratGL_holds

end Formalism.L2.GlobalTheoryTheory.LemB
end
