import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLPlanAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterLiftOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert
import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmpCofLPd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.XFibreOfParts

section
namespace Formalism.FourierDecayAlt.TL

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

theorem wordLiftOfParts : WordLiftOfParts := by
  intro hstep hlet A S _ _ _ _ _ _ r n L st Lf w hA hL hn
  induction w with
  | nil =>
    intro _ e
    have h1 : ((ofWord L st ([] : List (Letter ℂ S))).F * bTA L ([] : List (Letter ℂ S))) = 1 := by
      simp [ofWord, bTA, bT, Start.frame]
    rw [h1, Matrix.one_apply]
    split_ifs
    · simpa using hL.one
    · exact hL.zero _ _
  | cons l w ih =>
    intro hw e
    have hw' : admitted st w := by
      obtain ⟨h1, h2, h3, h4⟩ := hw
      refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'),
        fun l' hl' => h3 l' (List.mem_cons_of_mem _ hl'), h4.of_cons⟩
      simp only [List.map_cons, List.nodup_cons] at h1
      exact h1.2
    rw [hstep A S r L st l w hA hw e, Matrix.mul_apply]
    refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
    intro f _
    have hcoef : Lf n (9 * (r + 1) * n) ((∑ i : Fin 2, eU l.intersection_update_fsHerm_neg_one i 0 * letterCol L st l w i : SlopeTestRemainingChoices S A) e f) := by
      rw [Matrix.sum_apply]
      refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
      intro i _
      rw [Matrix.mul_apply]
      refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
      intro g _
      simp only [eU, Matrix.of_apply]
      split_ifs
      · rw [one_mul]
        exact hlet A S r n L st Lf l w hA hL hn hw i g f
      · rw [zero_mul]
        exact hL.zero _ _
    refine hL.mono ?_ ?_ (hL.mul hcoef (ih hw' f))
    · simp only [List.length_cons]
      exact le_of_eq (by ring)
    · simp only [List.length_cons]
      exact le_of_eq (by ring)

end Formalism.FourierDecayAlt.TL

example {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] (st : Formalism.FourierDecayAlt.Fr.Start A)
    (X φ τ α β γ : Formalism.FourierDecayAlt.Wd.SlopeTestRemainingChoices S A) (h1 : Formalism.FourierDecayAlt.TL.kMat st α) (h2 : Formalism.FourierDecayAlt.TL.kMat st β) (h3 : Formalism.FourierDecayAlt.TL.kMat st γ) :
    Matrix.of (fun i j => ∑ k, α i k * ((X * β - β * X) * γ) k j) ∈ Formalism.FourierDecayAlt.TL.dSpan st X φ τ :=
  Submodule.subset_span (Or.inl ⟨α, β, γ, h1, h2, h3, by rw [Matrix.mul_assoc]; rfl⟩)
end

section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

theorem identity_operator : TL.IdOp := by
  intro k r Wp Wq _ _ _ _ _ Bs
  let T : B.DTerm k r Wp Wq :=
    { coef := fun _ => 1
      coefAdj := fun _ => 1
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun _ _ _ => rfl }
  have hap : ∀ F, B.opApply [T] F = F := by
    intro F
    funext g
    simp [B.opApply, B.Rw, T]
  refine ⟨[T], ⟨?_, ?_, ?_⟩, hap⟩
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨?_, ?_⟩ <;> intro g₀ _ <;>
      refine ⟨Set.univ, fun _ => 1, ?_, Set.mem_univ _, ?_, fun _ _ _ => rfl⟩
    all_goals
      first
      | exact isOpen_univ
      | exact contDiffOn_const
      | (open scoped Formalism.FourierDecayAlt.B in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Elementwise in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Operator in exact contDiffOn_const)
      | exact @contDiffOn_const _ _ _ _ _ _ _ _ _ _ _ _
  · intro p _ f _ g _
    simp only [hap]
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨fun _ => 1, 0, 0, 0, [], ⟨1, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp
    · intro g
      simp
    · intro l _ _
      simp
    · simp [T]
    · simp
    · intro g _
      simp [C6.monoM, C6.Epart, T]

end

end Formalism.FourierDecayAlt.P
end

section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

noncomputable section

theorem lift_of_x_of_parts : TL.LiftXOfParts := by
  intro hZ _hC hX Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hD Y
  obtain ⟨_, _, hAct, hQQ, _, _, _, hLS⟩ := hD
  obtain ⟨B0, _, hB⟩ := hX Wp Wq P Bs X
  obtain ⟨hFB, hEq, hRad⟩ := hB Y
  set E := xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2) with hE
  set s : ℂ := M.sgn P l0 with hs
  have hx : st.x Y = L.GGi * st.QQ Y 1 1 := by
    rw [hLS.tau, ← mul_assoc, L.GGi_GG, one_mul]
  have hx1 : (st.x Y).1 = X.fn 5 * (s • X.t Y 1 1) := by
    rw [hx, hQQ Y, hAct.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  refine hZ Wp Wq P Bs 0 0 0 0 (fun _ => s) E (st.x Y) ?_ hFB ?_ ?_
  · refine ⟨MvPolynomial.C s, by simp, fun g => by simp⟩
  · intro p hp g hg J
    simp only [pow_zero, mul_one, smul_apply]
    rw [hEq p hp g hg J, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro Φ x hx'
    simp only [pow_zero, mul_one, smul_apply]
    rw [hx1, Module.End.mul_apply, X.fn_apply 5 _ x hx', LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
      Pi.smul_apply, hRad Φ x hx', smul_smul, smul_smul]
    have hG : (0 : ℝ) < Q.GGl P.k P.r Bs.z Bs.z' x.2 := hx'.2.2
    simp only [Q.fnVal]
    congr 1
    have hG' : ((Q.GGl P.k P.r Bs.z Bs.z' x.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    field_simp

end

end Formalism.FourierDecayAlt.P
end

section
namespace Formalism.FourierDecayAlt.P.TLC

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ}

lemma om_herm_add (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v w u : Fin (2 * r + k + 1) → ℂ) :
    herm H (v + w) u = herm H v u + herm H w u := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

lemma om_herm_smul (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : ℂ) (v u : Fin (2 * r + k + 1) → ℂ) :
    herm H (c • v) u = c * herm H v u := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma om_herm_sum {ι : Type*} (s : Finset ι) (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (v : ι → Fin (2 * r + k + 1) → ℂ) (u : Fin (2 * r + k + 1) → ℂ) :
    herm H (∑ i ∈ s, v i) u = ∑ i ∈ s, herm H (v i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, om_herm_add, ih]

lemma om_herm_smul_right (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : ℂ) (v u : Fin (2 * r + k + 1) → ℂ) :
    herm H v (c • u) = conj c * herm H v u := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def]

lemma om_herm_sum_right {ι : Type*} (s : Finset ι) (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (v : Fin (2 * r + k + 1) → ℂ) (u : ι → Fin (2 * r + k + 1) → ℂ) :
    herm H v (∑ i ∈ s, u i) = ∑ i ∈ s, herm H v (u i) := by
  simp only [herm, star_sum, sum_dotProduct]

lemma om_inv_eq {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r = g⁻¹ := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  symm
  apply Matrix.inv_eq_left_inv
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hH]

private lemma herm_swap_eq_zero_of_eq_zero (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) w v = conj (herm (Hpk k r) v w) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  unfold herm
  rw [← Complex.star_def, ← star_dotProduct_star, star_star, Matrix.star_mulVec, hH,
    ← Matrix.dotProduct_mulVec]

lemma om_N3xM_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : HermitianLatticeCounting.ExpansionTerms.formalDeterminantVectorOnGroup k r Bs.z Bs.z' g = g⁻¹ *ᵥ D.cofL Bs g := by
  have hd : IsUnit g.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg
  have hZ : ∀ a b, herm (Hpk k r) (g⁻¹ *ᵥ fvec k r Bs.z a) (fvec k r Bs.z' b) =
      starRingEnd ℂ (Zhat k r Bs.z Bs.z' g a b) := by
    intro a b
    rw [← Formalism.FourierDecayAlt.P.Qx2.herm_uh hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec,
      herm_swap_eq_zero_of_eq_zero]
    rfl
  have hM : (Matrix.of fun a b => herm (Hpk k r) (g⁻¹ *ᵥ fvec k r Bs.z a) (fvec k r Bs.z' b)) =
      (Zhat k r Bs.z Bs.z' g).map (starRingEnd ℂ) := by
    ext a b
    simp [hZ]
  unfold HermitianLatticeCounting.ExpansionTerms.formalDeterminantVectorOnGroup D.cofL
  rw [hM, show ((Zhat k r Bs.z Bs.z' g).map (starRingEnd ℂ)).adjugate =
      (Zhat k r Bs.z Bs.z' g).adjugate.map (starRingEnd ℂ) from
      (RingHom.map_adjugate (starRingEnd ℂ) _).symm, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mulVec_smul]
  rfl

lemma om_herm_wb_zero {v w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w)
    (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → v i = 0) : herm (Hpk k r) v w = 0 := by
  unfold herm
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · have : (Hpk k r *ᵥ v) i = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
      · simp [hv j hj.1 hj.2]
      · have : Hpk k r i j = 0 := by
          unfold Hpk
          have hij : i ≠ j := fun h => hj (h ▸ hi)
          split_ifs <;> first | rfl | omega | exact absurd ‹_› (by tauto)
        simp [this]
    simp [this]
  · have : w i = 0 := hw i (by omega)
    simp [this]

lemma om_fvec_wb_zero (z' : Fin (2 * r + k + 1) → ℂ) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w)
    (hz'w : herm (Hpk k r) w z' = 0) (b : Fin (r + 1)) : herm (Hpk k r) (fvec k r z' b) w = 0 := by
  unfold fvec
  split_ifs with hb
  · apply om_herm_wb_zero hw
    intro i hi1 _
    simp only [bvec, eI, Pi.single_apply]
    rw [if_neg]
    intro h
    rw [h] at hi1
    simp at hi1
    omega
  · rw [herm_swap_eq_zero_of_eq_zero, hz'w, map_zero]

lemma om_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (j : Fin k) :
    omC Bs B0 g j = herm (Hpk k r) (HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g) (B0 j) := by
  show herm (Hpk k r) ((Hpk k r * gᴴ * Hpk k r) *ᵥ D.cofL Bs g) (B0 j) = _
  rw [om_inv_eq hg, ← om_N3xM_eq Bs hg]
  obtain ⟨-, -, co, hco⟩ := HermitianLatticeCounting.P.omega_decomposition k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem
    Bs.T'_pos.ne' g hg
  have h0 : ∀ b, herm (Hpk k r) (co b • fvec k r Bs.z' b) (B0 j) = 0 := fun b => by
    rw [om_herm_smul, om_fvec_wb_zero Bs.z' (hB.1 j) (hB.2.2 j Bs.z' (by simp)) b, mul_zero]
  rw [hco, om_herm_add, om_herm_sum]
  simp [h0]

lemma om_complete {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z'] B0) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : inWb k r v) (hvz : herm (Hpk k r) v z' = 0) : ∑ j, herm (Hpk k r) v (B0 j) • B0 j = v := by
  classical
  let e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ := fun i => if h : i.val < k then B0 ⟨i.val, h⟩ else z'
  have he_wb : ∀ i, inWb k r (e i) := by
    intro i
    simp only [e]
    split_ifs
    exacts [hB.1 _, hz']
  have hzz : herm (Hpk k r) z' z' ≠ 0 := by
    intro h0
    simp [Tz, h0] at hT'
  have horth : ∀ i j, i ≠ j → herm (Hpk k r) (e i) (e j) = 0 := by
    intro i j hij
    simp only [e]
    split_ifs with hi hj hj
    · rw [hB.2.1, if_neg]
      intro h
      exact hij (Fin.ext (by simpa using congrArg Fin.val h))
    · exact hB.2.2 _ z' (by simp)
    · rw [herm_swap_eq_zero_of_eq_zero, hB.2.2 _ z' (by simp), map_zero]
    · have := i.isLt
      have := j.isLt
      exact absurd (Fin.ext (by omega)) hij
  have hn : ∀ i, herm (Hpk k r) (e i) (e i) ≠ 0 := by
    intro i
    simp only [e]
    split_ifs
    · rw [hB.2.1, if_pos rfl]
      exact one_ne_zero
    · exact hzz
  have key : ∀ (b : Fin (k + 1) → ℂ) (j : Fin (k + 1)),
      herm (Hpk k r) (∑ i, b i • e i) (e j) = b j * herm (Hpk k r) (e j) (e j) := by
    intro b j
    rw [om_herm_sum, Finset.sum_eq_single j]
    · rw [om_herm_smul]
    · intro i _ hij
      rw [om_herm_smul, horth i j hij, mul_zero]
    · simp
  have mid : ∀ u : Fin (2 * r + k + 1) → ℂ, inWb k r u →
      (∀ t : Fin (k + 1), u ⟨r + t.val, by omega⟩ = 0) → u = 0 := by
    intro u hu ht
    funext i
    show u i = 0
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · have h1 : u ⟨r + (i.val - r), by omega⟩ = 0 := ht ⟨i.val - r, by omega⟩
      have e1 : (⟨r + (i.val - r), by omega⟩ : Fin (2 * r + k + 1)) = i := Fin.ext (by simp; omega)
      rwa [e1] at h1
    · exact hu i (by omega)
  have sum_wb : ∀ b : Fin (k + 1) → ℂ, inWb k r (∑ i, b i • e i) := by
    intro b i hi
    simp [Finset.sum_apply, he_wb _ i hi]
  let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.of fun t i => e i ⟨r + t.val, by omega⟩
  have hA : ∀ b t, (A *ᵥ b) t = (∑ i, b i • e i) ⟨r + t.val, by omega⟩ := by
    intro b t
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinj : Function.Injective A.mulVec := by
    intro b1 b2 h12
    have h0 : A *ᵥ (b1 - b2) = 0 := by rw [Matrix.mulVec_sub, h12, sub_self]
    have hu : ∑ i, (b1 - b2) i • e i = 0 :=
      mid _ (sum_wb _) (fun t => by rw [← hA, h0]; rfl)
    funext j
    have h1 := key (b1 - b2) j
    have h00 : herm (Hpk k r) 0 (e j) = 0 := by simp [herm]
    rw [hu, h00] at h1
    have h2 := (mul_eq_zero.mp h1.symm).resolve_right (hn j)
    simpa [sub_eq_zero] using h2
  have hsurj : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hsub : ∀ x y u, herm (Hpk k r) (x - y) u = herm (Hpk k r) x u - herm (Hpk k r) y u := by
    intro x y u
    simp only [herm, Matrix.mulVec_sub, dotProduct_sub]
  set w := v - ∑ j, herm (Hpk k r) v (B0 j) • B0 j with hw
  have hwwb : inWb k r w := by
    intro i hi
    simp [hw, Finset.sum_apply, hv i hi, (hB.1 _) i hi]
  have hwe : ∀ j, herm (Hpk k r) w (e j) = 0 := by
    intro j
    rw [hw, hsub, om_herm_sum]
    simp only [om_herm_smul]
    simp only [e]
    split_ifs with hj
    · simp [hB.2.1]
    · simp [hB.2.2 _ z' (by simp), hvz]
  obtain ⟨b, hb⟩ := hsurj (fun t => w ⟨r + t.val, by omega⟩)
  have huw : ∑ i, b i • e i = w := by
    have h1 := mid (∑ i, b i • e i - w)
      (fun i hi => by rw [Pi.sub_apply, sum_wb b i hi, hwwb i hi, sub_zero])
      (fun t => by
        have h2 := hA b t
        rw [hb] at h2
        rw [Pi.sub_apply, ← h2, sub_self])
    exact sub_eq_zero.mp h1
  have hb0 : ∀ j, b j = 0 := by
    intro j
    have h1 := key b j
    rw [huw, hwe] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (hn j)
  have hw0 : w = 0 := by
    rw [← huw]
    simp [hb0]
  rw [hw, sub_eq_zero] at hw0
  exact hw0.symm

lemma om_N3om_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) :
    inWb k r (HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g) ∧ herm (Hpk k r) (HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g) Bs.z' = 0 := by
  obtain ⟨h1, h2, -⟩ := HermitianLatticeCounting.P.omega_decomposition k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem
    Bs.T'_pos.ne' g hg
  refine ⟨h1, ?_⟩
  simpa [fvec] using h2 (Fin.last r)

lemma om_expand {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : ∑ j, omC Bs B0 g j • B0 j = HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g := by
  simp_rw [om_eq Bs hB hg]
  exact om_complete Bs.z'_mem Bs.T'_pos hB (om_N3om_mem Bs hg).1 (om_N3om_mem Bs hg).2

theorem om_norm {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : C6.sq2 (omC Bs B0 g) = Gf k r Bs.z Bs.z' g / Tz k r Bs.z' := by
  have hm := (HermitianLatticeCounting.P.dual_vector_norm_on_group k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem Bs.T'_pos g hg).1
  rw [← om_expand Bs hB hg] at hm
  simp only [om_herm_sum, om_herm_smul, om_herm_sum_right, om_herm_smul_right, hB.2.1,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hm
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at hm
  apply Complex.ofReal_injective
  rw [← hm]
  simp only [C6.sq2, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]

theorem om_equiv {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) (p : B.SS k r) (hp : Bs.inSS p)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    ∑ j, omC Bs B0 (B.sgs p g) j • B0 j = (Matrix.of p.2.1)⁻¹ *ᵥ ∑ j, omC Bs B0 g j • B0 j := by
  obtain ⟨hA, hN1, hD, hN2⟩ := hp
  have hA' := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hA
  have hN1' := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hN1
  have hsg : B.sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) *
      Matrix.of p.2.1 := by
    simp only [B.sgs, Matrix.mul_assoc]
  have hm : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hN1'.1 hg) hN2.1
  have hsU : B.sgs p g ∈ UH (Hpk k r) := by
    rw [hsg]
    exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hA'.1 hm) hD.1
  rw [om_expand Bs hB hsU, om_expand Bs hB hg, hsg,
    HermitianLatticeCounting.P.dual_vector_equivariant k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem _ hm _ hA' _ hD,
    HermitianLatticeCounting.P.dual_vector_unipotent_invariant k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem g hg _ hN1' _ hN2]

def OmPolyP : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ),
    Q.IsFrameOf k r [Bs.z'] B0 → ∀ j, U.IsPolyDeg (r + 1) fun g => omC Bs B0 g j

def OmCellP : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ),
    Q.IsFrameOf k r [Bs.z'] B0 → ∀ x ∈ Q.DomR k r Bs.z Bs.z', ∀ j, omC Bs B0 (Q.wCell k r (Fin.last r) x.1 * x.2) j =
      conj (∏ a, x.1 a) * herm (Hpk k r) (x.2⁻¹ *ᵥ Bs.z) (B0 j)

theorem om_facts_of (h1 : OmPolyP) (h4 : OmCellP) : OmFacts := by
  intro k r Wp Wq _ _ _ _ _ Bs B0 hB
  exact ⟨h1 k r Wp Wq Bs B0 hB, fun g hg => om_norm Bs hB hg,
    fun p hp g hg => om_equiv Bs hB p hp hg.1, h4 k r Wp Wq Bs B0 hB⟩

lemma om_prod_erase (r : ℕ) (c : Fin r → ℂ) (ζ : ℂ) :
    ∏ j ∈ Finset.univ.erase (Fin.last r), (if h : j.val < r then c ⟨j.val, h⟩ else ζ) = ∏ a, c a := by
  rw [← Finset.compl_singleton, ← Fin.image_castSucc, Finset.prod_image (fun a _ b _ h => Fin.castSucc_injective _ h)]
  simp

lemma inv_mulVec_of_fixed_vector {n : ℕ} (W M : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) (hM : IsUnit M.det)
    (hG : IsUnit (W * M).det) (hW : W *ᵥ z = z) : (W * M)⁻¹ *ᵥ z = M⁻¹ *ᵥ z := by
  have hWd : IsUnit W.det := by
    rw [Matrix.det_mul] at hG
    exact isUnit_of_mul_isUnit_left hG
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  congr 1
  conv_lhs => rw [← hW]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hWd, Matrix.one_mulVec]

theorem om_cell {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (x : (Fin r → ℂ) × Q.Mx k r) (hx : x ∈ Q.DomR k r Bs.z Bs.z') (j : Fin k) :
    omC Bs B0 (Q.wCell k r (Fin.last r) x.1 * x.2) j = conj (∏ a, x.1 a) * herm (Hpk k r) (x.2⁻¹ *ᵥ Bs.z) (B0 j) := by
  obtain ⟨hc, hM, -⟩ := hx
  have hWU : bigCell k r x.1 1 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.big_cell_mem_holds k r x.1 1 hc (by simp)
  have hgU : bigCell k r x.1 1 * x.2 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hWU hM.1
  have hfix : ∀ b, (bigCell k r x.1 1 * x.2) *ᵥ fvec k r Bs.z' b =
      bigCell k r x.1 1 *ᵥ fvec k r (x.2 *ᵥ Bs.z') b := by
    intro b
    rw [← Matrix.mulVec_mulVec]
    congr 1
    unfold fvec
    split_ifs with hb
    · exact (hM.2 ⟨b.val, hb⟩ (by simp only [Fin.val_last]; exact hb)).1
    · rfl
  have hZ : Zhat k r Bs.z Bs.z' (bigCell k r x.1 1 * x.2) = Zhat k r Bs.z (x.2 *ᵥ Bs.z') (bigCell k r x.1 1) := by
    ext a b
    simp only [Zhat, hfix]
  have hMz' := (Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb hM Bs.z'_mem).1
  rw [Formalism.QuantumDeterminants.big_cell_coordinate_holds k r _ _ x.1 1 Bs.z_mem hMz'] at hZ
  have hcof : D.cofL Bs (bigCell k r x.1 1 * x.2) = conj (∏ a, x.1 a) • Bs.z := by
    unfold D.cofL
    rw [hZ, Matrix.adjugate_diagonal, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.diagonal_apply_eq, om_prod_erase]
      congr 1
      simp [fvec]
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), map_zero, zero_smul]
    · simp
  have hWz : bigCell k r x.1 1 *ᵥ Bs.z = Bs.z := by
    rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV, Matrix.one_mulVec]
  rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
  show herm (Hpk k r) ((Hpk k r * (bigCell k r x.1 1 * x.2)ᴴ * Hpk k r) *ᵥ
    D.cofL Bs (bigCell k r x.1 1 * x.2)) (B0 j) = _
  rw [om_inv_eq hgU, hcof, Matrix.mulVec_smul, om_herm_smul,
    inv_mulVec_of_fixed_vector _ _ _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hM.1) (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hgU) hWz]

end

end Formalism.FourierDecayAlt.P.TLC

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.TLC

theorem omega_polynomial_facts : TL.OmFacts := by
  exact om_facts_of (fun k r Wp Wq _ _ _ _ _ Bs B0 _ j => omp_poly Bs B0 j)
    (fun k r Wp Wq _ _ _ _ _ Bs B0 _ x hx j => om_cell Bs x hx j)

end Formalism.FourierDecayAlt.P
end

section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

namespace TLC

variable {k r : ℕ}

theorem cap_econj {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsRepW k r z π) {Bs Bs' : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs)
    (hB' : IsFrameOf k r [z] Bs') :
    (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) * (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c)) = 1 ∧
    (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c)) * (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) = 1 ∧
    EB π Bs = Econj (EB π Bs') (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c))
      (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) := by
  set P : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c) with hP
  set Q : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b) with hQ
  have hexp : ∀ a, Bs a = ∑ c, P c a • Bs' c := by
    intro a
    exact HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB' (hB.1 a) (hB.2.2 a z (by simp))
  have hQP : Q * P = 1 := by
    ext b a
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : herm (Hpk k r) (Bs a) (Bs b) = herm (Hpk k r) (∑ c, P c a • Bs' c) (Bs b) := by
      rw [← hexp a]
    rw [HermitianFormSums.herm_lsum, hB.2.1] at h1
    rw [show (if b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 by simp only [eq_comm], h1]
    apply Finset.sum_congr rfl
    intro c _
    simp only [hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have hunit : ∀ a b, unitB (Hpk k r) Bs a b =
      ∑ x ∈ (Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin k)),
        (P x.1 a * Q b x.2) • unitB (Hpk k r) Bs' x.1 x.2 := by
    intro a b
    rw [Finset.sum_product]
    ext p q
    have h1 : Bs a p = ∑ c, P c a * Bs' c p := by
      have := congrFun (hexp a) p
      rw [Finset.sum_apply] at this
      exact this
    have h2 : herm (Hpk k r) (bvec q) (Bs b) = ∑ d, Q b d * herm (Hpk k r) (bvec q) (Bs' d) := by
      have h3 : herm (Hpk k r) (bvec q) (Bs b) = herm (Hpk k r) (bvec q) (∑ d, P d b • Bs' d) := by
        rw [← hexp b]
      rw [h3, HermitianFormSums.herm_rsum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [hP, hQ, Matrix.of_apply, Qx2.herm_star]
    simp only [Matrix.sum_apply, Matrix.smul_apply, unitB, Matrix.of_apply, smul_eq_mul]
    rw [h1, h2, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  refine ⟨hQP, hPQ, ?_⟩
  funext a b
  unfold EB Econj
  rw [hunit a b, (HermitianFormSums.ec_sum elementary_lie_elements hπ _ _ (fun x : Fin k × Fin k => unitB (Hpk k r) Bs' x.1 x.2)
    (fun x => QrD.frame_lie hB' x.1 x.2) _ (QrD.frame_lie hB' a a)).2, Finset.sum_product]
  ext v
  simp

theorem cap_vec {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} {z' : Fin (2 * r + k + 1) → ℂ}
    (hB0 : IsFrameOf k r [z'] B0) {ν : Fin k → ℂ} (hν : C6.sq2 ν = 1) :
    inWb k r (∑ j, ν j • B0 j) ∧ herm (Hpk k r) (∑ j, ν j • B0 j) z' = 0 ∧
      herm (Hpk k r) (∑ j, ν j • B0 j) (∑ j, ν j • B0 j) = 1 := by
  refine ⟨HermitianFormSums.inWb_sum _ _ _ hB0.1, ?_, ?_⟩
  · rw [HermitianFormSums.herm_lsum]
    exact Finset.sum_eq_zero fun j _ => by rw [hB0.2.2 j z' (by simp), mul_zero]
  · rw [HermitianFormSums.herm_comb hB0]
    have : ∀ a, ν a * star (ν a) = ((Complex.normSq (ν a) : ℝ) : ℂ) := fun a => Complex.mul_conj (ν a)
    simp only [this]
    rw [← Complex.ofReal_sum]
    unfold C6.sq2 at hν
    rw [hν, Complex.ofReal_one]

end TLC

open TLC in
theorem capelli_vector_frame : TL.CapVFrame := by
  intro Wq _ _ _ k r z' π' B0 Bs ν hk hz hT hπ hB0 hν hBs w v
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨he, hez, hee⟩ := cap_vec hB0 hν
  set e := ∑ j, ν j • B0 j with hedef
  have hBs1 := HermitianFormSums.frame_sub hBs
  set C : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs e with hCdef
  have hCc : ∀ a : Fin n, C a.castSucc = Bs a := fun a => by rw [hCdef, Fin.snoc_castSucc]
  have hCl : C (Fin.last n) = e := by rw [hCdef, Fin.snoc_last]
  have hBe : ∀ a, herm (Hpk (n + 1) r) (Bs a) e = 0 := fun a => hBs.2.2 a e (by simp)
  have heB : ∀ a, herm (Hpk (n + 1) r) e (Bs a) = 0 := fun a => by
    rw [← Qx2.herm_star, hBe, star_zero]
  have hC : IsFrameOf (n + 1) r [z'] C := by
    refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [hCl]; exact he
      · rw [hCc]; exact hBs.1 a
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · refine Fin.lastCases ?_ (fun b => ?_) b
        · rw [hCl, hee, if_pos rfl]
        · rw [hCl, hCc, heB, if_neg (Fin.castSucc_lt_last b).ne']
      · refine Fin.lastCases ?_ (fun b => ?_) b
        · rw [hCl, hCc, hBe, if_neg (Fin.castSucc_lt_last a).ne]
        · rw [hCc, hCc, hBs.2.1]
          simp only [Fin.castSucc_inj]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [hCl]; exact hez
      · rw [hCc]; exact hBs.2.2 a v (by simp)
  obtain ⟨hQP, hPQ, hEB⟩ := cap_econj hz hT hπ hC hB0
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun c a => herm (Hpk (n + 1) r) (C a) (B0 c) with hP
  set Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun b d => herm (Hpk (n + 1) r) (B0 d) (C b) with hQ
  have hcol : (fun p => P p (Fin.last n)) = ν := by
    funext p
    simp only [hP, Matrix.of_apply, hCl, hedef, HermitianFormSums.herm_lsum, hB0.2.1, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hβ : ∀ j, (star ν ᵥ* P) j = if j = Fin.last n then 1 else 0 := by
    intro j
    have h1 : (star ν ᵥ* P) j = herm (Hpk (n + 1) r) (C j) e := by
      rw [hedef, HermitianFormSums.herm_rsum]
      simp only [Matrix.vecMul, dotProduct, hP, Matrix.of_apply, Pi.star_apply]
    rw [h1, ← hCl, hC.2.1, eq_comm]
  have hGl := (frame_general_linear Wq (n + 1) r (n + 1) z' π' B0 hπ hB0).1
  have key := AnisotropicColumnSums.chat_gen (n + 1) n rfl (Module.End ℂ Wq) (EB π' B0) P Q (Fin.last n) (by simp) Fin.castSucc
    (fun a => rfl) hGl hQP hPQ w (star ν) (fun j hj => by rw [hβ j, if_neg hj])
  rw [hcol, hβ, if_pos rfl, one_smul, ← hEB, ← BorderedDeterminants.qdet_sub] at key
  have hsub : subA (EB π' C) = EB π' Bs := by
    funext a b
    simp only [subA, EB, unitB, hCc]
  rw [hsub] at key
  have hcap := (frame_general_linear Wq (n + 1) r n z' π' Bs hπ hBs1).2 w v
  rw [hcap, ← key]
  rfl

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

open TLC in
theorem capelli_vector_equivariance : TL.CapVEquiv := by
  intro Wq _ _ _ k r z' π' B0 ν ν' h hk hz hT hπ hB0 hν hh hνν' w
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨he, hez, hee⟩ := cap_vec hB0 hν
  set e := ∑ j, ν j • B0 j with hedef
  set g := h⁻¹ with hgdef
  have hg : g ∈ UWset (n + 1) r z' := LieBracketMultiplication.uw_inv hh
  have hgU : g ∈ UH (Hpk (n + 1) r) := hg.1
  have hgL : g ∈ Glev (n + 1) r (Fin.last r) := Qx8.uw_glev _ hg
  have hν' : C6.sq2 ν' = 1 := by
    have h1 : herm (Hpk (n + 1) r) (∑ j, ν' j • B0 j) (∑ j, ν' j • B0 j) = 1 := by
      rw [hνν', Qx2.herm_uh hgU, hee]
    rw [HermitianFormSums.herm_comb hB0] at h1
    have : ∀ a, ν' a * star (ν' a) = ((Complex.normSq (ν' a) : ℝ) : ℂ) := fun a => Complex.mul_conj (ν' a)
    simp only [this] at h1
    rw [← Complex.ofReal_sum] at h1
    exact_mod_cast h1
  obtain ⟨Bs, hBs⟩ := exists_frame_two n r z' e hz hT he hez hee
  set Bs' : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ := fun a => g *ᵥ Bs a with hBs'def
  have hBs' : IsFrameOf (n + 1) r [z', ∑ j, ν' j • B0 j] Bs' := by
    refine ⟨fun a => Qx8.inWb_mulVec hgL (hBs.1 a), fun a b => ?_, fun a v hv => ?_⟩
    · rw [hBs'def, Qx2.herm_uh hgU]; exact hBs.2.1 a b
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · have e1 := Qx2.herm_uh hgU (Bs a) v
        rw [hg.2.2] at e1
        rw [e1]; exact hBs.2.2 a _ (by simp)
      · rw [hνν', Qx2.herm_uh hgU]; exact hBs.2.2 a _ (by simp)
  have hF := capelli_vector_frame Wq (n + 1) r z' π' B0 Bs ν (by omega) hz hT hπ hB0 hν hBs w
  have hF' := capelli_vector_frame Wq (n + 1) r z' π' B0 Bs' ν' (by omega) hz hT hπ hB0 hν' hBs' w
  have hBs1 := HermitianFormSums.frame_sub hBs
  have hBs1' := HermitianFormSums.frame_sub hBs'
  have hq := (frame_general_linear Wq (n + 1) r n z' π' Bs hπ hBs1).2 w
  have hq' := (frame_general_linear Wq (n + 1) r n z' π' Bs' hπ hBs1').2 w
  have hgi : g⁻¹ = h := Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1)
  have hgh : g * h = 1 := LeftDerivativeCurves.uh_inv_mul hh.1
  have hhg : h * g = 1 := LeftDerivativeCurves.uh_mul_inv hh.1
  have hUUi : (π' g).comp (π' h) = ContinuousLinearMap.id ℂ Wq := by
    rw [← hπ.1.2 _ hg _ hh, hgh, hπ.1.1]; rfl
  have hUiU : (π' h).comp (π' g) = ContinuousLinearMap.id ℂ Wq := by
    rw [← hπ.1.2 _ hh _ hg, hhg, hπ.1.1]; rfl
  set U : Module.End ℂ Wq := (π' g : Wq →ₗ[ℂ] Wq) with hU
  set Ui : Module.End ℂ Wq := (π' h : Wq →ₗ[ℂ] Wq) with hUi
  have hUUi' : U * Ui = 1 := by
    apply LinearMap.ext; intro v
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUUi
    simpa [hU, hUi] using this
  have hUiU' : Ui * U = 1 := by
    apply LinearMap.ext; intro v
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUiU
    simpa [hU, hUi] using this
  have hEB : ∀ a b, U * EB π' Bs a b * Ui = EB π' Bs' a b := by
    intro a b
    obtain ⟨hX1, hX2⟩ := QrD.frame_lie hBs1 a b
    obtain ⟨-, -, e1⟩ := differential_operator_adjoint Wq (n + 1) r z' π' hπ _ hX1 g hg
    obtain ⟨-, -, e2⟩ := differential_operator_adjoint Wq (n + 1) r z' π' hπ _ hX2 g hg
    obtain ⟨c1, c2⟩ := Qx8.hpart_conj Bs a b hgU
    unfold EB QrD.ecOp
    rw [c1, c2, e1, e2, hgi]
    apply LinearMap.ext; intro v
    simp [hU, hUi]
  let f : Module.End ℂ Wq →+* Module.End ℂ Wq :=
    { toFun := fun T => U * T * Ui
      map_one' := by simp only [mul_one, hUUi']
      map_mul' := fun S T => by
        show U * (S * T) * Ui = U * S * Ui * (U * T * Ui)
        calc U * (S * T) * Ui = U * S * (Ui * U) * T * Ui := by rw [hUiU']; noncomm_ring
          _ = U * S * Ui * (U * T * Ui) := by noncomm_ring
      map_zero' := by simp only [mul_zero, zero_mul]
      map_add' := fun S T => by noncomm_ring }
  have hf : ∀ v, f (algebraMap ℂ (Module.End ℂ Wq) v) = algebraMap ℂ (Module.End ℂ Wq) v := by
    intro v
    show U * algebraMap ℂ (Module.End ℂ Wq) v * Ui = _
    rw [← Algebra.commutes, mul_assoc, hUUi', mul_one]
  have hqd := QuantumMinorExpansion.map_qminor (EB π' Bs') f hf (EB π' Bs) (fun a b => hEB a b) id id w
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  rw [hF', hF, hq', hq]
  unfold qdet
  rw [← hqd]
  show U (qminor (EB π' Bs) id id w (Ui (π' h⁻¹ v))) = π' h⁻¹ (qminor (EB π' Bs) id id w v)
  have : Ui (π' h⁻¹ v) = v := by
    rw [← hgdef]
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUiU
    simpa [hUi] using this
  rw [this]
  rfl

end Formalism.FourierDecayAlt.P
end
end

section
namespace Formalism.FourierDecayAlt.P

theorem lift_of_x : Formalism.FourierDecayAlt.TL.LiftX :=
  lift_of_x_of_parts lift_zero_order lift_closed_under_operations
    (x_fibre_of_parts big_cell_values omega_polynomial_facts capelli_vector_frame capelli_vector_equivariance)

set_option maxHeartbeats 400000 in

theorem top_lift_exists : Formalism.FourierDecayAlt.TL.TopLiftExists3 := by
  classical
  refine ⟨11, by norm_num, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hl1 hlk hD
  obtain ⟨hA, hcap, hxi⟩ := actual_algebra_facts Wp Wq P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 hD
  obtain ⟨hmono, hzero, hadd, hsmul, hmul⟩ := lift_closed_under_operations Wp Wq P Bs
  have hF := lift_of_functions Wp Wq P Bs X L hD.2.2.1
  have hX := lift_of_x Wp Wq P Bs X μ L st l0 hD
  have hK := lift_capelli_operators Wp Wq P Bs X μ L st l0 hD
  have hpoly : ∀ (p : Polynomial ℂ) (a : Q.Pr ↥(Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')),
      TL.Lifts P Bs 0 0 a → TL.Lifts P Bs 0 0 (Polynomial.aeval a p) := by
    intro p a ha
    have hpow : ∀ m : ℕ, TL.Lifts P Bs 0 0 (a ^ m) := by
      intro m
      induction m with
      | zero => simpa using hF.1
      | succ m ih => simpa [pow_succ] using hmul 0 0 0 0 _ _ ih ha
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa using hadd 0 0 _ _ hp hq
    | monomial m c =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact hsmul 0 0 _ c (hpow m)
  have hn : P.r + 1 ≤ 2 * P.r + P.k + 1 := by omega
  have hSys : TL.LiftSys L st (2 * P.r + P.k + 1) (TL.Lifts P Bs) :=
    { mono := fun h1 h2 h => hmono _ _ _ _ _ h1 h2 h
      zero := hzero
      add := fun h1 h2 => hadd _ _ _ _ h1 h2
      smul := fun z h => hsmul _ _ _ z h
      one := hF.1
      mul := fun h1 h2 => hmul _ _ _ _ _ _ h1 h2
      fns := hF.2
      x := fun Y _ => hX Y
      xi := fun Y hY _ => by
        obtain ⟨p, hp⟩ := hxi Y hY
        rw [hp]
        exact hpoly p _ (hX Y)
      cap := fun Y hY => by
        rw [← hcap Y hY]
        exact hK Y }
  have hWL := TL.wordLiftOfParts word_recursion
    (letter_lift_of_parts TL.basicLift l_shape m_shape_of_l_shape)
  have hAdm : ∀ w : List C.Letter, KB.CutWord P l0 w → Fr.admitted st (D.positionted w) := by
    intro w hw
    have hM : M.CutWord P l0 (D.positionted w) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [D.positionted, List.map_ofFn]
        exact List.nodup_ofFn.mpr (fun a b h => h)
      · intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact ⟨by simp, by simpa using hw.1 i⟩
      · rw [D.positionted, List.pairwise_ofFn]
        intro i j hij
        simpa using hw.2 i j (ne_of_lt hij)
    obtain ⟨h1, h2, h3, h4⟩ := cut_admissible interlacing_sign q_positive_interlacing q_positive_shift
      types_interlace realPoints_statement P hD.1.1 l0 hl1 hlk (Fin w.length) (D.positionted w) hM
    refine ⟨h1, h2, ?_, h4⟩
    rw [hD.2.2.2.2.1, hD.2.2.2.2.2.1]
    exact h3
  have hLift : ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∃ Dop : B.DiffOp P.k P.r Wp Wq,
      KB.CutWord P l0 w → ∃ (nf : ℕ) (fib : Fin nf → B.Mat P.k P.r → C6.EndH Wp Wq),
        (∀ j, C6.FibBound Bs (fib j)) ∧
        C6.InDDPlus Bs fib ∅ (w.length * (2 * P.r + P.k + 1))
          (11 * w.length * (P.r + 1) * (2 * P.r + P.k + 1)) Dop ∧
        TL.RadIs P Bs Dop (((Fr.ofWord L st (D.positionted w)).F * TL.bTA L (D.positionted w)) e Wd.e1).1 := by
    intro w e
    by_cases hw : KB.CutWord P l0 w
    · have h := hWL _ (Fin w.length) P.r (2 * P.r + P.k + 1) L st (TL.Lifts P Bs) (D.positionted w) hA hSys hn
        (hAdm w hw) e
      have hl : (D.positionted w).length = w.length := List.length_ofFn
      rw [hl] at h
      obtain ⟨nf, fib, Dop, h1, h2, h3⟩ := h
      exact ⟨Dop, fun _ => ⟨nf, fib, h1, h2, h3⟩⟩
    · obtain ⟨Dop, -⟩ := identity_operator P.k P.r Wp Wq Bs
      exact ⟨Dop, fun h => absurd h hw⟩
  choose Dw hDw using hLift
  obtain ⟨D0, hD0, hD0F⟩ := identity_operator P.k P.r Wp Wq Bs
  refine ⟨⟨fun w e F => if w = [] then F else B.opApply (Dw w e) F, fun e F => by simp⟩, ?_, ?_⟩
  · intro w hw F hFc Φ hΦ e
    dsimp only
    have hact : ∀ (M0 : Wd.SlopeTestRemainingChoices (Fin w.length) (Q.Pr ↥(Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
        P5.act M0 (Top.firstStateVector Φ) e = (M0 e Wd.e1).1 Φ := by
      intro M0
      unfold P5.act Top.firstStateVector
      rw [Finset.sum_eq_single Wd.e1]
      · exact congrArg _ (if_pos rfl)
      · intro b _ hb
        have hb' : ¬ (b = fun _ => 0) := hb
        rw [if_neg hb', map_zero]
      · simp
    rw [hact]
    by_cases hne : w = []
    · subst hne
      simp only [if_true]
      have h1 : (Fr.ofWord L st (D.positionted ([] : List C.Letter))).F * P5.bTall L (D.positionted ([] : List C.Letter)) = 1 := by
        simp [D.positionted, Fr.ofWord, P5.bTall, P5.bTl, Wd.bT, Fr.Start.frame]
      have he : e = Wd.e1 := funext fun i => (Nat.not_lt_zero _ i.2).elim
      rw [h1, he]
      simpa using hΦ
    · rw [if_neg hne]
      obtain ⟨nf, fib, -, -, hR⟩ := hDw w e hw
      exact hR F hFc Φ hΦ
  · intro w hw e
    dsimp only
    by_cases hne : w = []
    · refine ⟨0, fun j => j.elim0, 0, 0, D0, fun j => j.elim0, ?_, by norm_num <;> positivity,
        by norm_num <;> positivity, ?_⟩
      · convert hD0 using 2
      · intro F g _
        rw [if_pos hne, hD0F]
    · obtain ⟨nf, fib, h1, h2, -⟩ := hDw w e hw
      refine ⟨nf, fib, _, _, Dw w e, h1, h2, ?_, ?_, ?_⟩
      · push_cast
        nlinarith [show (0:ℝ) ≤ (w.length:ℝ) * (2 * (P.r:ℝ) + P.k + 1) by positivity]
      · push_cast
        nlinarith [show (0:ℝ) ≤ (w.length:ℝ) * (2 * (P.r:ℝ) + P.k + 1) by positivity]
      · intro F g _
        rw [if_neg hne]

end Formalism.FourierDecayAlt.P
end
