import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRModelV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRDrTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatQMinOp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapToda
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCoef
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVRules
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrpCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AlgebraSmulCommClassComplex

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Gauge Gauge.VLem

noncomputable section

section model

variable (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r)

def capaVpM (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P)) :=
  (((List.finRange P.r).take i).reverse.map fun l => L.Tvl Y l).prod

theorem capaVpM_zero (Y : ℂ) : capaVpM P L Y 0 = 1 := by
  simp [capaVpM]

theorem capaVpM_succ (Y : ℂ) (i : ℕ) (h : i < P.r) :
    capaVpM P L Y (i + 1) = L.Tvl Y ⟨i, h⟩ * capaVpM P L Y i := by
  simp [capaVpM, List.take_add_one, h]

theorem capa_tvprod (Y : ℂ) : L.Tvprod Y = capaVpM P L Y P.r := by
  simp [R.LevelData.Tvprod, capaVpM, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

theorem capa_Tvl_mul_0 (Y : ℂ) (l : Fin P.r) (V : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P))) :
    (L.Tvl Y l * V) 0 0 = (algebraMap ℂ (MA.A P (MA.DQ P)) Y - L.pb l) * V 0 0 + -L.cb l * V 1 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

theorem capa_Tvl_mul_1 (Y : ℂ) (l : Fin P.r) (V : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P))) :
    (L.Tvl Y l * V) 1 0 = L.cbi l * V 0 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

theorem capa_actA_pb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.pbA P (MA.DQ P) l) f = fun ρ => MA.eulerQ (TT := P.TT) (M.vcb l) (f ρ) := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

theorem capa_actA_cb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

theorem capa_actA_cbi (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbiA P (MA.DQ P) l) f = fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb l)) * f ρ := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

end model

section ind

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem capa_vab_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℂ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ) =
          MA.actA P (Vp P Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ) =
          MA.actA P (Vp P Y i 1 0) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ with hΦB
    have hv : Q.vAB (E := Wq →L[ℂ] Wp) P.r Y (i + 1) =
        (fun f => Y • (Q.vAB P.r Y i).1 f + pOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f) -
          cOp ⟨i, h⟩ ((Q.vAB P.r Y i).2 f), fun f => ciOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f)) := by
      simp only [Q.vAB, dif_pos h]
    have e0 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 0) Φ =
        Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA - Q.crd (cOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 1) Φ = Q.crd (ciOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 0
    have hcB : FamR P Bs Dc (Q.crd (cOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 1
    have hciA : FamR P Bs Dc (Q.crd (ciOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 2
    have hsum : FamR P Bs Dc (Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA) := famR_add (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => c ⟨i, h⟩) (fun _ _ => rfl) _ (fun q => coordE_vc _ _)
    have tci : trR P Bs.μsec e (Q.crd (ciOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (c ⟨i, h⟩)⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hsum hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hsum ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_p hpl hk he hA, tc, tA, tB, Vp_succ P Y i h, Ts_mul_0, actA_add, actA_mul, actA_mul,
        actA_neg, actA_add, actA_algebraMap, actA_p, actA_c, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, Vp_succ P Y i h, Ts_mul_1, actA_mul, actA_ci]

theorem capa_vabm_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L) (Y : ℂ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r Y i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r Y i) 0) Φ) =
          MA.actA P (capaVpM P L Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r Y i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r Y i) 1) Φ) =
          MA.actA P (capaVpM P L Y i 1 0) (trR P Bs.μsec e Φ)) := by
  obtain ⟨-, hpb, -, -, hcb, hcbi, -⟩ := hL
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (vABm P.r Y 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (vABm P.r Y 0) 1) Φ = 0 := rfl
    have v0 : capaVpM P L Y 0 0 0 = 1 := by simp [capaVpM_zero]
    have v1 : capaVpM P L Y 0 1 0 = 0 := by simp [capaVpM_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (vABm P.r Y i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (vABm P.r Y i) 1) Φ with hΦB
    have hv : vABm (X := Wq →L[ℂ] Wp) P.r Y (i + 1) =
        (fun f => Y • (vABm P.r Y i).1 f - pbOp ⟨i, h⟩ ((vABm P.r Y i).1 f) -
          cbOp ⟨i, h⟩ ((vABm P.r Y i).2 f), fun f => cbiOp ⟨i, h⟩ ((vABm P.r Y i).1 f)) := by
      simp only [vABm, dif_pos h]
    have e0 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 0) Φ =
        Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA - Q.crd (cbOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 1) Φ = Q.crd (cbiOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pbOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 3
    have hcB : FamR P Bs Dc (Q.crd (cbOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 4
    have hciA : FamR P Bs Dc (Q.crd (cbiOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 5
    have hdif : FamR P Bs Dc (Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA) := famR_sub (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cbOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vcb ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => star (c ⟨i, h⟩)) (fun _ _ => rfl) _ (fun q => coordE_vcb _ _)
    have tci : trR P Bs.μsec e (Q.crd (cbiOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (star (c ⟨i, h⟩))⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vcb]; exact (star_ne_zero).2 (hx.1 _)), coordE_vcb])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hdif hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hdif ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_sub _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_pb hpl hk he hA, tc, tA, tB, capaVpM_succ P L Y i h, capa_Tvl_mul_0, hpb, hcb, actA_add, actA_mul,
        actA_mul, actA_neg, sub_eq_add_neg ((algebraMap ℂ (MA.A P (MA.DQ P))) Y), actA_add, actA_algebraMap, actA_neg,
        capa_actA_pb, capa_actA_cb, sub_eq_add_neg, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, capaVpM_succ P L Y i h, capa_Tvl_mul_1, actA_mul, hcbi, capa_actA_cbi]

end ind

theorem capelli_transition_holds : JDAVTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he L hL Dc Φ hΦ y
  have hA := (capa_vab_ind hpl hk he y P.r le_rfl Dc Φ hΦ).1
  have hAv := (capa_vabm_ind hpl hk he L hL y P.r le_rfl Dc Φ hΦ).1
  refine ⟨⟨hA.1, ?_⟩, ⟨hAv.1, ?_⟩⟩
  · rw [hA.2, R.LevelData.Ar, ← site_vector_eq_tensor_product P L hL y 0, sitesCommonSpace_v0_eq_Vp]
  · rw [hAv.2, R.LevelData.Avr, capa_tvprod]

theorem jDCapA_of_grp (hG : JDAGrp) : JDCapA := jDCapA_of_parts hG capelli_transition_holds residue_derivative_transition

end

end Formalism.FourierDecayAlt.P.CutMP
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

theorem exists_polyOp_qminor_sum {k r t κ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι)
    (a : ι → Fin t → Fin (2 * r + k + 1)) (b : ι → Fin t → Fin (2 * r + k + 1)) (β : ι → B.Mat k r → ℂ)
    (hβ : ∀ j ∈ s, U.IsPolyDeg κ (β j)) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ ∧ B.opOrder Θ = t ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (t : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r →
        B.opApply Θ F g = ∑ j ∈ s, β j g • qminorOp (Q.EH k r) (a j) (b j) u F g := by
  have h := fun j => qminorWordSum k r t (a j) (b j) u
  choose L hL hE using h
  let Θ₁ : B.DiffOp k r Wp Wq :=
    s.toList.flatMap fun j => (L j).map fun cw => pTerm (fun g => β j g * cw.1) cw.2
  let T₀ : B.DTerm k r Wp Wq := pTerm (fun _ => 0) (List.replicate t 0)
  have hT₀ : T₀.word = List.replicate t 0 := pTerm_word (fun X hX => by
    rw [List.eq_of_mem_replicate hX]; exact inLie_zero)
  refine ⟨Θ₁ ++ [T₀], ?_, ?_, ?_⟩
  · intro Tm hTm
    rcases List.mem_append.1 hTm with h1 | h1
    · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at h1
      obtain ⟨j, hj, cw, hcw, rfl⟩ := h1
      refine ⟨(pTerm_word_le _ _).trans (hL j cw hcw).2, fun g => β j g * cw.1, ?_, fun g => rfl, fun g => rfl⟩
      have := Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul (hβ j hj) (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const cw.1 0)
      simpa using this
    · rw [List.mem_singleton] at h1
      subst h1
      refine ⟨by rw [hT₀]; simp, fun _ => 0, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 κ, fun g => rfl, fun g => rfl⟩
  · unfold B.opOrder
    apply foldr_max_eq
    · intro x hx
      simp only [List.mem_map, List.mem_append, List.mem_singleton] at hx
      obtain ⟨Tm, hTm | rfl, rfl⟩ := hx
      · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hTm
        obtain ⟨j, _, cw, hcw, rfl⟩ := hTm
        exact (pTerm_word_le _ _).trans (hL j cw hcw).2
      · rw [hT₀]; simp
    · simp only [List.mem_map, List.mem_append, List.mem_singleton]
      exact ⟨T₀, Or.inr rfl, by rw [hT₀]; simp⟩
  · intro UU F hF g hgU hg
    have hT₀a : T₀.coef g (B.Rw T₀.word F g) = 0 := by
      change ((0 : ℂ) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw T₀.word F g) = 0
      simp
    simp only [B.opApply, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hT₀a,
      add_zero, Θ₁]
    rw [sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE j _ UU F hF g hgU hg, List.map_map, ← sum_map_mul_smul]
    congr 1
    apply List.map_congr_left
    intro cw hcw
    simp only [Function.comp_apply]
    rw [pTerm_word (fun X hX => ((hL j cw hcw).1 X hX).1)]
    change ((β j g * cw.1) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw cw.2 F g) = _
    rfl

end Formalism.FourierDecayAlt.P.CutMP.QMinOp

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

noncomputable section

theorem capBeta_pd (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capBeta k r c) := by
  unfold capBeta
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a)))) fun a l => ?_
  simp only [Matrix.of_apply, herm, dotProduct, Matrix.mulVec]
  refine pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  refine pd_sum _ fun j _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun c _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul (pd_entry _ _) (pd_const _ 0))

theorem capAlphaV_pd (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capAlphaV k r B) := by
  unfold capAlphaV
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)) fun a l => ?_
  simp only [Matrix.of_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine pd_sum _ fun m _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  refine pd_sum _ fun l _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) (pd_star_entry _ _))

theorem capelli_representation_holds : JDACapRep := by
  intro k r Wp Wq _ _ _ _ _ y
  classical
  have hκ : r ≤ (r + 1) * (2 * r + k + 1) := by nlinarith
  have ho : r ≤ 2 * r + k + 1 := by omega
  obtain ⟨Θ, hP, hO, hE⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun c : Fin r → Fin (2 * r + k + 1) => StrictMono c) (fun _ => C3.xR k r r le_rfl)
    (fun c => c) (capBeta k r) (fun c _ => capBeta_pd k r c) (Q.uC k r 0 y)
  obtain ⟨Θv, hPv, hOv, hEv⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun B : Fin r → Fin (2 * r + k + 1) => StrictMono fun l => C3.keyS k r (B l)) (fun B => B)
    (fun _ => C3.sR k r r le_rfl) (capAlphaV k r) (fun B _ => capAlphaV_pd k r B)
    (y - ((2 * r + k : ℕ) : ℂ) / 2 + (r : ℂ) - 1)
  refine ⟨Θ, Θv, QMinOp.polyOp_mono hP ho hκ, QMinOp.polyOp_mono hPv ho hκ, hO, hOv, fun F g hg hF => ?_,
    fun F g hg hF => ?_⟩
  · rw [hO] at hF
    rw [hE {g} F hF g rfl hg, Finset.sum_filter]
    rfl
  · rw [hOv] at hF
    rw [hEv {g} F hF g rfl hg, Finset.sum_filter]
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hg
    simp only [capAv, C3.AAvop, capAlphaV, hinv]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem colsVm_castSucc {k r m : ℕ} (hm : m + 1 ≤ r) :
    colsVm k r (m + 1) ∘ Fin.castSucc = colsVm k r m := by
  funext j; ext; simp [colsVm]

theorem mirror_chain_expansion_holds : MirrorChainExpansion := by
  intro A _ _ M _ _ k r E La ρ hG m _hm u hR0 hR1 hL
  have hm : m + 2 ≤ r := _hm
  set a := colsVm k r (m + 2) with hadef
  have hav : ∀ l : Fin (m + 2), (a l).val = r + k + 1 + l.val := by
    intro l; have := l.isLt; simp [a, colsVm]; omega
  have hcs : a ∘ Fin.castSucc = colsVm k r (m + 1) := colsVm_castSucc hm
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
  rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have ha2 : a (Fin.last (m + 1)) = esI k r ⟨r - m - 2, by omega⟩ := by
    ext; rw [hav]; simp [esI]; omega

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.castSucc l)) = esI k r ⟨r - 1 - l.val, by omega⟩ := by
      ext; rw [hav]; simp [esI]; omega
    rw [ha1, ha2, hR0 _ ⟨r - 1 - l.val, by omega⟩ (by simp; omega), smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (colsVm k r (m + 1)) (colsVm k r (m + 1)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs, ha2]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (esI k r ⟨r - m - 2, by omega⟩) (colsVm k r m) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [esI]; omega
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [colsVm, hq']; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      ρ • La (qminor E (colsVm k r m) (colsVm k r m) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = esI k r ⟨r - m - 2, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = colsVm k r m := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hx : colsVm k r (m + 1) (Fin.last m) = esI k r ⟨r - m - 1, by omega⟩ := by
        ext; simp [colsVm, esI]; omega
      have hne : esI k r ⟨r - m - 2, by omega⟩ ≠ colsVm k r (m + 1) (Fin.last m) := by
        rw [hx]; intro h'; have := congrArg Fin.val h'; simp [esI] at this; omega
      rw [tm_offdiag _ _ hne, hx, hL _ ⟨r - m - 1, by omega⟩ (by simp; omega), if_pos rfl]
      rw [colsVm_castSucc (by omega), smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = esI k r ⟨r - m - 2, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hq := q.isLt
      have hx : colsVm k r (m + 1) (Fin.castSucc q) = esI k r ⟨r - 1 - q.val, by omega⟩ := by
        ext; simp [colsVm, esI]
      have hne : esI k r ⟨r - m - 2, by omega⟩ ≠ colsVm k r (m + 1) (Fin.castSucc q) := by
        rw [hx]; intro h'; have := congrArg Fin.val h'; simp [esI] at this; omega
      rw [tm_offdiag _ _ hne, hx, hL _ ⟨r - 1 - q.val, by omega⟩ (by simp; omega), if_neg (by simp; omega),
        zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.last m)) = esI k r ⟨r - m - 1, by omega⟩ := by ext; rw [hav]; simp [esI]; omega
    rw [ha1, ha2, hR1]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.CutMP.TVG
end

section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem tVGrp_of (hRR : RightRuleEv) (hLR : LeftRuleCellv) (hTC : TorusCellv) (hCh : MirrorChainExpansion) : TVGrp := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have hGG := JDAToda.gg_pos Bs hc hg hcg
  have hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, hGG⟩
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  rw [JDAToda.omB_eq] at hf hLf hRf
  set D := OmPlus P.k P.r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  have h1N : (1 : Mx P.k P.r) ∈ Nlev P.k P.r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds P.k P.r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev P.k P.r 0 ∩ D, ∀ n ∈ Nlev P.k P.r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := P.k) (r := P.r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS P.k P.r 0 D (Wq →L[ℂ] Wp) := ⟨cut P.k P.r 0 D J, cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c * g ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs (c, g) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c * g ∈ Glev P.k P.r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hcl := claimV hRR hLR hTC hCh hD v₀ g (kvTop P.k P.r y) Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hg
    hcell P.r le_rfl 1 (Subalgebra.one_mem _) c hc
  rw [mul_one] at hcl
  have eR : kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (wCell P.k P.r (Fin.last P.r) c' * g)) c =
      kvC P.r (kvTop P.k P.r y) P.r (fun c' => La hD v₀ (wCell P.k P.r (Fin.last P.r) c' * g) 1) c :=
    kvC_loc _ _ _ _ (fun c' hc' => (cut_of_mem _ (hcell c' hc')).symm) hc
  rw [eR, ← hcl, La_apply]
  have hγ := hcell c hc
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (colsVm P.k P.r P.r) (colsVm P.k P.r P.r) (kvTop P.k P.r y) :
      SA (Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS P.k P.r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ colsVm P.k P.r P.r) (cI ∘ colsVm P.k P.r P.r)
        (kvTop P.k P.r y) := by
    have := map_qminor (SA (Wq →L[ℂ] Wp) hD).val (EA hD) (colsVm P.k P.r P.r) (colsVm P.k P.r P.r) (kvTop P.k P.r y)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL P.k P.r 0 ∘ (cI ∘ colsVm P.k P.r P.r) = colsVm P.k P.r P.r := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ colsVm P.k P.r P.r) (cI ∘ colsVm P.k P.r P.r)
    (kvTop P.k P.r y)).loc (cut P.k P.r 0 D J) J (fun x' hx' => cut_of_mem _ hx') _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

theorem toda_group_action_holds : TVGrp :=
  tVGrp_of mirror_right_rule_holds mirror_left_rule_cell_holds mirror_torus_cell_holds mirror_chain_expansion_holds

end Formalism.FourierDecayAlt.P.CutMP.TVG
end
end

section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdAlg

variable {R : Type*} [Ring R]

def cont (D e : ℕ → R) (a : ℕ) : ℕ → R
  | 0 => 1
  | 1 => D a
  | n + 2 => D (a + n + 1) * cont D e a (n + 1) - e (a + n + 1) * cont D e a n

theorem cont_zero (D e : ℕ → R) (a : ℕ) : cont D e a 0 = 1 := rfl

theorem cont_one (D e : ℕ → R) (a : ℕ) : cont D e a 1 = D a := rfl

theorem cont_two (D e : ℕ → R) (a n : ℕ) :
    cont D e a (n + 2) = D (a + n + 1) * cont D e a (n + 1) - e (a + n + 1) * cont D e a n := rfl

theorem cont_top (D e : ℕ → R) (hDe : ∀ i j, i + 1 ≤ j → D j * e i = e i * D j)
    (hee : ∀ i j, e i * e j = e j * e i) :
    ∀ n a, cont D e a (n + 2) = cont D e (a + 1) (n + 1) * D a - e (a + 1) * cont D e (a + 2) n
  | 0, a => by
    rw [cont_two, cont_one, cont_one, cont_zero, cont_zero, add_zero]
  | 1, a => by
    show cont D e a 3 = cont D e (a + 1) 2 * D a - e (a + 1) * cont D e (a + 2) 1
    have eA : cont D e a 3 = D (a + 2) * (D (a + 1) * D a - e (a + 1) * 1) - e (a + 2) * D a := rfl
    have eB : cont D e (a + 1) 2 = D (a + 2) * D (a + 1) - e (a + 2) * 1 := rfl
    rw [eA, eB, cont_one]
    have hc := hDe (a + 1) (a + 2) (by omega)
    simp only [mul_one, mul_sub, sub_mul, ← mul_assoc, hc]
    abel
  | n + 2, a => by
    have h1 := cont_top D e hDe hee (n + 1) a
    have h0 := cont_top D e hDe hee n a
    have eA : cont D e a (n + 2 + 2) =
        D (a + n + 3) * cont D e a (n + 1 + 2) - e (a + n + 3) * cont D e a (n + 2) := by
      rw [cont_two]; rfl
    have eB : cont D e (a + 1) (n + 2 + 1) =
        D (a + n + 3) * cont D e (a + 1) (n + 2) - e (a + n + 3) * cont D e (a + 1) (n + 1) := by
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, cont_two, show a + 1 + (n + 1) + 1 = a + n + 3 by omega]
    have eC : cont D e (a + 2) (n + 2) =
        D (a + n + 3) * cont D e (a + 2) (n + 1) - e (a + n + 3) * cont D e (a + 2) n := by
      rw [cont_two, show a + 2 + n + 1 = a + n + 3 by omega]
    rw [eA, eB, eC, h1, h0]
    have hc1 := hDe (a + 1) (a + n + 3) (by omega)
    have hc2 := hee (a + n + 3) (a + 1)
    simp only [mul_sub, sub_mul, ← mul_assoc, hc1, hc2]
    abel

def topK (Dt e : ℕ → R) (r : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | m + 1 => ((topK Dt e r m).1 * Dt m - e (r - m) * (topK Dt e r m).2, (topK Dt e r m).1)

theorem topK_eq (D e : ℕ → R) (hDe : ∀ i j, i + 1 ≤ j → D j * e i = e i * D j)
    (hee : ∀ i j, e i * e j = e j * e i) (r : ℕ) (Dt : ℕ → R) (hDt : ∀ m < r, Dt m = D (r - m - 1)) :
    ∀ m, m ≤ r → (topK Dt e r m).1 = cont D e (r - m) m ∧
      (topK Dt e r m).2 = if m = 0 then 0 else cont D e (r - m + 1) (m - 1)
  | 0, _ => by simp [topK, cont_zero]
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := topK_eq D e hDe hee r Dt hDt m (by omega)
    simp only [topK]
    refine ⟨?_, ?_⟩
    · rw [ih1, ih2, hDt m (by omega)]
      rcases m with _ | m
      · simp only [if_true, mul_zero, sub_zero, cont_zero, one_mul, Nat.sub_zero]
        rfl
      · obtain ⟨a, rfl⟩ : ∃ a, r = a + m + 2 := ⟨r - m - 2, by omega⟩
        rw [if_neg (by omega), show a + m + 2 - (m + 1) = a + 1 by omega,
          show a + 1 - 1 = a by omega, show a + 1 + 1 = a + 2 by omega,
          show a + m + 2 - (m + 1 + 1) = a by omega, show m + 1 - 1 = m by omega, cont_top D e hDe hee m a]
    · rw [ih1, if_neg (by omega), show m + 1 - 1 = m by omega, show r - (m + 1) + 1 = r - m by omega]

theorem topK_conj (G : R) (Dw Dy e : ℕ → R) (r : ℕ) (hG : ∀ m < r, G * Dw m = Dy m * G)
    (hGe : ∀ j, G * e j = e j * G) :
    ∀ m, m ≤ r → G * (topK Dw e r m).1 = (topK Dy e r m).1 * G ∧
      G * (topK Dw e r m).2 = (topK Dy e r m).2 * G
  | 0, _ => by simp [topK]
  | m + 1, hm => by
    obtain ⟨ih1, ih2⟩ := topK_conj G Dw Dy e r hG hGe m (by omega)
    simp only [topK]
    refine ⟨?_, ih1⟩
    rw [mul_sub, ← mul_assoc, ih1, mul_assoc, hG m (by omega), ← mul_assoc G (e (r - m)), hGe,
      mul_assoc (e (r - m)) G, ih2, sub_mul, mul_assoc, mul_assoc]

def botA (D Cb Cbi : ℕ → R) (r : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | i + 1 => if i < r then
      (D i * (botA D Cb Cbi r i).1 - Cb i * (botA D Cb Cbi r i).2, Cbi i * (botA D Cb Cbi r i).1)
      else botA D Cb Cbi r i

theorem botA_eq (D Cb Cbi : ℕ → R) (r : ℕ) :
    ∀ i, i ≤ r → (botA D Cb Cbi r i).1 = cont D (fun j => Cb j * Cbi (j - 1)) 0 i ∧
      (botA D Cb Cbi r i).2 =
        if i = 0 then 0 else Cbi (i - 1) * cont D (fun j => Cb j * Cbi (j - 1)) 0 (i - 1)
  | 0, _ => by simp [botA, cont_zero]
  | i + 1, hi => by
    obtain ⟨ih1, ih2⟩ := botA_eq D Cb Cbi r i (by omega)
    simp only [botA, if_pos (show i < r by omega)]
    refine ⟨?_, ?_⟩
    · rw [ih1, ih2]
      rcases i with _ | i
      · simp only [if_true, mul_zero, sub_zero, cont_zero, mul_one]
        rfl
      · rw [if_neg (by omega), cont_two, show 0 + i + 1 = i + 1 by omega, show i + 1 - 1 = i by omega,
          mul_assoc]
    · rw [ih1, if_neg (by omega), show i + 1 - 1 = i by omega]

end Formalism.FourierDecayAlt.P.CutMP.TVCrdAlg
end
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdLoc

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {k r : ℕ}

def gam (k r : ℕ) (a : Fin r) (x : Fin r → ℂ) : ℂ := ((‖x a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ)

theorem gaugeF_eq (k r : ℕ) : gaugeF k r = fun x => ∏ a : Fin r, gam k r a x := by
  funext x
  unfold gaugeF Formalism.FourierDecayAlt.Q.resG
  simp only [smul_eq_mul, mul_one, gam, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [if_pos (by simp)]

theorem gam_smooth (a : Fin r) : ContDiffOn ℝ ∞ (gam k r a) (OmX r) := by
  intro x hx
  have h1 : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => ‖c a‖) x :=
    (contDiffAt_norm ℝ (hx a)).comp x
      (ContinuousLinearMap.proj a : (Fin r → ℂ) →L[ℝ] ℂ).contDiff.contDiffAt
  have h2 := Complex.ofRealCLM.contDiff.contDiffAt.comp x (h1.pow (Mdim k r a - 1))
  exact h2.contDiffWithinAt

theorem gaugeF_smooth : ContDiffOn ℝ ∞ (gaugeF k r) (OmX r) := by
  rw [gaugeF_eq]
  exact contDiffOn_prod fun a _ => gam_smooth a

theorem gaugeF_ne {c : Fin r → ℂ} (hc : c ∈ OmX r) : gaugeF k r c ≠ 0 := by
  rw [gaugeF_eq]
  exact Finset.prod_ne_zero_iff.mpr fun a _ =>
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc a)))

theorem fderiv_zero_of_const {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : (Fin r → ℂ) → F}
    {x v : Fin r → ℂ} (hd : DifferentiableAt ℝ h x) (hc : ∀ t : ℝ, h (x + t • v) = h x) :
    fderiv ℝ h x v = 0 := by
  have hf : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 : HasDerivAt (fun t : ℝ => h (x + t • v)) (fderiv ℝ h x v) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hf (by simp)
  have h2 : HasDerivAt (fun t : ℝ => h (x + t • v)) 0 0 := by
    simp_rw [hc]
    exact hasDerivAt_const _ _
  exact h1.unique h2

def gamO (k r : ℕ) (i : Fin r) (x : Fin r → ℂ) : ℂ := ∏ a ∈ Finset.univ.erase i, gam k r a x

theorem gamO_smooth (i : Fin r) : ContDiffOn ℝ ∞ (gamO k r i) (OmX r) := by
  unfold gamO
  exact contDiffOn_prod fun a _ => gam_smooth a

theorem gamO_line (i : Fin r) (x : Fin r → ℂ) (w : ℂ) (t : ℝ) :
    gamO k r i (x + t • (Pi.single i w : Fin r → ℂ)) = gamO k r i x := by
  unfold gamO
  refine Finset.prod_congr rfl fun a ha => ?_
  have hai : a ≠ i := Finset.ne_of_mem_erase ha
  simp only [gam, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hai, smul_zero, add_zero]

theorem gauge_split (i : Fin r) (x : Fin r → ℂ) : gaugeF k r x = gam k r i x * gamO k r i x := by
  rw [gaugeF_eq, gamO]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

private theorem wbar_smul_lemma {m : ℕ} (l : Fin m) (c : (Fin m → ℂ) → ℂ) (φ : (Fin m → ℂ) → X)
    (x : Fin m → ℂ) (hc : DifferentiableAt ℝ c x) (hφ : DifferentiableAt ℝ φ x) :
    wirtBar l (fun y => c y • φ y) x = c x • wirtBar l φ x + wirtBar l c x • φ x := by
  unfold Formalism.QuantumDeterminants.wirtBar
  have e : (fun y => c y • φ y) = c • φ := rfl
  rw [e, fderiv_smul hc hφ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

theorem pbOp_gauge (i : Fin r) (f : (Fin r → ℂ) → X) (hf : f ∈ WSm r X) :
    pbOp i (fun x => gaugeF k r x • f x) =
      fun x => gaugeF k r x • pbOp i f x + (((Mdim k r i - 1 : ℕ) : ℂ) / 2) • (gaugeF k r x • f x) := by
  funext x
  show pbOp i (fun x => gaugeF k r x • f x) x =
    gaugeF k r x • pbOp i f x + (((Mdim k r i - 1 : ℕ) : ℂ) / 2) • (gaugeF k r x • f x)
  by_cases hx : x ∈ OmX r
  · have hO : IsOpen (OmX r) := by
      have e : OmX r = ⋂ l, {y : Fin r → ℂ | y l ≠ 0} := by
        ext y
        simp [OmX]
      rw [e]
      exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
    have hfd : DifferentiableAt ℝ f x :=
      (hf.1.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hgi : DifferentiableAt ℝ (gam k r i) x := Formalism.FourierDecayAlt.P.Qx6.diff_gamma i _ hx
    have hgO : DifferentiableAt ℝ (gamO k r i) x :=
      ((gamO_smooth i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hsplit : (fun y => gaugeF k r y • f y) = fun y => gam k r i y • (gamO k r i y • f y) := by
      funext y
      rw [gauge_split, mul_smul]

    have hwO : wirtBar i (gamO k r i) x = 0 := by
      unfold Formalism.QuantumDeterminants.wirtBar
      rw [fderiv_zero_of_const hgO (gamO_line i x 1), fderiv_zero_of_const hgO (gamO_line i x Complex.I)]
      simp
    have hpg := Formalism.FourierDecayAlt.P.Qx6.pbOp_gamma i hx (Mdim k r i - 1)
    unfold pbOp at hpg
    rw [if_pos hx] at hpg
    have key : star (x i) * wirtBar i (gam k r i) x =
        ((Mdim k r i - 1 : ℕ) : ℂ) / 2 * gam k r i x := by
      rw [← smul_eq_mul]
      exact hpg
    unfold pbOp
    rw [if_pos hx, if_pos hx, hsplit, wbar_smul_lemma i (gam k r i) (fun y => gamO k r i y • f y) x hgi (hgO.smul hfd),
      wbar_smul_lemma i _ _ x hgO hfd, hwO, gauge_split]
    simp only [smul_add, zero_smul, add_zero, smul_smul]
    rw [← mul_assoc (star (x i)) (wirtBar i (gam k r i) x), key]
    congr 1 <;> congr 1 <;> ring
  · unfold pbOp
    rw [if_neg hx, if_neg hx, hf.2 x hx]
    simp

theorem loc (Φ : (Fin r → ℂ) → X) (U : Set (Fin r → ℂ)) (c : Fin r → ℂ) (hU : IsOpen U) (hUO : U ⊆ OmX r)
    (hc : c ∈ U) (hΨ : ContDiffOn ℝ ∞ (fun c' => gaugeF k r c' • Φ c') U) :
    ∃ φ : (Fin r → ℂ) → X, φ ∈ WSm r X ∧ Φ =ᶠ[𝓝 c] φ ∧
      (fun c' => gaugeF k r c' • Φ c') =ᶠ[𝓝 c] (fun c' => gaugeF k r c' • φ c') := by
  have hO : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {y : Fin r → ℂ | y l ≠ 0} := by
      ext y
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc

  let χ : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hcl : Metric.closedBall c (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hχ0 : ∀ z, z ∉ Metric.closedBall c (ε / 2) → χ z = 0 := by
    intro z hz
    have h1 : z ∉ Function.support χ := by
      rw [χ.support_eq]
      exact fun h => hz (Metric.ball_subset_closedBall h)
    simpa [Function.mem_support] using h1
  let φ : (Fin r → ℂ) → X := fun y => χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y))
  have hev : Φ =ᶠ[𝓝 c] φ := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < ε / 4))
      fun y hy => ?_
    have hyU : y ∈ U := hball (Metric.ball_subset_ball (by linarith) hy)
    have h1 : χ y = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    show Φ y = χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y))
    rw [h1, one_smul, inv_smul_smul₀ (gaugeF_ne (hUO hyU))]
  have hsm : ∀ y ∈ OmX r, ContDiffAt ℝ ∞ φ y := by
    intro y hyO
    by_cases hyU : y ∈ U
    · have hg := (gaugeF_smooth (k := k)).contDiffAt (hO.mem_nhds hyO)
      have hgi := hg.inv (gaugeF_ne hyO)
      have hΨ' := hΨ.contDiffAt (hU.mem_nhds hyU)
      exact χ.contDiff.contDiffAt.smul (hgi.smul hΨ')
    · have hyc : y ∉ Metric.closedBall c (ε / 2) := fun h => hyU (hcl h)
      refine (contDiffAt_const (c := (0 : X))).congr_of_eventuallyEq ?_
      refine Filter.eventually_of_mem (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hyc)
        fun z hz => ?_
      show χ z • ((gaugeF k r z)⁻¹ • (gaugeF k r z • Φ z)) = 0
      rw [hχ0 z hz, zero_smul]
  refine ⟨φ, ?_, hev, hev.mono fun y hy => congrArg (gaugeF k r y • ·) hy⟩
  show ContDiffOn ℝ ∞ φ (OmX r) ∧ ∀ x, x ∉ OmX r → φ x = 0
  refine ⟨fun y hy => (hsm y hy).contDiffWithinAt, fun y hy => ?_⟩
  have hyc : y ∉ Metric.closedBall c (ε / 2) := fun h => hy (hUO (hcl h))
  show χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y)) = 0
  rw [hχ0 y hyc, zero_smul]

end Formalism.FourierDecayAlt.P.CutMP.TVCrdLoc
end
end

section
open Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdGerm

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutMP

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}

theorem pbOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    pbOp l f₁ =ᶠ[𝓝 c] pbOp l f₂ := by
  filter_upwards [h.eventuallyEq_nhds] with c' hc'
  simp only [pbOp, wirtBar, hc'.fderiv_eq]

theorem cbOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbOp l f₁ =ᶠ[𝓝 c] cbOp l f₂ := by
  filter_upwards [h] with c' hc'
  simp only [cbOp, hc']

theorem cbiOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbiOp l f₁ =ᶠ[𝓝 c] cbiOp l f₂ := by
  filter_upwards [h] with c' hc'
  simp only [cbiOp, hc']

theorem pbN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    pbN r i f₁ =ᶠ[𝓝 c] pbN r i f₂ := by
  unfold pbN
  split_ifs with hi
  · exact pbOp_germ _ h
  · exact EventuallyEq.rfl

theorem cbN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbN r i f₁ =ᶠ[𝓝 c] cbN r i f₂ := by
  unfold cbN
  split_ifs with hi
  · exact cbOp_germ _ h
  · exact EventuallyEq.rfl

theorem cbiN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbiN r i f₁ =ᶠ[𝓝 c] cbiN r i f₂ := by
  unfold cbiN
  split_ifs with hi
  · exact cbiOp_germ _ h
  · exact EventuallyEq.rfl

theorem iteratedOperator_germ (w : ℂ) : ∀ (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X) (c : Fin r → ℂ), f₁ =ᶠ[𝓝 c] f₂ →
    (kvP r w m).1 f₁ =ᶠ[𝓝 c] (kvP r w m).1 f₂ ∧ (kvP r w m).2 f₁ =ᶠ[𝓝 c] (kvP r w m).2 f₂
  | 0, f₁, f₂, c, h => ⟨h, EventuallyEq.rfl⟩
  | m + 1, f₁, f₂, c, h => by
    have hin : (fun c' => (w - (m : ℂ)) • f₁ c' - pbN r (r - m - 1) f₁ c') =ᶠ[𝓝 c]
        (fun c' => (w - (m : ℂ)) • f₂ c' - pbN r (r - m - 1) f₂ c') := by
      filter_upwards [h, pbN_germ (r - m - 1) h] with c' h1 h2
      rw [h1, h2]
    have ih1 := iteratedOperator_germ w m _ _ c hin
    have ih2 := iteratedOperator_germ w m f₁ f₂ c h
    refine ⟨?_, ih2.1⟩
    show (fun c' => (kvP r w m).1 _ c' - cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f₁)) c') =ᶠ[𝓝 c]
      (fun c' => (kvP r w m).1 _ c' - cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f₂)) c')
    filter_upwards [ih1.1, cbN_germ (r - m) (cbiN_germ (r - m - 1) ih2.2)] with c' h1 h2
    rw [h1, h2]

theorem vABm_germ (y : ℂ) : ∀ (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X) (c : Fin r → ℂ), f₁ =ᶠ[𝓝 c] f₂ →
    (vABm r y m).1 f₁ =ᶠ[𝓝 c] (vABm r y m).1 f₂ ∧ (vABm r y m).2 f₁ =ᶠ[𝓝 c] (vABm r y m).2 f₂
  | 0, f₁, f₂, c, h => ⟨h, EventuallyEq.rfl⟩
  | i + 1, f₁, f₂, c, h => by
    have ih := vABm_germ y i f₁ f₂ c h
    by_cases hi : i < r
    · simp only [vABm, dif_pos hi]
      refine ⟨?_, cbiOp_germ _ ih.1⟩
      filter_upwards [ih.1, pbOp_germ ⟨i, hi⟩ ih.1, cbOp_germ ⟨i, hi⟩ ih.2] with c' h1 h2 h3
      simp only [Pi.sub_apply, Pi.smul_apply]
      rw [h1, h2, h3]
    · simp only [vABm, dif_neg hi]
      exact ih

end Formalism.FourierDecayAlt.P.CutMP.TVCrdGerm
end
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdE

open TVCrdAlg TVCrdLoc TVCrdGerm

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}

theorem memW {f : (Fin r → ℂ) → X} (h : f ∈ WSm r X) :
    ContDiffOn ℝ ∞ f (OmX r) ∧ ∀ x, x ∉ OmX r → f x = 0 := h

def opE (l : Fin r) (i : Fin 6) : Module.End ℂ (WSm r X) where
  toFun f := ⟨opL l i f, preserved_operators_holds r X l i f f.2⟩
  map_add' f g := Subtype.ext (linear_operators_holds r X l i f g 1 f.2 g.2).1
  map_smul' a f := Subtype.ext (linear_operators_holds r X l i f f a f.2 f.2).2

@[simp] theorem opE_coe (l : Fin r) (i : Fin 6) (f : WSm r X) :
    ((opE l i f : WSm r X) : (Fin r → ℂ) → X) = opL l i f := rfl

theorem opL_three (l : Fin r) : opL (E := X) l 3 = pbOp l := rfl
theorem opL_four (l : Fin r) : opL (E := X) l 4 = cbOp l := rfl
theorem opL_five (l : Fin r) : opL (E := X) l 5 = cbiOp l := rfl

def mulE (a : (Fin r → ℂ) → ℂ) (ha : ContDiffOn ℝ ∞ a (OmX r)) : Module.End ℂ (WSm r X) where
  toFun f := ⟨fun x => a x • (f : (Fin r → ℂ) → X) x,
    ⟨ha.smul (memW f.2).1, fun x hx => by simp [(memW f.2).2 x hx]⟩⟩
  map_add' f g := Subtype.ext (funext fun x => by simp [smul_add])
  map_smul' s f := Subtype.ext (funext fun x => by simp [smul_comm (a x) s])

@[simp] theorem mulE_coe (a : (Fin r → ℂ) → ℂ) (ha : ContDiffOn ℝ ∞ a (OmX r)) (f : WSm r X) :
    ((mulE a ha f : WSm r X) : (Fin r → ℂ) → X) = fun x => a x • (f : (Fin r → ℂ) → X) x := rfl

theorem comm_of_mul (A B : Module.End ℂ (WSm r X)) (a b : (Fin r → ℂ) → ℂ)
    (hA : ∀ (f : WSm r X) x, (A f : (Fin r → ℂ) → X) x = a x • (f : (Fin r → ℂ) → X) x)
    (hB : ∀ (f : WSm r X) x, (B f : (Fin r → ℂ) → X) x = b x • (f : (Fin r → ℂ) → X) x) : Commute A B := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
  show (A (B f) : (Fin r → ℂ) → X) x = (B (A f) : (Fin r → ℂ) → X) x
  rw [hA, hB, hB, hA, smul_smul, smul_smul, mul_comm]

def PN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 3 else 0
def CbN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 4 else 0
def CbiN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 5 else 0

theorem PN_coe (i : ℕ) (f : WSm r X) : ((PN r X i f : WSm r X) : (Fin r → ℂ) → X) = pbN r i f := by
  unfold PN pbN; split_ifs <;> rfl
theorem CbN_coe (i : ℕ) (f : WSm r X) : ((CbN r X i f : WSm r X) : (Fin r → ℂ) → X) = cbN r i f := by
  unfold CbN cbN; split_ifs <;> rfl
theorem CbiN_coe (i : ℕ) (f : WSm r X) : ((CbiN r X i f : WSm r X) : (Fin r → ℂ) → X) = cbiN r i f := by
  unfold CbiN cbiN; split_ifs <;> rfl

theorem CbN_mul (i : ℕ) (f : WSm r X) (x : Fin r → ℂ) :
    (CbN r X i f : (Fin r → ℂ) → X) x = (if h : i < r then star (x ⟨i, h⟩) else 0) • (f : (Fin r → ℂ) → X) x := by
  unfold CbN; split_ifs <;> simp [opL, cbOp]
theorem CbiN_mul (i : ℕ) (f : WSm r X) (x : Fin r → ℂ) :
    (CbiN r X i f : (Fin r → ℂ) → X) x =
      (if h : i < r then (star (x ⟨i, h⟩))⁻¹ else 0) • (f : (Fin r → ℂ) → X) x := by
  unfold CbiN; split_ifs <;> simp [opL, cbiOp]

theorem comm_PN_CbN {i j : ℕ} (h : i ≠ j) : Commute (PN r X i) (CbN r X j) := by
  unfold PN CbN
  split_ifs with h1 h2
  · refine LinearMap.ext fun f => Subtype.ext ?_
    exact commuting_functional_holds r X ⟨i, h1⟩ ⟨j, h2⟩ 3 4 f f.2 (Or.inl fun e => h (congrArg Fin.val e))
  all_goals simp
theorem comm_PN_CbiN {i j : ℕ} (h : i ≠ j) : Commute (PN r X i) (CbiN r X j) := by
  unfold PN CbiN
  split_ifs with h1 h2
  · refine LinearMap.ext fun f => Subtype.ext ?_
    exact commuting_functional_holds r X ⟨i, h1⟩ ⟨j, h2⟩ 3 5 f f.2 (Or.inl fun e => h (congrArg Fin.val e))
  all_goals simp

theorem comm_CbN_CbN (i j : ℕ) : Commute (CbN r X i) (CbN r X j) := comm_of_mul _ _ _ _ (CbN_mul i) (CbN_mul j)
theorem comm_CbN_CbiN (i j : ℕ) : Commute (CbN r X i) (CbiN r X j) := comm_of_mul _ _ _ _ (CbN_mul i) (CbiN_mul j)
theorem comm_CbiN_CbiN (i j : ℕ) : Commute (CbiN r X i) (CbiN r X j) :=
  comm_of_mul _ _ _ _ (CbiN_mul i) (CbiN_mul j)

def Gop (k r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] : Module.End ℂ (WSm r X) :=
  mulE (gaugeF k r) gaugeF_smooth

theorem comm_G_CbN (k i : ℕ) : Commute (Gop k r X) (CbN r X i) :=
  comm_of_mul _ _ (gaugeF k r) _ (fun _ _ => rfl) (CbN_mul i)
theorem comm_G_CbiN (k i : ℕ) : Commute (Gop k r X) (CbiN r X i) :=
  comm_of_mul _ _ (gaugeF k r) _ (fun _ _ => rfl) (CbiN_mul i)

def sG (k r : ℕ) (i : Fin r) : ℂ := ((Mdim k r i - 1 : ℕ) : ℂ) / 2

theorem P_G (k : ℕ) (i : Fin r) : opE i 3 * Gop k r X = Gop k r X * opE i 3 + sG k r i • Gop k r X := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  show pbOp i (fun x => gaugeF k r x • (f : (Fin r → ℂ) → X) x) = _
  rw [pbOp_gauge i _ f.2]
  funext x
  simp [Gop, opL_three, sG]

theorem G_PN (k : ℕ) {i : ℕ} (hi : i < r) :
    Gop k r X * PN r X i = (PN r X i - sG k r ⟨i, hi⟩ • 1) * Gop k r X := by
  have h := P_G (X := X) k ⟨i, hi⟩
  have hP : PN r X i = opE ⟨i, hi⟩ 3 := dif_pos hi
  rw [hP, sub_mul, smul_mul_assoc, one_mul, h]
  abel

def Dd (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (y : ℂ) (j : ℕ) : Module.End ℂ (WSm r X) :=
  y • 1 - PN r X j
def Ee (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (j : ℕ) : Module.End ℂ (WSm r X) :=
  CbN r X j * CbiN r X (j - 1)
def Dw (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (w : ℂ) (m : ℕ) : Module.End ℂ (WSm r X) :=
  (w - (m : ℂ)) • 1 - PN r X (r - m - 1)

theorem hDe (y : ℂ) : ∀ i j, i + 1 ≤ j → Dd r X y j * Ee r X i = Ee r X i * Dd r X y j := by
  intro i j hij
  have : Commute (Dd r X y j) (Ee r X i) := by
    unfold Dd Ee
    refine Commute.sub_left ((Commute.one_left _).smul_left y) ?_
    exact (comm_PN_CbN (by omega)).mul_right (comm_PN_CbiN (by omega))
  exact this.eq

theorem hee : ∀ i j, Ee r X i * Ee r X j = Ee r X j * Ee r X i := by
  intro i j
  have : Commute (Ee r X i) (Ee r X j) := by
    unfold Ee
    refine Commute.mul_left ?_ ?_
    · exact (comm_CbN_CbN i j).mul_right (comm_CbN_CbiN i (j - 1))
    · exact ((comm_CbN_CbiN j (i - 1)).symm).mul_right (comm_CbiN_CbiN (i - 1) (j - 1))
  exact this.eq

theorem hGe (k : ℕ) : ∀ j, Gop k r X * Ee r X j = Ee r X j * Gop k r X := by
  intro j
  exact ((comm_G_CbN k j).mul_right (comm_G_CbiN k (j - 1))).eq

theorem shift_eq (k : ℕ) (y : ℂ) {m : ℕ} (hm : m < r) :
    kvTop k r y - (m : ℂ) + sG k r ⟨r - m - 1, by omega⟩ = y := by
  have h : Mdim k r ⟨r - m - 1, by omega⟩ - 1 = 2 * m + k + 2 := by
    simp only [Mdim]; omega
  simp only [sG, kvTop, h]
  push_cast
  ring

theorem hG (k : ℕ) (y : ℂ) : ∀ m < r,
    Gop k r X * Dw r X (kvTop k r y) m = Dd r X y (r - m - 1) * Gop k r X := by
  intro m hm
  unfold Dw Dd
  rw [mul_sub, mul_smul_comm, mul_one, G_PN k (show r - m - 1 < r by omega), sub_mul, sub_mul, smul_mul_assoc,
    smul_mul_assoc, one_mul]
  have hy := shift_eq (r := r) k y hm
  conv_rhs => rw [← hy]
  rw [add_smul]
  abel

theorem iteratedOperator_coe (w : ℂ) : ∀ (m : ℕ) (f : WSm r X),
    (kvP r w m).1 (f : (Fin r → ℂ) → X) = ((topK (Dw r X w) (Ee r X) r m).1 f : WSm r X) ∧
      (kvP r w m).2 (f : (Fin r → ℂ) → X) = ((topK (Dw r X w) (Ee r X) r m).2 f : WSm r X)
  | 0, f => ⟨rfl, rfl⟩
  | m + 1, f => by
    have hD : (fun c => (w - (m : ℂ)) • (f : (Fin r → ℂ) → X) c - pbN r (r - m - 1) (f : (Fin r → ℂ) → X) c) =
        ((Dw r X w m f : WSm r X) : (Fin r → ℂ) → X) := by
      funext c
      simp [Dw, PN_coe]
    refine ⟨?_, (iteratedOperator_coe w m f).1⟩
    simp only [kvP, topK]
    rw [hD, (iteratedOperator_coe w m _).1, (iteratedOperator_coe w m f).2, ← CbiN_coe, ← CbN_coe]
    simp [Ee]

theorem vABm_coe (y : ℂ) : ∀ (i : ℕ) (f : WSm r X),
    (vABm r y i).1 (f : (Fin r → ℂ) → X) = ((botA (Dd r X y) (CbN r X) (CbiN r X) r i).1 f : WSm r X) ∧
      (vABm r y i).2 (f : (Fin r → ℂ) → X) = ((botA (Dd r X y) (CbN r X) (CbiN r X) r i).2 f : WSm r X)
  | 0, f => ⟨rfl, rfl⟩
  | i + 1, f => by
    by_cases h : i < r
    · obtain ⟨h1, h2⟩ := vABm_coe y i f
      have hP : PN r X i = opE ⟨i, h⟩ 3 := dif_pos h
      have hC : CbN r X i = opE ⟨i, h⟩ 4 := dif_pos h
      have hCi : CbiN r X i = opE ⟨i, h⟩ 5 := dif_pos h
      simp only [vABm, dif_pos h, botA, if_pos h]
      rw [h1, h2]
      refine ⟨?_, ?_⟩
      · simp [Dd, hP, hC, opL_three, opL_four]
      · simp [hCi, opL_five]
    · simp only [vABm, dif_neg h, botA, if_neg h]
      exact vABm_coe y i f

end Formalism.FourierDecayAlt.P.CutMP.TVCrdE

namespace Formalism.FourierDecayAlt.P.CutMP

open TVCrdAlg TVCrdLoc TVCrdGerm TVCrdE

theorem toda_coordinate_holds : TVCrd := by
  intro k r X _ _ y Φ U c hU hUO hc hΨ
  obtain ⟨φ, hφ, hΦ, hΨφ⟩ := TVCrdLoc.loc (k := k) Φ U c hU hUO hc hΨ
  have eL : kvC r (kvTop k r y) r Φ c = kvC r (kvTop k r y) r φ c :=
    (iteratedOperator_germ (kvTop k r y) r Φ φ c hΦ).1.eq_of_nhds
  have eR : (vABm r y r).1 (fun c' => gaugeF k r c' • Φ c') c =
      (vABm r y r).1 (fun c' => gaugeF k r c' • φ c') c :=
    (vABm_germ y r _ _ c hΨφ).1.eq_of_nhds
  rw [eL, eR]
  let f : WSm r X := ⟨φ, hφ⟩
  have hK : kvC r (kvTop k r y) r φ = ((topK (Dw r X (kvTop k r y)) (Ee r X) r r).1 f : WSm r X) :=
    (iteratedOperator_coe (kvTop k r y) r f).1
  have hA : (vABm r y r).1 (fun c' => gaugeF k r c' • φ c') =
      ((botA (Dd r X y) (CbN r X) (CbiN r X) r r).1 (Gop k r X f) : WSm r X) :=
    (vABm_coe y r (Gop k r X f)).1
  have hB := (botA_eq (Dd r X y) (CbN r X) (CbiN r X) r r le_rfl).1
  have hT := (topK_eq (Dd r X y) (Ee r X) (hDe y) hee r (fun m => Dd r X y (r - m - 1)) (fun _ _ => rfl) r le_rfl).1
  have hC := (topK_conj (Gop k r X) (Dw r X (kvTop k r y)) (fun m => Dd r X y (r - m - 1)) (Ee r X) r
    (hG k y) (hGe k) r le_rfl).1
  rw [Nat.sub_self] at hT
  have hAT : (botA (Dd r X y) (CbN r X) (CbiN r X) r r).1 =
      (topK (fun m => Dd r X y (r - m - 1)) (Ee r X) r r).1 := by
    rw [hB, hT]; rfl
  rw [hK, hA, hAT]
  have h2 : (topK (fun m => Dd r X y (r - m - 1)) (Ee r X) r r).1 (Gop k r X f) =
      Gop k r X ((topK (Dw r X (kvTop k r y)) (Ee r X) r r).1 f) := by
    rw [← Module.End.mul_apply, ← hC, Module.End.mul_apply]
  rw [h2]
  rfl

end Formalism.FourierDecayAlt.P.CutMP
end
end

section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem jda_capelli_toda_mirror_proof : JDACapTodaV :=
  jDACapTodaV_of_parts toda_coefficient_holds TVG.toda_group_action_holds toda_coordinate_holds

end Formalism.FourierDecayAlt.P.CutMP
end

section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem jDCapA_of_inv_toda (hI : JDACapInv) (hT : JDACapToda) (hTv : JDACapTodaV) : JDCapA :=
  jDCapA_of_grp (jDAGrp_of_parts capelli_representation_holds hI hT hTv)

theorem jDCapA_of_inv_todaV (hI : JDACapInv) (hTv : JDACapTodaV) : JDCapA :=
  jDCapA_of_inv_toda hI jda_capelli_toda_proof hTv

theorem jDCapA_of_todaV (hTv : JDACapTodaV) : JDCapA := jDCapA_of_inv_todaV capelli_invariance_criterion hTv

theorem capelli_minors_holds : JDCapA := jDCapA_of_todaV jda_capelli_toda_mirror_proof

end Formalism.FourierDecayAlt.P.CutMP
end
