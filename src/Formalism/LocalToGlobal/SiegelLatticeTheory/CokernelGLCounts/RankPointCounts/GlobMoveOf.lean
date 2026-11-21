import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupGlob

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def locL (p : PlF D) (A B : PairVal.MatR D) : MatP D p :=
  match (Zd.M p).split with
  | none => Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) * A.map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a))
  | some g => glue g.e (Matrix.diagonal (cf Zd p) * A.map ((p1 g.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p))
      (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 g.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p))

def locR (p : PlF D) (A B : PairVal.MatR D) : MatP D p :=
  match (Zd.M p).split with
  | none => Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) * B.map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))
  | some g => glue g.e (Matrix.diagonal (cfi Zd p) * B.map ((p1 g.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p))
      (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 g.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p))

theorem tr_lem {K : Type*} [CommRing K] {n : ℕ} (S L X B : Matrix (Fin n) (Fin n) K) (hS : S * S = 1)
    (hSt : S.transpose = S) :
    (L * (X * S) * B * S).transpose * S = (S * B.transpose * S) * (X.transpose * S) * (S * L.transpose * S) := by
  simp only [Matrix.transpose_mul, hSt, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc S S, hS, Matrix.one_mul]

theorem corner_conj {K : Type*} [CommRing K] {r : ℕ} {L U Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hL : IsLo L)
    (hU : IsUp U) (c : K) : L * (Y - c • Ecorner r) * U = L * Y * U - c • Ecorner r := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU]

theorem locMove (u u' : D.what₂.Word) (p : PlF D) {Z₁ Z₂ A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B)
    (h : Z₂ * Sg D.host.E D.R.rS = A * (Z₁ * Sg D.host.E D.R.rS) * B) :
    CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p =
      locL Zd p A B * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A B := by
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hM : (Zd.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>
    simp only [hM, hR] at hAg
  · set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)
    set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)
    have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
    rw [zzp_sgn_ord Zd u u' p hM Z₂, zzp_sgn_ord Zd u u' p hM Z₁, h, Matrix.map_mul, Matrix.map_mul,
      regroup fr fri hfr]
    simp only [locL, locR, hM]
    rfl
  · obtain ⟨hge, hgq⟩ := hAg
    have hcc : ∀ a, cf Zd p a * cfi Zd p a = 1 := cf_cfi Zd p
    have hcc' : ∀ a, cfi Zd p a * cf Zd p a = 1 := cfi_cf Zd p
    have hL1 : IsLo (Matrix.diagonal (cf Zd p) * A.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p)) :=
      isLo_conj (isLo_map _ hA) _ _ hcc
    have hU1 : IsUp (Matrix.diagonal (cfi Zd p) * B.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) :=
      isUp_conj (isUp_map _ hB) _ _ hcc'
    have hL2a : IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) :=
      (isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) :
        IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    have hU2a : IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) :=
      (isUp_conj (isUp_transpose (isLo_map ((p2 sg.e).comp (D.s.atP p).ιE) hA)) _ _ (fun a => sgn_sq' D.R.rS a) :
        IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    have hL2 := isLo_conj hL2a (cf Zd p) (cfi Zd p) hcc
    have hU2 := isUp_conj hU2a (cfi Zd p) (cf Zd p) hcc'
    have hZ2 : Z₂ = A * (Z₁ * Sg D.host.E D.R.rS) * B * Sg D.host.E D.R.rS := by
      rw [← h, Matrix.mul_assoc, sg_sq, Matrix.mul_one]
    simp only [locL, locR, hM, hge]
    apply mat_eq sg.e
    · have l1 := zz1' Zd p sg hR g hM hge hgq u u' Z₂
      have r1 := zz1' Zd p sg hR g hM hge hgq u u' Z₁
      have key1 : (A * (Z₁ * Sg D.host.E D.R.rS) * B).map ((p1 sg.e).comp (D.s.atP p).ιE) =
          A.map ((p1 sg.e).comp (D.s.atP p).ιE) * (Z₁ * Sg D.host.E D.R.rS).map ((p1 sg.e).comp (D.s.atP p).ιE) *
            B.map ((p1 sg.e).comp (D.s.atP p).ιE) := by simp only [Matrix.map_mul]
      rw [h, key1, fact1 (cf Zd p) (cfi Zd p) hcc'] at l1
      refine l1.trans ?_
      conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, r1, corner_conj hL1 hU1]
    · have e2 : (Z₂.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS =
          (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            ((Z₁.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) := by
        rw [hZ2, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
        exact tr_lem _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _)
      have l2 := zz2' Zd p sg hR g hM hge hgq u u' Z₂
      have r2 := zz2' Zd p sg hR g hM hge hgq u u' Z₁
      rw [e2, fact1 (cf Zd p) (cfi Zd p) hcc'] at l2
      refine l2.trans ?_
      conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, r2, corner_conj hL2 hU2]

end Formalism.L2.SG.Pf.TupGlob
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def StabApprox (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z₁ A₀ B₀ : PairVal.MatR D), AtMat w Z₁ → IsLo A₀ → IsUp B₀ →
    (∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧
      locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
        l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) →
    ∃ X Y : PairVal.MatR D, IsLo X ∧ IsUp Y ∧
      X * (Z₁ * Sg D.host.E D.R.rS) * Y = Z₁ * Sg D.host.E D.R.rS ∧
      ∀ p, TieN.IntLow (Zd.M p) (locL Zd p (A₀ * X) (Y * B₀)) ∧ TieN.IntUp (Zd.M p) (locR Zd p (A₀ * X) (Y * B₀))

def Dict : Prop :=
  ∀ A B : PairVal.MatR D, IsLo A → IsUp B →
    (∀ p, TieN.IntLow (Zd.M p) (locL Zd p A B) ∧ TieN.IntUp (Zd.M p) (locR Zd p A B)) →
    IntFr A.conjTranspose ∧ IntFr (Sg D.host.E D.R.rS * B * Sg D.host.E D.R.rS) ∧
      TieG A.conjTranspose (Sg D.host.E D.R.rS * B * Sg D.host.E D.R.rS)

variable {Zd}

theorem isUpUni_of {K : Type*} [CommRing K] {n : ℕ} {U : Matrix (Fin n) (Fin n) K} (h : IsUp U) : IsUpUni U :=
  fun i j => ⟨fun hji => h.2 j i hji, by rintro rfl; exact h.1 i⟩

theorem isUp_conjT {n : ℕ} {A : Matrix (Fin n) (Fin n) D.host.E} (h : IsLo A) : IsUp A.conjTranspose :=
  ⟨fun a => by simp [Matrix.conjTranspose_apply, h.1 a],
    fun a b hab => by simp [Matrix.conjTranspose_apply, h.2 a b hab]⟩

theorem globMove_of (u u' : D.what₂.Word) (hS : StabApprox Zd u u') (hD : Dict Zd) : GlobMove D Zd.M Zd.δ u u' := by
  intro w Z₁ Z₂ _ hZ₁ hZ₂ htup
  have hZ₁' := hZ₁
  obtain ⟨L1, U1, hL1, hU1, e1⟩ := hZ₁
  obtain ⟨L2, U2, hL2, hU2, e2⟩ := hZ₂
  rw [Formalism.L2.SG.Pf.AtPt.zhatOM_eq] at e1 e2
  have lo : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsLoUni L → Formalism.DoubleCosetMeasures.IsLowUni L :=
    fun L h => ⟨fun i j hij => (h i j).1 hij, fun a => (h a a).2 rfl⟩
  have up : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUpUni U → Formalism.DoubleCosetMeasures.IsUpUni U :=
    fun U h => ⟨fun i j hji => (h i j).1 hji, fun a => (h a a).2 rfl⟩
  have lo' : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L → IsLo L :=
    fun L h => ⟨h.2, fun a b hab => h.1 hab⟩
  have up' : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U → IsUp U :=
    fun U h => ⟨h.2, fun a b hab => h.1 hab⟩
  have detL : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L →
      IsUnit L.det := fun L h => by
    rw [Matrix.det_of_lowerTriangular L h.1]
    simp [h.2]
  have detU : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U →
      IsUnit U.det := fun U h => by
    rw [Matrix.det_of_upperTriangular h.1]
    simp [h.2]
  have hA₀lo : IsLo (L2 * L1⁻¹) :=
    isLo_mul (lo' _ (lo _ hL2)) (lo' _ (Formalism.DoubleCosetMeasures.isLowUni_inv (hx := lo _ hL1)))
  have hB₀up : IsUp (U1⁻¹ * U2) :=
    isUp_mul (up' _ (Formalism.DoubleCosetMeasures.isUpUni_inv (hx := up _ hU1))) (up' _ (up _ hU2))
  have hmove : Z₂ * Sg D.host.E D.R.rS = (L2 * L1⁻¹) * (Z₁ * Sg D.host.E D.R.rS) * (U1⁻¹ * U2) := by
    rw [e2, e1]
    have i1 : L1⁻¹ * L1 = 1 := Matrix.nonsing_inv_mul L1 (detL _ (lo _ hL1))
    have i2 : U1 * U1⁻¹ = 1 := Matrix.mul_nonsing_inv U1 (detU _ (up _ hU1))
    calc L2 * ptMat w * U2 = L2 * (L1⁻¹ * L1) * ptMat w * ((U1 * U1⁻¹) * U2) := by
          rw [i1, i2, Matrix.mul_one, Matrix.one_mul]
      _ = L2 * L1⁻¹ * (L1 * ptMat w * U1) * (U1⁻¹ * U2) := by simp only [Matrix.mul_assoc]
  have hstab : ∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧
      locL Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) *
          locR Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) =
        l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ := by
    intro p
    have hmem := mem_kkOrb_self (M := Zd.M) p (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p)
    have ht := htup p
    unfold tupZ at ht
    rw [← ht] at hmem
    obtain ⟨l, ρ, hl, hρ, heq⟩ := hmem
    refine ⟨l, ρ, hl, hρ, ?_⟩
    rw [← locMove (Zd := Zd) u u' p hA₀lo hB₀up hmove]
    exact heq
  obtain ⟨X, Y, hX, hY, hXY, hint⟩ := hS w Z₁ (L2 * L1⁻¹) (U1⁻¹ * U2) hZ₁' hA₀lo hB₀up hstab
  obtain ⟨hIA, hIB, hT⟩ := hD (L2 * L1⁻¹ * X) (Y * (U1⁻¹ * U2)) (isLo_mul hA₀lo hX) (isUp_mul hY hB₀up) hint
  have hSg : Sg D.host.E D.R.rS =
      Matrix.diagonal (fun b : Fin (D.R.rS + 1) => (-1 : D.host.E) ^ (D.R.rS - b.val)) := by
    have h1 := (Formalism.L2.SG.Pf.AtPt.zhatOM_eq (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)).symm.trans
      (Formalism.L2.SG.Pf.zhatOM_eq_pv 1)
    simpa using h1
  have hsq : ∀ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - b.val) * (-1 : D.host.E) ^ (D.R.rS - b.val) = 1 := by
    intro b
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hSS : Sg D.host.E D.R.rS * Sg D.host.E D.R.rS = 1 := by
    rw [hSg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact hsq b
  refine ⟨(L2 * L1⁻¹ * X).conjTranspose, Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS,
    isUpUni_of (isUp_conjT (isLo_mul hA₀lo hX)), isUpUni_of ?_, hIA, hIB, hT, ?_⟩
  · rw [hSg]
    exact isUp_conj (isUp_mul hY hB₀up) _ _ hsq
  · rw [Matrix.conjTranspose_conjTranspose]
    have h3 : Z₂ * Sg D.host.E D.R.rS =
        L2 * L1⁻¹ * X * (Z₁ * Sg D.host.E D.R.rS) * (Y * (U1⁻¹ * U2)) := by
      rw [hmove]
      conv_lhs => rw [← hXY]
      simp only [Matrix.mul_assoc]
    calc Z₂ = Z₂ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS := by
          rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      _ = L2 * L1⁻¹ * X * Z₁ * (Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS) := by
          rw [h3]
          simp only [Matrix.mul_assoc]

end Formalism.L2.SG.Pf.TupGlob
end
end
