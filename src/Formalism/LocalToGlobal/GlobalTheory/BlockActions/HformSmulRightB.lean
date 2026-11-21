import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ArchimedeanSignatureMatchingOfTrivialBranchingSymm

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

structure PendClausesS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  coM_mem : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m)
  coM_inj : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0
  coP_mem : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg
  coP_inj : ∀ w, ∀ z ∈ (D.fm u).ptC, coPTS Tf B w z = 0 → z = 0
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c)))
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMTS Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))).re

def pendOfS (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendClausesS Tf B gP) : Pend D u where
  br τ := Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)
  coM := coMTS Tf B
  coP := coPTS Tf B
  coM_mem := h.coM_mem
  coM_inj := h.coM_inj
  coP_mem := h.coP_mem
  coP_inj := h.coP_inj
  Pt_eq := by
    intro w φ hφ c
    obtain ⟨P, hP, hv, hz⟩ := h.exP w φ hφ c
    exact hz _ (hL.map.pt_eq (bZ_isUnitS Tf) φ c P hP hv)
  lat_co := h.lat_co
  pt_co := h.pt_co
  gP := gP
  ipV_co := h.ipV_co
  re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord
  beOn_eq := hL.beOn
  interlace := sg_interlace Tf.valP

theorem brExists_of_tiedS (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendClausesS Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  ⟨pendOfS Tf hL B gP h, archimedeanSignatureMatching_of_trivial_branching_symm Tf _ fun _ => rfl⟩

section Cl

theorem bZg_isUnitS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det) :
    IsUnit (bZg u Tf.til.z0 B').det := by
  have hBi : Function.Injective B'.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hB')
  refine isUnit_det_cols (Nm_succ D.R) (iXm D * B') (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E)) ?_ ?_
  · intro x y h
    simp only [← Matrix.mulVec_mulVec] at h
    exact hBi (iXm_mulVec_injective D h)
  · intro x h
    apply quotient_not_in_range_symmetric Tf (B' *ᵥ x)
    rw [Matrix.mulVec_mulVec]; exact h

theorem trEv_repS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    ∃ Q ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m), trEvS Tf c (φ ((D.fm u).til c)) =
      fnOf _ (shiftOf (lamT u D.R.m)) (atInf (embT D) (bZg u Tf.til.z0 B')⁻¹) Q := by
  obtain ⟨P, hP, hv⟩ := val_repS Tf φ hφ c
  have hM : trEvS Tf c (φ ((D.fm u).til c)) = fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eqS, hv, Equiv.apply_symm_apply]
  have hU := atInf_inv_isUnit _ (bZg_isUnitS Tf B' hB')
  rw [hM]
  exact exists_change _ _ _ _ _ hU P hP

theorem eW_repS (Tf : FormsTiedSym D u Ch chOf) (B' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (hB' : IsUnit B'.det)
    (z : (D.mem u).P.Wrow) (hz : z ∈ (D.fm u).ptC) (c : (D.fm u).clsP) :
    ∃ Q ∈ Formalism.L2.Forms.CSpan (D.fm u).sg, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) (atInf (embT D) B'⁻¹) Q := by
  have hF := (Tf.valP.ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (Tf.clsP.y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ Formalism.L2.Forms.CSpan (D.fm u).sg := by
    have := CSpan_shW (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgT at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hU := atInf_inv_isUnit _ hB'
  rw [he]
  exact exists_change _ _ _ _ _ hU Q0 hQ0'

variable (Tf : FormsTiedSym D u Ch chOf)
  (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
  (hB : ∀ w c, IsUnit (B w c).det)

include hB

theorem coM_mem_ofS : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    coMTS Tf B w c (φ ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan ((D.fm u).lam D.R.m) := by
  intro w c φ hφ
  obtain ⟨Q, hQ, hq⟩ := trEv_repS Tf (B w c) (hB w c) φ hφ c
  have : coMTS Tf B w c (φ ((D.fm u).til c)) = Q := by
    simp only [coMTS, LinearMap.coe_comp, Function.comp_apply]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (bZg_isUnitS Tf (B w c) (hB w c)))]
  rw [this]; exact hQ

theorem coP_mem_of_isUnit_det' : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan (D.fm u).sg := by
  intro w z hz c
  obtain ⟨Q, hQ, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
  have : coPTS Tf B w z c = Q := by
    simp only [coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
      LinearEquiv.coe_coe]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c))]
  rw [this]; exact hQ

theorem coP_inj_of_isUnit_det' : ∀ w, ∀ z ∈ (D.fm u).ptC, coPTS Tf B w z = 0 → z = 0 := by
  intro w z hz h0
  apply Tf.valP.eW.injective
  rw [map_zero]
  funext c
  obtain ⟨Q, hQ, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
  have : coPTS Tf B w z c = Q := by
    simp only [coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
      LinearEquiv.coe_coe]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c))]
  have hQ0 : Q = 0 := by rw [← this, h0]; rfl
  rw [hq, hQ0, map_zero]; rfl

theorem coM_inj_ofS : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coMTS Tf B w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0 := by
  intro w c φ hφ h0
  obtain ⟨Q, hQ, hq⟩ := trEv_repS Tf (B w c) (hB w c) φ hφ c
  have hc : coMTS Tf B w c (φ ((D.fm u).til c)) = Q := by
    simp only [coMTS, LinearMap.coe_comp, Function.comp_apply]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (bZg_isUnitS Tf (B w c) (hB w c)))]
  have ht : trEvS Tf c (φ ((D.fm u).til c)) = 0 := by rw [hq, ← hc, h0, map_zero]
  funext s'
  let ga : GL (Fin (D.R.N D.R.m)) D.host.E := (Tf.til.ga c).1
  have hy := congrFun ht (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').tr (atInf (embT D) (ga : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga))
  simp only [trEvS, LinearMap.smul_apply, LinearMap.funLeft_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hy
  have hback : (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').tr (atInf (embT D) (ga : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga)).tr
      (atInf (embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E)) (isUnit_det_atInf (embT D) ga⁻¹) =
      (Tf.val D.R.m le_rfl (Or.inr rfl)).eY s' := by
    apply Subtype.ext
    funext τ
    show atInf (embT D) ((ga⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
      (atInf (embT D) (ga : Matrix _ _ D.host.E) τ * ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').1 τ) = ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s').1 τ
    have h1 := atInf_mul_inv (embT D) ga⁻¹ τ
    rw [inv_inv] at h1
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hback, Equiv.symm_apply_apply] at hy
  exact (mul_eq_zero.mp hy).resolve_left (Units.ne_zero _)

omit hB in

structure PendRestS (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c)))
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMTS Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))).re

theorem brExists_of_restS (hL : LowerSymmetricCompatible Tf)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : PendRestS Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  brExists_of_tiedS Tf hL B gP
    { coM_mem := coM_mem_ofS Tf B hB, coM_inj := coM_inj_ofS Tf B hB, coP_mem := coP_mem_of_isUnit_det' Tf B hB,
      coP_inj := coP_inj_of_isUnit_det' Tf B hB, exP := h.exP, lat_co := h.lat_co, pt_co := h.pt_co, ipV_co := h.ipV_co,
      re_petersson_self_eq_sum_coord := h.re_petersson_self_eq_sum_coord }

end Cl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem brTen_blkRowS (Tf : FormsTiedSym D u Ch chOf) (G : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brTen D u (blkRow (fun τ => ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (G τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
              Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose) P) =
      blkRow (fun τ => (G τ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose) (Formalism.L2.Ker.brTen D u P) := by
  have hS : ∀ τ, Formalism.L2.Col.Br.SameShift (lamTr D u τ) (sgTr D u τ) :=
    fun τ => Formalism.L2.Ker.sameShiftTr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)
  rw [blkRow_eq_blk, blkRow_eq_blk]
  unfold Formalism.L2.Ker.brTen
  rw [Formalism.L2.Ker.ta_blk_comp, Formalism.L2.Ker.ta_blk_comp]
  have e : (fun τ => ⇑(Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) ∘ₗ
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := D.R.N D.R.m) ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (G τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
        Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose).toLinearMap)) =
      fun τ => ⇑((Formalism.GradedWeylDivisibility.rowAct ℂ (n := D.R.N D.R.m - 1) (G τ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose).toLinearMap ∘ₗ
        Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) := by
    funext τ f
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    exact brOne_rowAct (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (hS τ) (G τ) f
  rw [e]

theorem shift_lamT_sgTS (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) :
    shiftOf (lamT u D.R.m) τ = shiftOf (sgT u) τ := by
  have hS : Formalism.L2.Col.Br.SameShift (lamTr D u τ) (sgTr D u τ) :=
    Formalism.L2.Ker.sameShiftTr D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N D.R.m = D.R.k + D.R.m * (D.R.t + 1) := rfl
  have h1 : 0 < D.R.N D.R.m := by omega
  have h2 : 0 < D.R.N D.R.m - 1 := by omega
  have hS' : (sgTr D u τ).detShift = (lamTr D u τ).detShift := hS
  unfold lamTr sgTr at hS'
  rw [detShift_wSh _ _ h1, detShift_wSh _ _ h2] at hS'
  simp only [shiftOf, lamT, sgT]
  rw [detShift_shW _ _ h1, detShift_shW _ _ h2]
  unfold cTw at hS'
  omega

theorem exP_ofS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) :
    ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPTS Tf B w z c = Formalism.L2.Ker.brTen D u (coMTS Tf B w c (φ ((D.fm u).til c))) := by
  intro w φ hφ c
  obtain ⟨P, hP, hv⟩ := val_repS Tf φ hφ c
  refine ⟨P, hP, hv, fun z hz => ?_⟩
  have hBc := hB w c
  have hU1 := atInf_inv_isUnit _ hBc
  have hbZ := bZ_isUnitS Tf
  have hbZg := bZg_isUnitS Tf (B w c) hBc
  have hU2 := atInf_inv_isUnit _ hbZg

  have hL : coPTS Tf B w z c = (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
      (atInf (embT D) (B w c)⁻¹ τ)⁻¹).det ^ shiftOf (sgT u) τ) •
      blkRow (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
        (atInf (embT D) (B w c)⁻¹ τ)⁻¹) (Formalism.L2.Ker.brTen D u P) := by
    have e1 : coPTS Tf B w z c = fnInv (gramC (gramP D) (embT D)) (shiftOf (sgT u)) (atInf (embT D) (B w c)⁻¹) (Tf.valP.eW z c) := by
      simp only [coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
        LinearEquiv.coe_coe]
    rw [e1, hz, fnOf_change _ _ (atInf (embT D) (B w c)⁻¹) 1 hU1, fnInv_fnOf _ _ _ hU1]

  have hM : trEvS Tf c (φ ((D.fm u).til c)) = fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P := by
    funext y
    rw [trEv_eqS, hv, Equiv.apply_symm_apply]
  have hR : coMTS Tf B w c (φ ((D.fm u).til c)) = (∏ τ, (atInf (embT D) (bZ u Tf.til.z0)⁻¹ τ *
      (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹).det ^ shiftOf (lamT u D.R.m) τ) •
      blkRow (fun τ => atInf (embT D) (bZ u Tf.til.z0)⁻¹ τ * (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹) P := by
    simp only [coMTS, LinearMap.coe_comp, Function.comp_apply]
    rw [hM, mZ, fnOf_change _ _ (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) (atInf (embT D) (bZ u Tf.til.z0)⁻¹) hU2,
      fnInv_fnOf _ _ _ hU2]
  have hKm : (fun τ => atInf (embT D) (bZ u Tf.til.z0)⁻¹ τ * (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ)⁻¹) =
      fun τ => ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (glT (B w c) hBc τ) : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ).transpose := by
    funext τ
    rw [embGL_glT, atInf_inv_inv _ hbZg, bZg_eq_mul]
    show (bZ u Tf.til.z0)⁻¹.map (embT D τ) * (bZ u Tf.til.z0 * dgE (B w c)).map (embT D τ) = _
    rw [← Matrix.map_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbZ, Matrix.one_mul]
  have hKp : (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) τ *
      (atInf (embT D) (B w c)⁻¹ τ)⁻¹) = fun τ => ((glT (B w c) hBc τ : GL (Fin (D.R.N D.R.m - 1)) ℂ) : Matrix _ _ ℂ).transpose := by
    funext τ
    rw [glT_val, Matrix.transpose_transpose, Pi.one_apply, Matrix.one_mul, atInf_inv_inv _ hBc]
    rfl
  rw [hL, hR, hKm, hKp, map_smul, brTen_blkRowS Tf]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := congrFun hKm τ
  have h2 := congrFun hKp τ
  rw [h1, h2, shift_lamT_sgTS Tf τ, embGL_glT, glT_val, Matrix.det_transpose]
  unfold dgE
  rw [Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.det_submatrix_equiv_self, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_transpose]

structure RestrictionSymmetric (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMTS Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPTS Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMTS Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPTS Tf B w z c))).re

theorem pendRest_ofS (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionSymmetric Tf B gP) :
    PendRestS Tf B gP :=
  ⟨exP_ofS Tf B hB, h.lat_co, h.pt_co, h.ipV_co, h.re_petersson_self_eq_sum_coord⟩


theorem brExists_of_rest4S (Tf : FormsTiedSym D u Ch chOf) (hL : LowerSymmetricCompatible Tf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det)
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) (h : RestrictionSymmetric Tf B gP) :
    ∃ P : Pend D u, ArchimedeanSignatureMatching P :=
  brExists_of_restS Tf B hB hL gP (pendRest_ofS Tf B hB gP h)

theorem weightedInner_self_eq_sum_coords_of_orthonormal' (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsUnit (B w c).det) (o : FrP D) (ho : o.IsON) :
    ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
      (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c))
        (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c))).re := by
  classical
  intro w z hz
  have hQ : ∀ c, blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c) ∈ Formalism.L2.Forms.CSpan (D.fm u).sg := by
    intro c
    have h0 := coP_mem_of_isUnit_det' Tf B hB w z hz c
    rw [← cspan_sgTr] at h0
    have h1 := Formalism.L2.Ker.lc_blk_sqAct_mem _ (gPof B hB o w c) _ h0
    rw [cspan_sgTr] at h1
    exact h1
  have hE : ∀ c, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹)
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gPof B hB o w c τ)) (coPTS Tf B w z c)) := by
    intro c
    obtain ⟨Q, _, hq⟩ := eW_repS Tf (B w c) (hB w c) z hz c
    have hc : coPTS Tf B w z c = Q := by
      simp only [coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
        LinearEquiv.coe_coe]
      rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (hB w c))]
    have hs : shiftOf (sgT u) = fun τ => (sgTr D u τ).detShift := funext fun τ => (shift_sgTr τ).symm
    rw [hc, hq, hs, fnOf_sqAct _ (sgTr D u) (atInf (embT D) (B w c)⁻¹) o.1 o.2 _ (fun τ => rfl)]
  rw [Tf.valP.ipP o ho z z _ _ hQ hQ hE hE, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ)⁻¹ = (((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  rfl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG

section Gen

variable {A : Type} [CommRing A]

theorem hform_reindexB {m n : Type} [Fintype m] [Fintype n] (σ : A →+* A) (e : m ≃ n) (J : Matrix m m A) (x y : m → A) :
    hform σ (J.reindex e e) (x ∘ e.symm) (y ∘ e.symm) = hform σ J x y := by
  unfold hform
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem hform_smul_leftB {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A) (s : A) (x y : n → A) :
    hform σ J (s • x) y = σ s * hform σ J x y := by
  unfold hform
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_rightB {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A) (s : A) (x y : n → A) :
    hform σ J x (s • y) = s * hform σ J x y := by
  unfold hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gramOf_apply {m n : Type} [Fintype m] [Fintype n] (σ : A →+* A) (M : Matrix m n A) (J : Matrix m m A) (a b : n) :
    ((M.map σ)ᵀ * J * M) a b = hform σ J (fun k => M k a) (fun k => M k b) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hform, Finset.sum_mul]
  rw [Finset.sum_comm]

end Gen

variable (D : D7)

abbrev crdM : (D.sp.X D.R.m).V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E) :=
  letI := D.host.cmStar
  (D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm)

abbrev crdP : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  letI := D.host.cmStar
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)

theorem hform_frame (S : @HSpace D.host.E _ _ D.host.cmStar) (v w : S.V) :
    hform (sigD D : D.host.E →+* D.host.E) S.gram (S.frame.equivFun v) (S.frame.equivFun w) = S.hT v w := by
  letI := D.host.cmStar
  rw [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.hT_expand]
  unfold hform
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, mul_assoc]
  rfl

theorem hform_crdM (v w : (D.sp.X D.R.m).V) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (crdM D v) (crdM D w) = (D.sp.X D.R.m).hT v w := by
  letI := D.host.cmStar
  have e : ∀ x, crdM D x = (D.sp.X D.R.m).frame.equivFun x ∘ (finCongr (rankN D D.R.m le_rfl)).symm := fun x => rfl
  rw [e, e]
  unfold gramN
  rw [hform_reindexB, hform_frame]

theorem hform_crdP (v w : D.sp.X'.V) :
    hform (sigD D : D.host.E →+* D.host.E) (gramP D) (crdP D v) (crdP D w) = D.sp.X'.hT v w := by
  letI := D.host.cmStar
  have e : ∀ x, crdP D x = D.sp.X'.frame.equivFun x ∘ (finCongr (rankP D)).symm := fun x => rfl
  rw [e, e]
  unfold gramP
  rw [hform_reindexB, hform_frame]

theorem iXc_eq (x : Fin (D.R.N D.R.m - 1) → D.host.E) : iXc D x = crdM D (D.sp.iX' ((crdP D).symm x)) := rfl

theorem zc_eq : zc D = crdM D D.sp.z := rfl

theorem hform_iXc (x y : Fin (D.R.N D.R.m - 1) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (iXc D y) =
      hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
  letI := D.host.cmStar
  rw [iXc_eq, iXc_eq, hform_crdM, D.sp.iX'_isom, ← hform_crdP, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem hform_iXc_zc (x : Fin (D.R.N D.R.m - 1) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (zc D) = 0 := by
  letI := D.host.cmStar
  rw [iXc_eq, zc_eq, hform_crdM]
  exact D.sp.z_orth _

theorem hform_zc_iXc (x : Fin (D.R.N D.R.m - 1) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (iXc D x) = 0 := by
  letI := D.host.cmStar
  rw [iXc_eq, zc_eq, hform_crdM, ← (D.sp.X D.R.m).herm.eq (D.sp.iX' _) D.sp.z, D.sp.z_orth, map_zero]

variable {D}

theorem gram_bZ {u : D.what₂.Word} (z0 : Fin (D.R.N D.R.m) → D.host.E) (hz : ∃ a : D.host.E, z0 = a • zc D)
    (hn : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 z0 = ((D.mem u).A.T : D.host.E)) :
    ((bZ u z0).map (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl * bZ u z0 =
      Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R)))
        (Matrix.fromBlocks (gramP D) 0 0 (Matrix.of fun _ _ => ((D.mem u).A.T : D.host.E)⁻¹)) := by
  obtain ⟨a, rfl⟩ := hz
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have hcol1 : ∀ i : Fin (D.R.N D.R.m - 1),
      (fun k => bZ u (a • zc D) k ((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inl i))) = iXc D (Pi.single i 1) := by
    intro i
    funext k
    have hi : (((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inl i) : Fin (D.R.N D.R.m)) : ℕ) < D.R.N D.R.m - 1 := by
      simp
    have hi' : (⟨_, hi⟩ : Fin (D.R.N D.R.m - 1)) = i := Fin.ext (by simp)
    simp only [bZ, dif_pos hi, hi', iXm, LinearMap.toMatrix'_apply]
  have hcol2 : ∀ j : Fin 1,
      (fun k => bZ u (a • zc D) k ((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inr j))) =
        (a / ((D.mem u).A.T : D.host.E)) • zc D := by
    intro j
    funext k
    have hj : ¬ (((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inr j) : Fin (D.R.N D.R.m)) : ℕ) < D.R.N D.R.m - 1 := by
      simp
    simp only [bZ, dif_neg hj, Pi.smul_apply, smul_eq_mul]
    ring
  ext x y
  obtain ⟨p, rfl⟩ := (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).surjective x
  obtain ⟨q, rfl⟩ := (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).surjective y
  rw [gramOf_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases p with i | i <;> rcases q with j | j
  · rw [hcol1, hcol1, hform_iXc, Matrix.fromBlocks_apply₁₁]
    simp [hform, Pi.single_apply]
  · rw [hcol1, hcol2, hform_smul_rightB, hform_iXc_zc, mul_zero, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [hcol2, hcol1, hform_smul_leftB, hform_zc_iXc, mul_zero, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · have ha : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (a • zc D) (a • zc D) =
        (sigD D : D.host.E →+* D.host.E) a * (a * hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (zc D)) := by
      rw [hform_smul_leftB, hform_smul_rightB]
    rw [hcol2, hcol2, hform_smul_leftB, hform_smul_rightB, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, map_div₀, map_natCast]
    rw [ha] at hn
    rw [show (sigD D : D.host.E →+* D.host.E) a / ((D.mem u).A.T : D.host.E) * (a / ((D.mem u).A.T : D.host.E) *
      hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (zc D)) =
      ((sigD D : D.host.E →+* D.host.E) a * (a * hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (zc D))) /
        (((D.mem u).A.T : D.host.E) * ((D.mem u).A.T : D.host.E)) by ring, hn]
    field_simp

end Formalism.L2.GlobalTheoryTheory.Br
end
end
