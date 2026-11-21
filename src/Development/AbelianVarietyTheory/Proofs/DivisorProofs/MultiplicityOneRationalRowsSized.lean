import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertJunkColIn3
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormsBasisInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneGivesLiftDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneGivesUnitEquivStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefinitePositivityBothLevelsShortList
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPositiveScalarsBasePlace

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem iC_principal_injective : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → (R.toCx3 F).zs.InBlock → ∀ t, Function.Injective ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F _hOk hC _hIB t
  have hj : GlobalTheory.QPosCompare.IsForm ((R.toCx3 F).jR t) :=
    GlobalTheory.TwistPlacesObj.isForm_tw _ R.toRealDat.emb0 (GlobalTheory.QPosCompare.isForm_jX hC.base.models t)
  exact GlobalTheory.TwistPlacesObj.lin_injective ((R.toCx3 F).Θ t) hj
    ((A3.A.fam.R t).toF (A3.A.fam.lvl ⊥ 1) ((R.toCx3 F).zs.Z t))
    (BlockDat.toF_injective _ _ _) (fun y => GlobalTheory.TwistPlacesObj.toF_mem _ _ _ y)

end GlobalTheory.PrimIn
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_complexCoords_principalLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → (R.toCx3 F).zs.InBlock → ∀ t, Function.Injective ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) := by
  atlas_forward_decl GlobalTheory.PrimIn.iC_principal_injective
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem theta_Z_mem_range_iC {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type}
    {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hIB : X.zs.InBlock) (t : A3.fam3.base3.Tup) :
    ∀ z ∈ X.Z t, X.Θ t (X.jR t z) ∈ LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) := by
  intro z hz
  have h1 : z ∈ (A3.A.fam.R t).ZHg A3.A.fam.X := hIB.1 t hz
  obtain ⟨x, hx⟩ := GlobalTheory.PrincipalRows.mem_range_toF_full (A3.A.fam.R t) A3.A.fam.X (X.zs.Z t) z hz h1.2
  refine ⟨cpt A3.A.v0.embedding x, ?_⟩
  have h3 := GlobalTheory.OneForm.iC_cpt X (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t x
  refine h3.trans ?_
  exact congrArg (fun y => X.Θ t (X.jR t y)) hx

set_option maxHeartbeats 1000000 in

theorem iC_range_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ t, LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) = ⊤ := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F _hOk hC hUp hRT hIB t
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hC.base.models
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hC.base.models
  have hmem := GlobalTheory.PrincipalRows.theta_adjoint_mem (R.toCx3 F) F.cv hKR hJR hRT t
    (LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t))
    (theta_Z_mem_range_iC A3 (R.toCx3 F) hIB t)
  have hinj : Function.Injective (LinearMap.adjoint ((R.toCx3 F).Θ t)) := by
    show Function.Injective (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.Th t)))
    rw [Tw.adjoint_map]
    intro x y hxy
    exact hUp t hxy
  have hinj2 : Function.Injective ((R.toCx3 F).Θ t ∘ₗ LinearMap.adjoint ((R.toCx3 F).Θ t)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    have h0 : LinearMap.adjoint ((R.toCx3 F).Θ t) e = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_left]
      have : (R.toCx3 F).Θ t (LinearMap.adjoint ((R.toCx3 F).Θ t) e) = 0 := he
      rw [this, inner_zero_right]
    exact hinj (h0.trans (map_zero _).symm)
  have hsurj := LinearMap.injective_iff_surjective.mp hinj2
  rw [eq_top_iff]
  intro e _
  obtain ⟨e', rfl⟩ := hsurj e
  exact hmem e'

end GlobalTheory.PrimIn
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexCoords_principalLevel_range_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ t, LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) = ⊤ := by
  atlas_forward_decl GlobalTheory.PrimIn.iC_range_eq_top
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.PrimIn

theorem principalLevel_rows_bijective_of_parts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → R.PrincipalLevelBijective F := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hOk hW hUp hRow hIn
  have hinj := GlobalTheory.T.injective_complexCoords_principalLevel R F hOk hW hIn
  have htop := GlobalTheory.T.complexCoords_principalLevel_range_eq_top R F hOk hW hUp hRow hIn
  refine ⟨hinj _, fun t => ⟨hinj t, ?_⟩⟩
  rw [htop t, htop _]

end GlobalTheory.PrimIn
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.Stage2

theorem stage2 : Hypotheses3 → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) ∧ (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) ∧ R.PrincipalLevelBijective F := by
  intro P eps heps
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := GlobalTheory.Published.siegelEisensteinContinuation_of_doublingMethod P.q9
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.definite_positivity_both_levels_short_list P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q12 eps heps
  refine ⟨x₀, ?_⟩
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F L hLe hLx hSz hPar hT hM hRow
  obtain ⟨pV⟩ := hPar
  obtain ⟨_hGiven, _hGS, _hCD, _hLI, hTR, hUI, _hUIW⟩ := GlobalTheory.T.multiplicity_one_gives_lift_data P R F hT hM
  obtain ⟨_hOk, _hGU, hGE, hBlk, _hA, _hB⟩ := GlobalTheory.T.multiplicity_one_gives_unit_equiv P R F hT hM
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hPos : ∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos :=
    hx₀ (s := 1) R F L pV hLe hLx hSz hT.ok hT.char hT.ex hT.host hT.ccK hT.guard hT.types hTR hGE hBlk hRow
  have hScal := GlobalTheory.T.thetaLift_positiveScalars_basePlace P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q11 R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hTR hJ hGE hPos
  exact ⟨hPos, hScal, GlobalTheory.PrimIn.principalLevel_rows_bijective_of_parts R F hT.ok hT.char hUI hRow hBlk⟩

end GlobalTheory.Stage2
end
