import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivMulConst
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ActsAwayNbar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAway
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FTfact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WopTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocFactPf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussO
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLaw
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VacKOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenC
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GramXDiag
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussN
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFactPf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilThetaConvergence.WeilThetaConvergenceOfSiegelSet

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {D : D7} {n : ℕ}

theorem pLaw (hN : LawN) (hMul : LocMul) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}
    (hL : IsLocFact ω τ fr ι L) {e : ℤ}
    (hLev : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f)
    (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (Z : Matrix (Fin n) (Fin n) ℂ)
    (hG : IsSch (gZf ε (tLoc l τ) (cLoc l τ) Z)) :
    L q (gZf ε (tLoc l τ) (cLoc l τ) Z) = fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) q Z *
      gZf ε (tLoc l τ) (cLoc l τ) (actZ q Z) u := by
  obtain ⟨hA, hDd, hb⟩ := siegelP_data q hq
  have hAh : IsUnit ((mR q).toBlocks₁₁ᴴ).det := by rw [Matrix.det_conjTranspose]; exact hA.star
  set q1 := mkGR (nU ((mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ)) (by rw [det_nU]; exact one_ne_zero) (inG_nU hb)
  set q2 := mkGR (mM (mR q).toBlocks₁₁) (det_mM hA) (inG_mM hA)
  have hq12 : q = q1 * q2 := by
    apply GR_ext
    rw [mR_mul, mR_mkGR, mR_mkGR]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR q), hq, hDd]
    unfold nU mM
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAh]
  have h2 := hLev q2 (mR q).toBlocks₁₁ hA (mR_mkGR _ _ _) _ hG
  have hs2 : IsSch (levF e (mR q).toBlocks₁₁ (gZf ε (tLoc l τ) (cLoc l τ) Z)) := by rw [← h2]; exact hL.1 q2 _ hG
  have h1 := hN D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL q1 _ hb (mR_mkGR _ _ _) _ hs2
  have hm := hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL q1 q2 _ hG
  rw [hq12, hm, h2, h1, ← hq12]
  funext u
  simp only [levF, gZf_mul]
  rw [siegelP_actZ q hq Z, siegelP_jF q hq, cnt_add, ← chN_mul_gZf ε (abs_tLoc l τ) _ _ hb u]
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

theorem gaussLaw_of : TensInj → LawN → LawM → VacK → LocMul → GZSch → LNe → GaussLaw := by
  intro hTI hN hM hV hMul hGZ hLNe D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨e, hLev⟩ := hM D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  refine ⟨e, fun y Z hZ => ?_⟩
  have hc : 0 < cLoc l τ := by
    unfold cLoc
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hcx.hψ hcx.hθ hcx.hl τ))
  have hI := isSiegel_I (n := n)
  have hGi : IsSch (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) := hGZ V.rank n ε _ _ hc (abs_tLoc l τ) _ hI
  obtain ⟨q, hq21, hqZ⟩ := siegelOrb n Z hZ
  obtain ⟨p0, k, hyq, hp0, hk⟩ := iwaGR n (y * q)
  have e1 := pLaw hN hMul hcx hL hLev q hq21 (Complex.I • 1) hGi
  rw [hqZ] at e1
  set p := cnt (epsT (tLoc l τ) ε) true
  set p' := cnt (epsT (tLoc l τ) ε) false
  have hjq : jF e p p' q (Complex.I • 1) ≠ 0 := by
    rw [siegelP_jF q hq21]
    obtain ⟨hA, -, -⟩ := siegelP_data q hq21
    exact mul_ne_zero (zpow_ne_zero _ hA.ne_zero) (zpow_ne_zero _ (hA.star).ne_zero)
  have hGZeq : gZf ε (tLoc l τ) (cLoc l τ) Z =
      fun u => (jF e p p' q (Complex.I • 1))⁻¹ * L q (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) u := by
    funext u
    rw [e1]
    field_simp
  have hVk := hV D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL e hLev k hk
  simp only [vac] at hVk
  rw [hGZeq, locLin hTI hcx hL y _ (hL.1 q _ hGi),
    ← hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y q _ hGi, hyq,
    hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL p0 k _ hGi, hVk, locLin hTI hcx hL p0 _ hGi,
    pLaw hN hMul hcx hL hLev p0 hp0 (Complex.I • 1) hGi]
  have cy := (cocycleZ n e p p' y q (Complex.I • 1) hI).2.2.2
  have cp := (cocycleZ n e p p' p0 k (Complex.I • 1) hI).2.2.2
  rw [hqZ] at cy
  rw [actZ_K hk] at cp
  rw [hyq] at cy
  have hact : actZ p0 (Complex.I • 1) = actZ y Z := cp.1.symm.trans cy.1
  have hrel : jF e p p' y Z * jF e p p' q (Complex.I • 1) = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) :=
    cy.2.symm.trans cp.2
  have hjy : jF e p p' y Z = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) * (jF e p p' q (Complex.I • 1))⁻¹ := by
    rw [← hrel]; field_simp
  funext u
  rw [hact, hjy]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem tensInj_of : AwayIn → TensInj := by
  intro hAI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC f g h
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have hcls := hAI D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr (LocLawH.cx_lne hC) _ hΨ
  exact LocLawH.tens_cancel hσ V l s τ hC.hfr.1 (h _ hcls)

theorem lawN_of : UnipTau → TensInj → LawN := by
  intro hU hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL y b hb hy f hf
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ f hf]
  funext x
  rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y b hb hy]
  simp only [tens, chN]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem weight_factor_eq_automorphy (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y = jF e p q y (Complex.I • 1) := by
  simp only [F0, f0, jF, u1, u2, conj_I_smul_one, Matrix.mul_neg, mul_I_smul_one]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

theorem lawM_of : TensInj → LawM := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  refine ⟨k - j, fun y a ha hy f hf => ?_⟩
  set A : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a ha.ne_zero with hAdef
  have hAv : A.1 = a := rfl
  have hAi : (A⁻¹).1 = a⁻¹ := by rw [Matrix.coe_units_inv, hAv]
  have hyA : y = LocLawH.mOf A := by
    apply GR_ext
    rw [hy, LocLawH.mR_mOf, hAv, hAi, Matrix.conjTranspose_nonsing_inv]
    rfl
  have hy0 : (mR (LocLawH.mOf A)).toBlocks₂₁ = 0 := by simp [LocLawH.mR_mOf]
  have haOf : LocLawH.aOf (LocLawH.mOf A) hy0 = A := Units.ext (by rw [LocLawH.aOf_val, LocLawH.mR_mOf]; simp)
  have hsc := LocLawH.scal hC.hθ hσ k j hk hj (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false)
    (cnt_add _) (LocLawH.mOf A) hy0
  rw [haOf] at hsc
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ f hf]
  funext x
  rw [hyA, hC.hω.levi _ (LocLawH.unitAt hσ τ A) (LocLawH.mat_mOf hσ hC.hι A), hsc, weight_factor_eq_automorphy,
    siegelP_jF _ hy0, cnt_add]
  have hbl : (mR (LocLawH.mOf A)).toBlocks₁₁ = a := by rw [LocLawH.mR_mOf]; simp [hAv]
  rw [hbl]
  have hΨx : Ψ (HMul.hMul x (LocLawH.unitAt hσ τ A).1 : Mx D V.rank n) = Ψ x := by
    refine hΨ.1 _ _ (fun τ' h => ?_) ?_
    · rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_ne hσ h, Matrix.mul_one]
    · rw [LocLawH.unitAt_val, Matrix.map_mul, LocLawH.finite_part_adelic_point_matrix hσ, Matrix.mul_one]
  simp only [tens, hΨx, levF]
  rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_matrix hσ, hAv, ← Matrix.mul_assoc]
  have hof : (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) = fr⁻¹ * compAt θ τ x := rfl
  rw [hof]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem locMul_of : TensInj → LocMul := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y y' f hf
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx _ _ fun Ψ hΨ => ?_
  have hf' := hL.1 y' f hf
  rw [← hL.2 (y * y') Ψ hΨ f hf, ← hL.2 y Ψ hΨ _ hf', map_mul, map_mul, Module.End.mul_apply]
  congr 2
  apply Subtype.ext
  exact hL.2 y' Ψ hΨ f hf

end PositivityTheory.Rg.Sw.Glob
end
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem gaussLaw_of' (hV : VacK) (hG : GZSch) : GaussLaw := by
  have hT : TensInj := tensInj_of awayIn
  exact gaussLaw_of hT (lawN_of unipTau hT) (lawM_of hT) hV (locMul_of hT) hG lNe

end PositivityTheory.Rg.Sw.Glob
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.NbarH

variable {m n : ℕ}

theorem ftLoc_const_mul (ε : Fin m → Bool) (s : ℝ) (k : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε s (fun v => k * g v) u = k * ftLoc ε s g u := by
  unfold ftLoc
  simp_rw [mul_assoc]
  exact MeasureTheory.integral_const_mul k _

theorem ftLoc_const_mul' (ε : Fin m → Bool) (s : ℝ) (k : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) :
    ftLoc ε s (fun v => k * g v) = fun u => k * ftLoc ε s g u := funext fun u => ftLoc_const_mul ε s k g u

theorem sigR_sq (ε : Fin m → Bool) (a : Fin m) : (VacC.sigR ε a : ℂ) ^ 2 = 1 := by
  unfold VacC.sigR; split_ifs <;> norm_num

theorem ftLoc_vac (ε : Fin m → Bool) (t c s : ℝ) (hc : 0 < c) (hs : s ^ 2 = c ^ 2) :
    ftLoc ε s (vac ε t c) = fun u => ((Real.pi : ℂ) / c) ^ (m * n) * vac (n := n) ε t c u := by
  funext u
  have hs' : (s : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast hs
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [VacC.ftLoc_eq, VacC.vac_eq, VacS.ftG_DG _ _ _ _ (fun a j => by simpa using hc)]
  have hγ : (fun (a : Fin m) (j : Fin n) => (s : ℂ) ^ 2 * ((VacC.sigR ε a : ℝ) : ℂ) ^ 2 / (c : ℂ)) = fun _ _ => (c : ℂ) := by
    funext a j
    rw [sigR_sq, hs']
    field_simp
  rw [hγ]
  simp only [VacS.DG, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul]
  rw [← pow_mul, mul_comm n m]

end PositivityTheory.Rg.Sw.Glob.NbarH
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open NbarH GaussH

theorem lawNbar_of (hU : UnipTau) (hW : WEx) (hF : FTfact) (hTI : TensInj) (hLNe : LNe) : LawNbar := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL y c hc hyc f hf
  have htc : |tLoc l τ| = cLoc l τ := abs_tLoc l τ
  have hc0 : 0 < cLoc l τ := by
    unfold cLoc
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hC.hψ hC.hθ hC.hl τ))
  have hsq : (tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [← htc, sq_abs]
  have hsq' : (-tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [neg_sq, hsq]
  obtain ⟨w, hw⟩ := hW D n
  have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
  obtain ⟨yn, hyn⟩ := OG.exists_nU n (-c) hc'
  have hιy : ι y = w * ι yn * w⁻¹ := by rw [OG.iota_conj hC.hθ hC.hι w hw y yn c hyc hyn]; group
  obtain ⟨κ, A, A', hκ, hFT⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC w hw
  have hvS : IsSch (vac (n := n) ε (tLoc l τ) (cLoc l τ)) := gZSch V.rank n ε _ _ hc0 htc _ isSiegel_I
  set K : ℂ := ((Real.pi : ℂ) / (cLoc l τ)) ^ (V.rank * n) with hK
  have hK0 : K ≠ 0 := pow_ne_zero _ (div_ne_zero (by exact_mod_cast Real.pi_pos.ne') (by exact_mod_cast hc0.ne'))
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
  have kA := hFT (A' Ψ) hA'Ψ

  have hid : ∀ g (hg : IsSch g), tens θ τ fr g Ψ =
      tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ) (fun v => κ⁻¹ * ftLoc ε (-tLoc l τ) g v) u) (A (A' Ψ)) := by
    intro g hg
    have h1 : ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ =
        ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) g u) (A' Ψ), hA'Ψ.2 _ ((hFΨ g hg).2.1)⟩ :=
      Subtype.ext (hFΨ g hg).2.2.2
    have h2 := (kA.2.2 _ ((hFΨ g hg).2.1)).2.2.1
    have h3 : ω w (ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩) = ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h1] at h3
    rw [← h2, h3]
  have hAA : ∀ x, A (A' Ψ) x = (K * K)⁻¹ * Ψ x := by
    intro x
    have h := congrFun (hid _ hvS) x
    simp only [tens, ftLoc_vac ε _ _ _ hc0 hsq', ftLoc_const_mul', ftLoc_vac ε _ _ _ hc0 hsq] at h
    have hv0 : vac (n := n) ε (tLoc l τ) (cLoc l τ) (fr⁻¹ * compAt θ τ x) ≠ 0 := Complex.exp_ne_zero _
    have hκ' : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
    field_simp at h
    rw [h, hK]
    field_simp

  rw [← hL.2 y Ψ hΨ f hf]
  have hE : IsSch (fun u => chN ε (tLoc l τ) (-c) u * (κ⁻¹ * ftLoc ε (-tLoc l τ) f u)) :=
    OpGenAH.isSch_phase ε (tLoc l τ) (-c) hc' (hFΨ f hf).2.1
  have s1 : ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ =
      ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ), hA'Ψ.2 _ ((hFΨ f hf).2.1)⟩ :=
    Subtype.ext (hFΨ f hf).2.2.2
  have s2 : ω (ι yn) ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ), hA'Ψ.2 _ ((hFΨ f hf).2.1)⟩ =
      ⟨tens θ τ fr (fun u => chN ε (tLoc l τ) (-c) u * (κ⁻¹ * ftLoc ε (-tLoc l τ) f u)) (A' Ψ), hA'Ψ.2 _ hE⟩ := by
    apply Subtype.ext
    funext x
    rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC yn (-c) hc' hyn]
    simp only [tens, chN, mul_assoc]
  have s3 := (kA.2.2 _ hE).2.2.1
  rw [hιy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, s1, s2, s3]
  funext x
  simp only [tens]
  rw [hAA x]
  have hKK : ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) = (K * K)⁻¹ := by
    rw [hK, htc, ← pow_two, ← pow_mul, ← inv_pow, inv_div]
    push_cast
    ring_nf
  rw [hKK]
  have hκ' : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  have e : (fun v => chN ε (tLoc l τ) (-c) v * (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)) =
      fun v => κ⁻¹ * (chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v) := by funext v; ring
  rw [e, ftLoc_const_mul']
  linear_combination (ftLoc ε (tLoc l τ) (fun v => chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v)
    (fr⁻¹ * compAt θ τ x)) * (K * K)⁻¹ * Ψ x * hκ'

end PositivityTheory.Rg.Sw.Glob
end
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem gaussian_law_of_weil (hW : WEx) (hF : FTfact) : GaussLaw :=
  gaussLaw_of' (vacK_of gZSch (lawN_of unipTau (tensInj_of awayIn))
    (lawNbar_of unipTau hW hF (tensInj_of awayIn) lNe) (locMul_of (tensInj_of awayIn)) lNe) gZSch

end PositivityTheory.Rg.Sw.Glob
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem gaussLaw : GaussLaw := gaussian_law_of_weil wEx fTfact

end PositivityTheory.Rg.Sw.Glob
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem awayAct_gen (hG : GenA) : AwayAct := awayAct_of hG fTfact decompAway

theorem locFact : LocFact := locFact_of decomp (opGen_of fTfact)

theorem localRepresentationL2 : LocalL2Isometry := local_L2_isometry fTfact

theorem gIdil_gen (h : GlobalTheory.Published.WeilThetaConvergence) (hG : GenA) : GIdil :=
  gIdil_of h gZSch decompAway (awayAct_gen hG) locFact gaussLaw awayIn localRepresentationL2

end PositivityTheory.Rg.Sw.Glob
end
