import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.ProjVar.Var

namespace GlobalTheory.ProjVar

def cxStage (F : Type) [Field F] [NumberField F] : TrueGeo.CxSt F where
  borel _ _ := inferInstance
  vol := vol
  FnC := FnC
  cx := cx
  cx_smul := cx_smul
  Met := Met
  mAdd Y σ Δ Δ' := mAdd Y σ Δ Δ'
  mPow Y σ Δ := mPow Y σ Δ
  fsMet Y σ Δ := fsMet Y σ Δ
  pn Y σ Δ := pn Y σ Δ
  pnK Y σ Δ := pnK Y σ Δ
  mSmooth Y σ Δ := mSmooth Y σ Δ
  mPsh Y σ Δ := mPsh Y σ Δ
  redZero Y σ Δ := redZero Y σ Δ
  agreeOn Y σ Δ := agreeOn Y σ Δ
  resNorm Y σ Δ := Var.resNorm Y σ Δ
  regOn Y σ Δ := regOn Y σ Δ
  ofWeight Y σ Δ L r := Var.ofWeight Y σ Δ L r
  pn_ofWeight Y σ Δ L r h φ f y i hi _ := by rw [Var.pn_ofWeight h φ (mem_ptsIn.2 hi), fval_cx]
  pn_mAdd Y σ Δ Δ' m m' f f' y h h' := by
    rw [map_mul, Var.pn_mAdd (secReg_cx_iff.2 h) (secReg_cx_iff.2 h')]
  pn_mPow Y σ Δ k m f y h := by rw [map_pow, Var.pn_mPow (secReg_cx_iff.2 h.regularAt)]
  pn_mul Y σ Δ m a f y ha h := by
    rw [map_mul, Var.pn_mul (regC_cx_iff.2 ha) (secReg_cx_iff.2 h), val_cx]
  pn_fs Y σ Δ ι κ _ _ b X f y g hg hb _ _ := by
    have e (k) := hasVal_sum_smul (y := y) hg (fun i => secReg_cx_of_mem (hb i) y) fun i => X i k
    rw [pn_fsMet (fun k => (secReg_iff hg).2 (e k).regC) hg, fval_cx]
    simp only [fval, fun k => (e k).val_eq, ← map_mul, val_cx]

end GlobalTheory.ProjVar
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.CxPts Formalism.BasicNotions

namespace GlobalTheory.ProjVar.Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv}

end GlobalTheory.ProjVar.Var

namespace GlobalTheory.TrueGeo

def cxSt (F : Type) [Field F] [NumberField F] : CxSt F := ProjVar.cxStage F

variable {F : Type} [Field F] [NumberField F]



variable {Y : Var F} {σ : F →+* ℂ} {Δ Δ' : Y.Dv}

example (n : ℕ) (y : Pts (proj F n) σ) : (cxSt F).mSmooth _ σ _ (projMet F σ n) ∧
    ∑ j, (cxSt F).pn _ σ _ (projMet F σ n)
      ((cxSt F).cx _ σ ((proj F n).coordFn (proj_gen_mem F n 0) j)) y = 1 ∧
    ((cxSt F).pn _ σ _ (projMet F σ n) ((cxSt F).cx _ σ 1) y = 0 ↔
      under y ∈ (proj F n).supp (projHyp F n)) := by
  have hy := (mSmooth_projMet F σ n).1 (mem_univ y)
  have he : (projHyp F n).Eff := (proj F n).eff_hyp _
  exact ⟨mSmooth_projMet F σ n, sum_pn_fsMet hy,
    ((pn_eq_zero_iff hy (secReg_cx_iff.2 (he _))).trans secZero_cx_iff).trans he.mem_supp_iff.symm⟩

example (c : ℂ) (y : Pts Y σ) :
    (cxSt F).pn Y σ 0 ((cxSt F).fsMet Y σ 0 fun _ : Unit => c • (cxSt F).cx Y σ 1)
      ((cxSt F).cx Y σ 1) y = 1 / ‖c‖ ^ 2 := by
  have hg : y ∈ eqnSet σ (0 : Y.Dv) 1 := isEqn_zero _
  have h₁ : HasVal y (Y.cx σ 1) 1 := map_one (Y.cx σ) ▸ hasVal_one
  change pn Y σ 0 (fsMet Y σ 0 fun _ : Unit => c • Y.cx σ 1) (Y.cx σ 1) y = _
  rw [pn_fsMet (fun _ => ⟨1, hg, ((h₁.smul c).mul h₁).regC⟩) hg, fval_one, h₁.val_eq]
  simp only [fval_one, (h₁.smul c).val_eq]
  simp

example : ¬ (cxSt F).mSmooth Y σ Δ ((cxSt F).fsMet Y σ Δ (k := Empty) Empty.elim) := fun h =>
  have ⟨y⟩ := nonempty_pts (Y := Y) (σ := σ)
  have ⟨k, _⟩ := (mSmooth_fsMet_iff.1 h y).2
  k.elim

end GlobalTheory.TrueGeo
end
end
