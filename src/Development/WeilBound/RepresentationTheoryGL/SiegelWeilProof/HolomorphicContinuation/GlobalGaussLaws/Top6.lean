import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop2
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawB
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLaw
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRho
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVac
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoI
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFockVectorOfSchrodingerMemFockSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterPLin
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGaussIndicator
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAway
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ActsAwayNbar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WopTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFactPf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFact

section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

variable {σ : Type}

def reP (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (coeff m p).re

def imaginary (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (coeff m p).im

theorem coeff_reP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : coeff m (reP p) = (coeff m p).re := by
  classical
  unfold reP
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : coeff m p = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem coeff_imP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : coeff m (imaginary p) = (coeff m p).im := by
  classical
  unfold imaginary
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : coeff m p = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem eq_map_re_add_im (p : MvPolynomial σ ℂ) :
    p = map (algebraMap ℝ ℂ) (reP p) + C Complex.I * map (algebraMap ℝ ℂ) (imaginary p) := by
  ext m
  rw [coeff_add, coeff_C_mul, coeff_map, coeff_map, coeff_reP, coeff_imP]
  apply Complex.ext <;> simp

theorem eq_zero_of_eval_real (p : MvPolynomial σ ℂ) (h : ∀ y : σ → ℝ, eval (fun i => (y i : ℂ)) p = 0) : p = 0 := by
  have hev : ∀ (y : σ → ℝ) (q : MvPolynomial σ ℝ),
      eval (fun i => (y i : ℂ)) (map (algebraMap ℝ ℂ) q) = ((eval y q : ℝ) : ℂ) := by
    intro y q
    rw [eval_map]
    change _ = (algebraMap ℝ ℂ) (eval₂ (RingHom.id ℝ) y q)
    rw [hom_eval₂]
    rfl
  have key : ∀ y : σ → ℝ, eval y (reP p) = 0 ∧ eval y (imaginary p) = 0 := by
    intro y
    have hy := h y
    rw [eq_map_re_add_im p, eval_add, eval_mul, eval_C, hev, hev] at hy
    have hre := congrArg Complex.re hy
    have him := congrArg Complex.im hy
    simp at hre him
    exact ⟨hre, him⟩
  have hr : reP p = 0 := MvPolynomial.funext fun y => by simpa using (key y).1
  have hi : imaginary p = 0 := MvPolynomial.funext fun y => by simpa using (key y).2
  rw [eq_map_re_add_im p, hr, hi]
  simp

end PositivityTheory.Rg.Sw.Glob.LocInstH
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

open MvPolynomial

def toRe (m n : ℕ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k => if k.2.2 then X (k.1, k.2.1, false) - C Complex.I * X (k.1, k.2.1, true)
    else X (k.1, k.2.1, false) + C Complex.I * X (k.1, k.2.1, true)

def ofRe (m n : ℕ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k => if k.2.2 then C (1 / (2 * Complex.I)) * (X (k.1, k.2.1, false) - X (k.1, k.2.1, true))
    else C (1 / 2) * (X (k.1, k.2.1, false) + X (k.1, k.2.1, true))

theorem ofRe_toRe {m n : ℕ} (P : PX m n) : ofRe m n (toRe m n P) = P := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hC : (C Complex.I : PX m n) * C (1 / (2 * Complex.I)) = C (1 / 2) := by
    rw [← C_mul]; congr 1; field_simp
  have hC2 : (C (1 / 2) : PX m n) + C (1 / 2) = 1 := by
    rw [← C_add, ← C_1]; congr 1; norm_num
  have : (ofRe m n).comp (toRe m n) = AlgHom.id ℂ (PX m n) := by
    apply MvPolynomial.algHom_ext
    intro k
    obtain ⟨a, i, b⟩ := k
    cases b
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, toRe, ofRe, aeval_X, map_add, map_mul, aeval_C, algebraMap_eq,
        Bool.false_eq_true, if_false, if_true]
      linear_combination (X (a, i, false) - X (a, i, true)) * hC + X (a, i, false) * hC2
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, toRe, ofRe, aeval_X, map_sub, map_mul, aeval_C, algebraMap_eq,
        Bool.false_eq_true, if_false, if_true]
      linear_combination -(X (a, i, false) - X (a, i, true)) * hC + X (a, i, true) * hC2
  exact congrArg (fun f => f P) this

theorem evX_eq_eval_toRe {m n : ℕ} (P : PX m n) (y : Fin m × Fin n × Bool → ℝ) :
    evX P (fun a i => (y (a, i, false) : ℂ) + Complex.I * (y (a, i, true) : ℂ)) =
      eval (fun k => (y k : ℂ)) (toRe m n P) := by
  have key : (aeval fun k : Fin m × Fin n × Bool => if k.2.2 then star ((y (k.1, k.2.1, false) : ℂ) + Complex.I * (y (k.1, k.2.1, true) : ℂ))
      else (y (k.1, k.2.1, false) : ℂ) + Complex.I * (y (k.1, k.2.1, true) : ℂ)) = (aeval fun k => (y k : ℂ)).comp (toRe m n) := by
    apply MvPolynomial.algHom_ext
    intro k
    obtain ⟨a, i, b⟩ := k
    cases b
    · simp [toRe]
    · simp [toRe, Complex.conj_ofReal, sub_eq_add_neg]
  unfold evX
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
  exact congrArg (fun f => f P) key

theorem evX_injective {m n : ℕ} {P Q : PX m n} (h : ∀ u, evX P u = evX Q u) : P = Q := by
  have h0 : toRe m n (P - Q) = 0 := by
    apply eq_zero_of_eval_real
    intro y
    rw [← evX_eq_eval_toRe]
    have := h (fun a i => (y (a, i, false) : ℂ) + Complex.I * (y (a, i, true) : ℂ))
    unfold evX at this ⊢
    rw [map_sub, this, sub_self]
  rw [← sub_eq_zero, ← ofRe_toRe (P - Q), h0, map_zero]

theorem fP_injective {m n : ℕ} {c : ℝ} {P Q : PX m n} (h : fP c P = fP c Q) : P = Q := by
  apply evX_injective
  intro u
  have := congrFun h u
  simp only [fP] at this
  have hg : gs c u ≠ 0 := Complex.exp_ne_zero _
  exact mul_right_cancel₀ hg this

theorem fP_smul_add {m n : ℕ} (c : ℝ) (a : ℂ) (P Q : PX m n) : fP c (a • P + Q) = a • fP c P + fP c Q := by
  funext u
  simp only [fP, evX, map_add, smul_eq_C_mul, map_mul, eval_C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.LocInstH

namespace PositivityTheory.Rg.Sw.Glob

open LocInstH

theorem locInst_of (hT : TensMem) (hl : LIl) (hlin : LIlin) (hlaw : LIlaw) (hcell : LIcell) (hcont : LIcont)
    (hrho : LIrho) (hk : LIkact) (hvac : LIvac) (hkv : LIkvac) : LocInst := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  have hl0 := hl D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨hlinL, hid⟩ := hlin D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨e, he⟩ := hlaw D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨C0, hC0, hCc⟩ := hcell D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨ρ, hρ, hfin⟩ := hrho D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  have hzero : ∀ y : GR n, L y (fP (cLoc l τ) (0 : PX V.rank n)) = 0 := by
    intro y
    have h2 := hlinL y 1 0 0
    simp only [one_smul, add_zero] at h2
    have : L y (fP (cLoc l τ) (0 : PX V.rank n)) + L y (fP (cLoc l τ) (0 : PX V.rank n)) =
        L y (fP (cLoc l τ) (0 : PX V.rank n)) + 0 := by rw [add_zero]; exact h2.symm
    exact add_left_cancel this
  let sL : PX V.rank n →ₗ[ℂ] (GR n → ℂ) :=
    { toFun := fun P => sLd L (cLoc l τ) P
      map_add' := fun P Q => by
        funext y
        have h2 := hlinL y 1 P Q
        rw [one_smul, one_smul] at h2
        simp only [sLd, Pi.add_apply, h2]
      map_smul' := fun a P => by
        funext y
        have h2 := hlinL y a P 0
        rw [add_zero, hzero y, add_zero] at h2
        simp only [sLd, Pi.smul_apply, RingHom.id_apply, h2, smul_eq_mul] }
  have hsign : ((tLoc l τ = cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε true ∧ (pqOf ε l τ).2 = cnt ε false) ∨
      (tLoc l τ = -cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε false ∧ (pqOf ε l τ).2 = cnt ε true)) := by
    unfold tLoc cLoc pqOf
    split_ifs with h
    · exact Or.inl ⟨by rw [abs_of_pos h], rfl, rfl⟩
    · have hneg : l τ < 0 := lt_of_le_of_ne (not_lt.mp h) hl0
      exact Or.inr ⟨by rw [abs_of_neg hneg]; ring, rfl, rfl⟩
  have hcpos : 0 < cLoc l τ := by
    unfold cLoc
    have := abs_pos.mpr hl0
    positivity
  have h11 : sLd L (cLoc l τ) 1 1 = 1 := by
    simp [sLd, hid, fP, evX, gs]
  have hvac' : ∀ g, sLd L (cLoc l τ) 1 g = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e g :=
    hvac V.rank n ε (cLoc l τ) (tLoc l τ) (pqOf ε l τ).1 (pqOf ε l τ).2 e hcpos hsign (sLd L (cLoc l τ) 1) C0
      (hcont D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL 1) h11 (fun y g hy => he 1 y g hy) (fun g b hb hg => hCc 1 g b hb hg)
  refine ⟨sL, ρ, (pqOf ε l τ).1, (pqOf ε l τ).2, e, ?_, ?_, fun P y => rfl, hρ⟩
  · have hs := hC.hsig
    unfold pqOf GoodSig at *
    split_ifs <;> omega
  · refine ⟨hcpos, hsign, fun P => hcont D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL P, hvac', fun P y g hy => he P y g hy,
      ⟨C0, hC0, fun P g b hb hg => hCc P g b hb hg⟩,
      fun P g k hk' => hk D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL ρ hρ P g k hk', ?_, hfin⟩
    intro k hkK
    have h1 := hkv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL e hvac' k hkK
    rw [hρ k 1 hkK] at h1
    apply fP_injective (c := cLoc l τ)
    rw [h1]
    have := fP_smul_add (cLoc l τ) (F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e k) (1 : PX V.rank n) 0
    simp only [add_zero] at this
    rw [this]
    funext u
    simp [fP, evX]

end PositivityTheory.Rg.Sw.Glob
end
end

section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

def ptX {m : ℕ} (u : Matrix (Fin m) (Fin n) ℂ) : Fin m × Fin n × Bool → ℂ := fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1

theorem evX_eq_eval {m : ℕ} (Q : PX m n) (u : Matrix (Fin m) (Fin n) ℂ) : evX Q u = eval (ptX u) Q := rfl

theorem ptX_add_smul {m : ℕ} (u w : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    ptX (u + (t : ℂ) • w) = ptX u + (t : ℂ) • ptX w := by
  funext k
  simp only [ptX, Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [Complex.conj_ofReal]

theorem gAway_add_dirAt (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (X : Matrix (Fin V.rank) (Fin n) ℂ) (t : ℝ) :
    gAway V l s τ (z + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X) = gAway V l s τ z := by
  have hz : ∀ τ', τ' ≠ τ → (z + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X) τ' = z τ' := by
    intro τ' h
    rw [Pi.add_apply, Pi.smul_apply, dirAt_ne h, smul_zero, add_zero]
  delta gAway
  beta_reduce
  congr 2
  refine Finset.sum_congr rfl fun τ' hτ' => ?_
  rw [hz τ' (by simpa using hτ')]

theorem gaussian_vacuum_add_line {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) (x : Mx D V.rank n)
    (X : Matrix (Fin V.rank) (Fin n) ℂ) (t : ℝ) :
    psi0 θ V n l s τ (x + lineAt θ τ X t) = psi0 θ V n l s τ x := by
  obtain ⟨-, hfinL, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ X
  have h1 : (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) =
      (fun τ' => compAt θ τ' x) + (t : ℂ) • GlobalTheory.FockAnnKill.dirAt τ X := by
    funext τ'
    have hadd : compAt θ τ' (x + lineAt θ τ X t) = compAt θ τ' x + compAt θ τ' (lineAt θ τ X t) := by
      ext i j
      show (θ τ') (infPart D ((x + lineAt θ τ X t) i j)) =
        (θ τ') (infPart D (x i j)) + (θ τ') (infPart D (lineAt θ τ X t i j))
      rw [show (x + lineAt θ τ X t) i j = x i j + lineAt θ τ X t i j from rfl, map_add, map_add]
    rw [hadd, hcomp t τ', Pi.add_apply, Pi.smul_apply]
    by_cases h : τ' = τ
    · rw [if_pos h, h, dirAt_self]
    · rw [if_neg h, dirAt_ne h, smul_zero]
  have h2 : (fun i j => finPart D ((x + lineAt θ τ X t) i j)) = (fun i j => finPart D (x i j)) := by
    funext i j
    have h0 : finPart D (lineAt θ τ X t i j) = 0 := congrFun (congrFun (hfinL t) i) j
    rw [show (x + lineAt θ τ X t) i j = x i j + lineAt θ τ X t i j from rfl, map_add, h0, add_zero]
  show gAway V l s τ (fun τ' => compAt θ τ' (x + lineAt θ τ X t)) *
      g0 D V.rank n (fun i j => finPart D ((x + lineAt θ τ X t) i j)) =
    gAway V l s τ (fun τ' => compAt θ τ' x) * g0 D V.rank n (fun i j => finPart D (x i j))
  rw [h1, h2, gAway_add_dirAt]

private theorem hasDerivAt_mvPolynomial_eval_line_zero {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℂ) (a v : σ → ℂ) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (a + (t : ℂ) • v) p)
      (∑ k, v k * MvPolynomial.eval a (MvPolynomial.pderiv k p)) 0 := by
  induction p using MvPolynomial.induction_on
  next r =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  next p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  next p i hp =>
    have hX : HasDerivAt (fun t : ℝ => (a + (t : ℂ) • v) i) (v i) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
      have h2 := (h1.mul_const (v i)).const_add (a i)
      simpa using h2
    have h := hp.mul hX
    simp only [map_mul, MvPolynomial.eval_X]
    refine h.congr_deriv ?_
    have hk : ∀ k, MvPolynomial.eval a (MvPolynomial.pderiv k (p * MvPolynomial.X i)) =
        MvPolynomial.eval a (MvPolynomial.pderiv k p) * a i +
          (if i = k then MvPolynomial.eval a p else 0) := by
      intro k
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        MvPolynomial.eval_X, Pi.single_apply]
      split_ifs with h
      · simp only [map_one, mul_one]
        ring
      · simp only [map_zero, mul_zero, zero_add, add_zero]
        ring
    have hs1 : ∑ k, v k * (MvPolynomial.eval a (MvPolynomial.pderiv k p) * a i) =
        (∑ k, v k * MvPolynomial.eval a (MvPolynomial.pderiv k p)) * a i := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hs2 : ∑ k, v k * (if i = k then MvPolynomial.eval a p else 0) = MvPolynomial.eval a p * v i := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
        ring
      · intro b _ hb
        rw [if_neg (Ne.symm hb), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    simp only [hk, mul_add, Finset.sum_add_distrib, hs1, hs2, Complex.ofReal_zero, zero_smul, add_zero]

private theorem hasDerivAt_norm_sq_add_smul_zero (u w : ℂ) :
    HasDerivAt (fun t : ℝ => ‖u + (t : ℂ) * w‖ ^ 2) (2 * (star u * w).re) 0 := by
  have h : (fun t : ℝ => ‖u + (t : ℂ) * w‖ ^ 2) =
      fun t : ℝ => (u.re + t * w.re) * (u.re + t * w.re) + (u.im + t * w.im) * (u.im + t * w.im) := by
    funext t
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  rw [h]
  have h1 : HasDerivAt (fun t : ℝ => u.re + t * w.re) w.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.re).const_add u.re
  have h2 : HasDerivAt (fun t : ℝ => u.im + t * w.im) w.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.im).const_add u.im
  refine ((h1.mul h1).add (h2.mul h2)).congr_deriv ?_
  show _ = 2 * ((starRingEnd ℂ) u * w).re
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem hasDerivAt_gs_line_zero {m : ℕ} (c : ℝ) (U W : Matrix (Fin m) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => gs c (U + (t : ℂ) • W))
      (gs c U * (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ))) 0 := by
  have hr : HasDerivAt (fun t : ℝ => c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2)
      (c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re) 0 := by
    refine HasDerivAt.const_mul c ?_
    first
      | exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun i _ => hasDerivAt_norm_sq_add_smul_zero (U a i) (W a i)
      | exact HasDerivAt.sum fun a _ => HasDerivAt.sum fun i _ => hasDerivAt_norm_sq_add_smul_zero (U a i) (W a i)
  have hn : HasDerivAt (fun t : ℝ => -((c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2 : ℝ) : ℂ))
      (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ)) 0 := hr.ofReal_comp.neg
  have hc := hn.cexp
  have e0 : (fun t : ℝ => gs c (U + (t : ℂ) • W)) =
      fun t : ℝ => Complex.exp (-((c * ∑ a, ∑ i, ‖U a i + (t : ℂ) * W a i‖ ^ 2 : ℝ) : ℂ)) := by
    funext t
    rfl
  rw [e0]
  refine hc.congr_deriv ?_
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  rfl

theorem annS_tens {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (X : Matrix (Fin V.rank) (Fin n) ℂ) (x : Mx D V.rank n) :
    annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) x =
      (∑ k, ptX (fr⁻¹ * X) k * eval (ptX (fr⁻¹ * compAt θ τ x)) (pderiv k Q)) *
        gs (cLoc l τ) (fr⁻¹ * compAt θ τ x) * psi0 θ V n l s τ x := by
  obtain ⟨-, -, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ X
  set c := cLoc l τ with hc
  set z := compAt θ τ x with hz
  set U : Matrix (Fin V.rank) (Fin n) ℂ := fr⁻¹ * z with hU
  set W : Matrix (Fin V.rank) (Fin n) ℂ := fr⁻¹ * X with hW
  set Ψx := psi0 θ V n l s τ x with hΨ
  have hadd : ∀ y : Mx D V.rank n, compAt θ τ (x + y) = z + compAt θ τ y := by
    intro y
    ext i j
    show (θ τ) (infPart D ((x + y) i j)) = (θ τ) (infPart D (x i j)) + (θ τ) (infPart D (y i j))
    rw [show (x + y) i j = x i j + y i j from rfl, map_add, map_add]
  have hcz : ∀ t : ℝ, compAt θ τ (x + lineAt θ τ X t) = z + (t : ℂ) • X := by
    intro t
    rw [hadd, hcomp t τ, if_pos rfl]
  have hφ : ∀ t : ℝ, tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t) =
      eval (ptX U + (t : ℂ) • ptX W) Q * gs c (U + (t : ℂ) • W) * Ψx := by
    intro t
    have e1 : fr⁻¹ * compAt θ τ (x + lineAt θ τ X t) = U + (t : ℂ) • W := by
      rw [hcz t, Matrix.mul_add, Matrix.mul_smul]
    show fP c Q (fr⁻¹ * compAt θ τ (x + lineAt θ τ X t)) * psi0 θ V n l s τ (x + lineAt θ τ X t) = _
    rw [e1, gaussian_vacuum_add_line hθ V l s τ x X t]
    show evX Q (U + (t : ℂ) • W) * gs c (U + (t : ℂ) • W) * Ψx = _
    rw [evX_eq_eval, ptX_add_smul]
  have hderiv : HasDerivAt (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t))
      ((∑ k, ptX W k * eval (ptX U) (pderiv k Q)) * gs c U * Ψx +
        eval (ptX U) Q * (gs c U * (-((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ))) * Ψx) 0 := by
    have hP := hasDerivAt_mvPolynomial_eval_line_zero Q (ptX U) (ptX W)
    have hG := hasDerivAt_gs_line_zero c U W
    rw [show (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t)) =
        fun t : ℝ => eval (ptX U + (t : ℂ) • ptX W) Q * gs c (U + (t : ℂ) • W) * Ψx from funext hφ]
    refine ((hP.mul hG).mul_const Ψx).congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_smul, add_zero]
    ring
  have hφx : tens θ τ fr (fP c Q) (psi0 θ V n l s τ) x = eval (ptX U) Q * gs c U * Ψx := by
    have h0 := hφ 0
    simp only [map_zero, add_zero, Complex.ofReal_zero, zero_smul] at h0
    exact h0
  have hdet : IsUnit fr.det := hfr.1
  have hdetH : IsUnit frᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star
  have hGs : gramAt D V τ * s τ = (fr⁻¹)ᴴ * fr⁻¹ := by
    have h := hfr.2.2
    calc gramAt D V τ * s τ = (frᴴ)⁻¹ * (frᴴ * (gramAt D V τ * s τ) * fr) * fr⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
            ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul]
      _ = (fr⁻¹)ᴴ * fr⁻¹ := by
          rw [h, Matrix.mul_one, Matrix.conjTranspose_nonsing_inv]
  have e1' : ∑ a, ∑ i, 2 * (star (U a i) * W a i).re = 2 * (Uᴴ * W).trace.re := by
    show _ = 2 * (∑ i, (Uᴴ * W) i i).re
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_comm
  have e2' : Uᴴ * W = zᴴ * (gramAt D V τ * s τ) * X := by
    rw [hGs]
    simp only [hU, hW, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e3' : (zᴴ * (gramAt D V τ * s τ) * X).trace.re = (Xᴴ * (gramAt D V τ * s τ) * z).trace.re := by
    have h : Xᴴ * (gramAt D V τ * s τ) * z = (zᴴ * (gramAt D V τ * s τ) * X)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        (hM τ).eq, Matrix.mul_assoc]
    rw [h, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
  have hc' : c = 2 * Real.pi * |l τ| := rfl
  have hlin : GlobalTheory.StdUnn.linF V l s τ X z = ((c * ∑ a, ∑ i, 2 * (star (U a i) * W a i).re : ℝ) : ℂ) := by
    show ((4 * Real.pi * |l τ| * (Xᴴ * (gramAt D V τ * s τ) * z).trace.re : ℝ) : ℂ) = _
    congr 1
    rw [e1', e2', e3', hc']
    ring
  show deriv (fun t : ℝ => tens θ τ fr (fP c Q) (psi0 θ V n l s τ) (x + lineAt θ τ X t)) 0 +
      GlobalTheory.StdUnn.linF V l s τ X z * tens θ τ fr (fP c Q) (psi0 θ V n l s τ) x = _
  rw [hderiv.deriv, hφx, hlin]
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem const_of_annS {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (h : ∀ X, annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) = 0) :
    Q = C (evX Q 0) := by
  have hk : ∀ u W : Matrix (Fin V.rank) (Fin n) ℂ, ∑ k, ptX W k * eval (ptX u) (pderiv k Q) = 0 := by
    intro u W
    have e := congrFun (h (fr * W)) (xL θ τ (fr * u))
    rw [annS_tens hθ hfr hM l] at e
    have hinv : ∀ v : Matrix (Fin V.rank) (Fin n) ℂ, fr⁻¹ * (fr * v) = v := fun v => by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
    have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
      have := congrFun (compAt_xL hθ τ (fr * u)) τ
      simpa [dirAt_self] using this
    have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
      unfold psi0
      rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
      simp only [one_mul]
      exact gaussian_at_zero_eq_one D V.rank n
    rw [hc, hinv, hinv, hp, mul_one] at e
    exact (mul_eq_zero.1 e).resolve_right (gs_ne_zero _ _)
  have hconst : ∀ u : Matrix (Fin V.rank) (Fin n) ℂ, evX Q u = evX Q 0 := by
    intro u
    let F : ℝ → ℂ := fun t => eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u) Q
    have hF : ∀ t, HasDerivAt F 0 t := by
      intro t
      have hd := GlobalTheory.FockAnnKill.hasDerivAt_eval_line Q (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ)) (ptX u) t
      refine hd.congr_deriv ?_
      have e2 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u = ptX ((0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • u) :=
        (ptX_add_smul _ _ t).symm
      rw [e2]
      exact hk _ u
    have hdiff : Differentiable ℝ F := fun t => (hF t).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff (fun t => (hF t).deriv) 1 0
    have e1 : F 1 = evX Q u := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((1 : ℝ) : ℂ) • ptX u) Q = eval (ptX u) Q
      rw [Complex.ofReal_one, one_smul]
      have e3 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ptX u = ptX u := by
        funext k
        obtain ⟨a, i, b⟩ := k
        cases b <;> simp [ptX]
      rw [e3]
    have e0 : F 0 = evX Q 0 := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((0 : ℝ) : ℂ) • ptX u) Q = eval (ptX 0) Q
      rw [Complex.ofReal_zero, zero_smul, add_zero]
    rw [← e1, ← e0, hc]
  apply sub_eq_zero.1
  apply evX_eq_zero
  intro u
  show eval _ (Q - C (evX Q 0)) = 0
  rw [map_sub, eval_C]
  exact sub_eq_zero.2 (hconst u)

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.RhoH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

theorem annS_stable : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ (τ : D.what₂.Tau) (Φ : schwartzA θ V.rank n), (∀ X, annS V l s θ τ X Φ.1 = 0) →
    ∀ k ∈ K D n, ∀ X, annS V l s θ τ X (ω k Φ).1 = 0 := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs τ Φ hann k hk X
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨hschS, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ

  have hkill1 : ∀ Z : Matrix (Fin V.rank) (Fin A.rank) ℂ,
      annih (heisO ψ₀ (dblSp A) V) θ τ (cplxO (s' τ) (s τ)) (Z * (dblDec A).qX.map (tauE D τ)) f = 0 := by
    intro Z
    apply GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero D ψ₀ hstd A V μ 𝓕 hμ _ (GlobalTheory.StdUnn.isThetaFunO_annih_of_std (A := A) (B := V) (ν := μ) (𝓨 := 𝓕) hstd hθ hμ τ _ _ hf)
    rw [GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf τ Z, hfΦ]
    exact hann Z
  have hkill : ∀ Y : Matrix (Fin V.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ₀ (dblSp A) V) θ τ (cplxO (s' τ) (s τ)) Y f = 0 := by
    intro Y
    obtain ⟨Z, Z', c, hdec⟩ := GlobalTheory.T.annihilationOperator_doubledHermitianSpace_decomp D ψ₀ hstd θ hθ A V μ' hsk s' s hstd' hs τ Y
    rw [hdec f hf, hkill1, hkill1, smul_zero, add_zero]

  have hkk : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hS : ∀ τ', s' τ' * compAt θ τ' (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) =
      compAt θ τ' (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) * s' τ' := fun τ' => (hcomm (κ.symm k) hkk τ').symm
  have hm1 : ∀ τ', compAt θ τ' (Formalism.L2.Theta.mt V 1) = 1 := by
    intro τ'
    simp [Formalism.L2.Theta.mt, compAt, Matrix.map_one]
  have hT : ∀ τ', s τ' * compAt θ τ' (Formalism.L2.Theta.mt V 1) = compAt θ τ' (Formalism.L2.Theta.mt V 1) * s τ' := by
    intro τ'
    rw [hm1, Matrix.mul_one, Matrix.one_mul]
  let X' : Matrix (Fin V.rank) (Fin A.rank) ℂ := X
  set Y0 : Matrix (Fin V.rank) (Fin (dblSp A).rank) ℂ :=
    (X' * (dblDec A).qX.map (tauE D τ)) * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) with hY0
  have hmove := (GlobalTheory.FockMove.om_foldr hdat hθ (κ.symm k) 1 hS hT hf [(τ, Y0)]).2
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil] at hmove
  rw [hkill Y0, map_zero, hm1, Matrix.one_mul, hY0, Matrix.mul_assoc,
    GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.mul_one] at hmove

  have htk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htk
  have hth' : IsThetaFunO ψ₀ (dblSp A) V (omh (κ.symm k, 1) f) := hdat.om_pres _ f hf
  have e := GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hth' τ X'
  rw [← hmove] at e
  have hs0 : sch ψ₀ A V μ 𝓕 (0 : WO (dblSp A) V → ℂ) = 0 := by
    have := (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ f f hf hf 0).2.2.2
    rw [zero_smul, zero_smul] at this
    exact this
  rw [hs0] at e
  show annS V l s θ τ X ((ω k) Φ).1 = 0
  rw [show ((ω k) Φ).1 = sch ψ₀ A V μ 𝓕 (omh (κ.symm k, 1) f) from htk]
  exact e.symm

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 8000000

open RhoH in
theorem lIkvac : LIkvac := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL e hvac k hk
  classical
  obtain ⟨𝓕, hμ⟩ := hC.hμ
  have hΨ0m : psi0 θ V n l s τ ∈ awayA θ V n l s τ := unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V l s τ
  have hl0 : ∀ τ, l τ ≠ 0 := l_ne_zero D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl
  have hmem : ∀ P : PX V.rank n, tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) (psi0 θ V n l s τ) ∈ fockA θ V n l s :=
    fun P => hT D n V θ l s τ ε fr hC.hθ hl0 hC.hs hC.hfr _ hΨ0m P
  have hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian := fun τ => (hC.hs τ).2.2.1

  have hann1 : ∀ X, annS V l s θ τ X (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 1).1 = 0 := by
    intro X
    rw [phiS_val (hmem 1).1]
    funext x
    rw [annS_tens hC.hθ hC.hfr hM l]
    simp
  have hann2 := annS_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs τ _ hann1 (ι k)
    (iota_mem_K hC.hθ hC.hι k hk)
  rw [hL k _ hΨ0m 1] at hann2

  have hΦ : (phiS θ τ fr (cLoc l τ) (psi0 θ V n l s τ) 1).1 ∈ fockA θ V n l s := by
    rw [phiS_val (hmem 1).1]
    exact (hmem 1).2
  have hst := fock_stable D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 hμ ω hC.hω l hC.hl s hC.hs _ hΦ (ι k)
    (iota_mem_K hC.hθ hC.hι k hk)
  rw [hL k _ hΨ0m 1] at hst
  obtain ⟨Q, hQ⟩ := tens_slice hC.hθ hC.hfr l _ hst
  rw [hQ] at hann2
  have hQc := const_of_annS hC.hθ hC.hfr hM l Q hann2
  set a := evX Q 0 with ha
  have hL1 : L k (fP (cLoc l τ) 1) = a • fP (cLoc l τ) 1 := by
    rw [hQ, hQc]
    funext u
    simp [fP, evX]

  have hv := hvac k
  unfold sLd at hv
  rw [hL1] at hv
  have hg0 : gs (cLoc l τ) (0 : Fin V.rank → Fin n → ℂ) = 1 := by
    simp [gs]
  have hf0 : fP (cLoc l τ) (1 : PX V.rank n) 0 = 1 := by
    simp [fP, evX, hg0]
  simp only [Pi.smul_apply, smul_eq_mul, hf0, mul_one] at hv
  rw [hL1, hv]

end PositivityTheory.Rg.Sw.Glob
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocCell

variable {D : D7} {n : ℕ}

theorem exists_away (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) :
    ∃ Ψ ∈ awayA θ V n l s τ, Ψ 0 ≠ 0 := by
  classical
  let W : AddSubgroup (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ intAE D}
      add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (intAE D).zero_mem
      neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin V.rank) (Fin n) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  refine ⟨fun x => gAway V l s τ (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j)), ?_, ?_⟩
  · refine Submodule.subset_span ⟨1, g, hg, by simp, ?_⟩
    funext x
    simp [evalPoly]
  · have hg0 : g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = 1 := by
      simp only [g]
      rw [if_pos]
      exact (QuotientAddGroup.eq_zero_iff (N := W) _).2 fun i j => by simp
    show gAway V l s τ (fun τ => compAt θ τ 0) * g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) ≠ 0
    rw [hg0, mul_one]
    simp [gAway, compAt]

def piT {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x : Mx D m n) : Fin m → Fin n → ℂ := fun a i => compAt θ τ x a i

theorem exists_sec (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (m n : ℕ) :
    ∃ S : (Fin m → Fin n → ℂ) → Mx D m n,
      (∀ x u, piT θ τ (x + S u) = piT θ τ x + u) ∧
      (∀ x u τ', τ' ≠ τ → compAt θ τ' (x + S u) = compAt θ τ' x) ∧
      ∀ x u, (x + S u).map (finPart D) = x.map (finPart D) := by
  classical
  have hL := fun z : Matrix (Fin m) (Fin n) ℂ => GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let S : (Fin m → Fin n → ℂ) → Mx D m n := fun u =>
    ∑ a, ∑ i, (lineAt θ τ (Matrix.single a i 1) (u a i).re + lineAt θ τ (Matrix.single a i Complex.I) (u a i).im)
  have e : ∀ (τ' : D.what₂.Tau) (y : Mx D m n),
      compAt θ τ' y = ((θ τ').comp (infPart D)).toAddMonoidHom.mapMatrix y := fun _ _ => rfl
  have ef : ∀ y : Mx D m n, y.map (finPart D) = (finPart D).toAddMonoidHom.mapMatrix y := fun _ => rfl
  have hc : ∀ τ' (u : Fin m → Fin n → ℂ), compAt θ τ' (S u) = if τ' = τ then Matrix.of u else 0 := by
    intro τ' u
    rw [e]
    simp only [S]
    simp_rw [map_sum, map_add]
    simp_rw [← e, (hL _).2.2]
    split_ifs with h
    · ext a' i'
      simp [Matrix.sum_apply, Matrix.single_apply]
      rw [Fintype.sum_eq_single a' (fun c hc => by simp [hc]), Fintype.sum_eq_single i' (fun c hc => by simp [hc])]
      simp only [and_self, if_true]
      exact Complex.re_add_im _
    · simp
  have hf : ∀ u, (S u).map (finPart D) = 0 := by
    intro u
    rw [ef]
    simp only [S]
    simp_rw [map_sum, map_add]
    simp_rw [← ef, (hL _).2.1]
    simp
  refine ⟨S, fun x u => ?_, fun x u τ' h => ?_, fun x u => ?_⟩
  · funext a i
    simp only [piT, Pi.add_apply]
    rw [e, map_add, ← e, ← e, hc, if_pos rfl]
    rfl
  · rw [e, map_add, ← e, ← e, hc, if_neg h, add_zero]
  · rw [ef, map_add, ← ef, ← ef, hf, add_zero]

theorem cov {m n : ℕ} (fr : Matrix (Fin m) (Fin m) ℂ) (hfr : IsUnit fr.det) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ f : (Fin m → Fin n → ℂ) → ℂ,
      ∫ u : Fin m → Fin n → ℂ, f (fr⁻¹ * Matrix.of u) = (c' : ℂ) * ∫ y, f y := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hfr
  have h2 : fr⁻¹ * fr = 1 := Matrix.nonsing_inv_mul fr hfr
  let T : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) :=
    { toFun := fun u => Matrix.of.symm (fr⁻¹ * Matrix.of u)
      invFun := fun u => Matrix.of.symm (fr * Matrix.of u)
      map_add' := fun u v => by
        ext a i
        simp [Matrix.mul_apply, Finset.sum_add_distrib, mul_add]
      map_smul' := fun r u => by
        ext a i
        simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, RingHom.id_apply,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Complex.real_smul]
        ring
      left_inv := fun u => by
        show fr * (fr⁻¹ * Matrix.of u) = u
        rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        rfl
      right_inv := fun u => by
        show fr⁻¹ * (fr * Matrix.of u) = u
        rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
        rfl }
  have hT : LinearMap.det (T : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' T).ne_zero
  refine ⟨|(LinearMap.det (T : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ)))⁻¹|, abs_pos.2 (inv_ne_zero hT),
    fun f => ?_⟩
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → Fin n → ℂ))) hT
  let Te : (Fin m → Fin n → ℂ) ≃ᵐ (Fin m → Fin n → ℂ) :=
    (T.toContinuousLinearEquiv.toHomeomorph).toMeasurableEquiv
  have hTe : ∀ u, Te u = fr⁻¹ * Matrix.of u := fun u => rfl
  have hm : Measure.map Te volume = Measure.map (T : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ)) volume := rfl
  calc ∫ u : Fin m → Fin n → ℂ, f (fr⁻¹ * Matrix.of u) = ∫ u, f (Te u) := rfl
    _ = ∫ y, f y ∂(Measure.map Te volume) := (integral_map_equiv Te f).symm
    _ = _ := by
      rw [hm, hmap, integral_smul_measure]
      simp [ENNReal.toReal_ofReal (abs_nonneg _)]

theorem continuous_evX {m n : ℕ} (P : PX m n) : Continuous (evX P) := by
  unfold evX
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  split_ifs
  · exact continuous_star.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  · exact (continuous_apply k.2.1).comp (continuous_apply k.1)

theorem int_gauss_ne (hSF : SchFP) {m n : ℕ} {c : ℝ} (hc : 0 < c) : ∫ y : Fin m → Fin n → ℂ, fP c (1 : PX m n) y ≠ 0 := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨S, hS⟩ := hSF m n c hc 1
  have hint : Integrable (fP c (1 : PX m n)) := hS ▸ S.integrable
  have e : fP c (1 : PX m n) = fun y => ((Real.exp (-(c * ∑ a, ∑ i, ‖y a i‖ ^ 2)) : ℝ) : ℂ) := by
    funext y
    simp [fP, evX, gs, Complex.ofReal_exp]
  rw [e]
  beta_reduce
  rw [integral_complex_ofReal]
  have hr : Integrable (fun y : Fin m → Fin n → ℂ => Real.exp (-(c * ∑ a, ∑ i, ‖y a i‖ ^ 2))) := by
    refine hint.norm.congr (Filter.Eventually.of_forall fun y => ?_)
    show ‖fP c (1 : PX m n) y‖ = _
    rw [congrFun e y, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact_mod_cast (integral_exp_pos hr).ne'

theorem weyl0 {θ : InfFam D} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (W : G D n) (hW : mat W = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) :
    (ω W Φ).1 0 = ∫ y, Φ.1 y ∂μ := by
  rw [hω.weyl W hW Φ 0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [GlobalTheory.StdUnn.inner]

theorem trivInv {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} (hx : IsTrivAt θ τ x) : IsTrivAt θ τ x⁻¹ := by
  have e : mat x * mat x⁻¹ = 1 := by
    unfold mat
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h2 : compAt θ τ (mat x * mat x⁻¹) = compAt θ τ (mat x) * compAt θ τ (mat x⁻¹) :=
    Matrix.map_mul (f := (θ τ).comp (infPart D))
  unfold IsTrivAt at *
  rw [e, hx, one_mul] at h2
  rw [← h2]
  exact Matrix.map_one ((θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem wSplit (hDA : DecompAway) {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n}
    (hι : IsPlaceEmb θ τ ι) (W : G D n) (hW : mat W = blk4 0 1 (-1) 0) :
    ∃ x : G D n, IsTrivAt θ τ x ∧ (∃ y0 : GR n, mR y0 = JJ n) ∧ ∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ),
      mR g = JJ n * nU b → ∃ Nb : GR n, mR Nb = nU b ∧ ι g = W * ι Nb * x⁻¹ := by
  obtain ⟨x, y, hx, hWxy, hcomm⟩ := hDA D n θ τ ι hθ hι W
  have hmm : ∀ a b : G D n, mat (a * b) = mat a * mat b := fun a b => by
    unfold mat
    rw [map_mul, Units.val_mul]
  have hy : mR y = JJ n := by
    have h1 : compAt θ τ (mat W) = compAt θ τ (mat x) * compAt θ τ (mat (ι y)) := by
      rw [hWxy, hmm]
      exact Matrix.map_mul (f := (θ τ).comp (infPart D))
    unfold IsTrivAt at hx
    rw [hx, Matrix.one_mul, (hι.2 y).1, hW] at h1
    have h2 : compAt θ τ (blk4 (0 : Matrix (Fin n) (Fin n) (AE D)) 1 (-1) 0) = reidx (JJ n) := by
      change (blk4 (0 : Matrix (Fin n) (Fin n) (AE D)) 1 (-1) 0).map ((θ τ).comp (infPart D)) = _
      rw [LocCellA.block_matrix_map, LocCellA.map_neg_one', LocCellA.map_one', Matrix.map_zero _ (map_zero _)]
      rfl
    rw [h2] at h1
    ext i j
    have := congrFun (congrFun h1 (finSumFinEquiv i)) (finSumFinEquiv j)
    simpa [reidx] using this.symm
  refine ⟨x, hx, ⟨y, hy⟩, fun g b hgb => ⟨y⁻¹ * g, ?_, ?_⟩⟩
  · have hm : ∀ a c : GR n, mR (a * c) = mR a * mR c := fun _ _ => rfl
    have hyy : mR y⁻¹ * mR y = 1 := by rw [← hm, inv_mul_cancel]; rfl
    rw [hm, hgb, ← hy, ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  · have hyW : ι y = W * x⁻¹ := by
      rw [hWxy, hcomm y]
      group
    have hc2 : ι (y⁻¹ * g) * x⁻¹ = x⁻¹ * ι (y⁻¹ * g) := by
      have := hcomm (y⁻¹ * g)
      calc ι (y⁻¹ * g) * x⁻¹ = x⁻¹ * (x * ι (y⁻¹ * g)) * x⁻¹ := by group
        _ = x⁻¹ * (ι (y⁻¹ * g) * x) * x⁻¹ := by rw [this]
        _ = x⁻¹ * ι (y⁻¹ * g) := by group
    calc ι g = ι y * ι (y⁻¹ * g) := by rw [← map_mul, mul_inv_cancel_left]
      _ = W * x⁻¹ * ι (y⁻¹ * g) := by rw [hyW]
      _ = W * ι (y⁻¹ * g) * x⁻¹ := by rw [mul_assoc, ← hc2, ← mul_assoc]

end PositivityTheory.Rg.Sw.Glob.LocCell

namespace PositivityTheory.Rg.Sw.Glob

open LocCell in

theorem lIcell_of (hAw : AwayAct) (hDA : DecompAway) (hU : UnipTau) (hAI : AwayIn) (hSF : SchFP) (hLN : LNe)
    (hLc : LIcont) (hLl : LIlaw) (hLv : LIvac) : LIcell := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hTM L hL
  have hl0 : ∀ τ', l τ' ≠ 0 := hLN D ψ θ l hC.hψ hC.hθ hC.hl
  have hcpos : 0 < cLoc l τ := by
    unfold cLoc
    have := abs_pos.2 (hl0 τ)
    positivity
  obtain ⟨Ψ0, hΨ0a, hΨ00⟩ := exists_away θ V n l s τ
  have hΨ0 : AwayCls θ τ fr Ψ0 := hAI D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr hl0 Ψ0 hΨ0a
  obtain ⟨W, hW⟩ := wEx D n
  obtain ⟨x, hx, ⟨y0, hy0⟩, hsplit⟩ := wSplit hDA hC.hθ hC.hι W hW
  obtain ⟨A, hA⟩ := hAw D n V ψ χ θ μ ω H l s ν τ ε fr ι hC x⁻¹ (trivInv hx)
  obtain ⟨hB, hAf⟩ := hA Ψ0 hΨ0
  have hphi : ∀ P : PX V.rank n, phiS θ τ fr (cLoc l τ) Ψ0 P =
      ⟨tens θ τ fr (fP (cLoc l τ) P) Ψ0, hΨ0.2 _ (hSF _ _ _ hcpos P)⟩ := by
    intro P
    unfold phiS
    rw [dif_pos (hΨ0.2 _ (hSF _ _ _ hcpos P))]

  let aF : PX V.rank n → Matrix (Fin n) (Fin n) ℂ → (Fin V.rank → Fin n → ℂ) → ℂ := fun P b u =>
    Complex.exp (Complex.I * tLoc l τ * (b * gramX ε (fr⁻¹ * Matrix.of u)).trace) *
      fP (cLoc l τ) P (fr⁻¹ * Matrix.of u)
  have key : ∀ P (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR g = JJ n * nU b →
      ∃ Nb : GR n, (∀ z, aF P b (piT θ τ z) * A Ψ0 z =
        (ω (ι Nb) (ω x⁻¹ (phiS θ τ fr (cLoc l τ) Ψ0 P))).1 z) ∧
        sLd L (cLoc l τ) P g * Ψ0 0 = ∫ z, aF P b (piT θ τ z) * A Ψ0 z ∂μ := by
    intro P g b hb hgb
    obtain ⟨Nb, hNb, hg⟩ := hsplit g b hgb
    have hpt : ∀ z, aF P b (piT θ τ z) * A Ψ0 z = (ω (ι Nb) (ω x⁻¹ (phiS θ τ fr (cLoc l τ) Ψ0 P))).1 z := by
      intro z
      rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC Nb b hb hNb, hphi P, hAf _ (hSF _ _ _ hcpos P)]
      have e : Matrix.of (piT θ τ z) = compAt θ τ z := rfl
      simp only [aF, tens, e]
      ring
    refine ⟨Nb, hpt, ?_⟩
    have e1 : (ω (ι g) (phiS θ τ fr (cLoc l τ) Ψ0 P)).1 0 = sLd L (cLoc l τ) P g * Ψ0 0 := by
      rw [hL g Ψ0 hΨ0a P]
      simp [tens, sLd, compAt]
      exact Or.inl rfl
    rw [← e1, hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, weyl0 hC.hω W hW]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hpt z).symm)
  obtain ⟨𝓕, hμ1⟩ := hC.hμ
  haveI : μ.IsAddHaarMeasure := hμ1.1
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  obtain ⟨S, hS1, hS2, hS3⟩ := exists_sec θ hC.hθ τ V.rank n
  have hπc : Continuous (piT θ τ : Mx D V.rank n → Fin V.rank → Fin n → ℂ) := by
    have := GlobalTheory.RealWeil.continuous_compAt hC.hθ τ V.rank n
    exact continuous_pi fun a => continuous_pi fun i => this.matrix_elem a i
  have hBinv : ∀ z u, A Ψ0 (z + S u) = A Ψ0 z := fun z u => hB.1 _ _ (fun τ' h => hS2 z u τ' h) (hS3 z u)
  have hfPc : ∀ P : PX V.rank n, Continuous (fP (cLoc l τ) P) := fun P => by
    obtain ⟨Sf, hSf⟩ := hSF _ _ _ hcpos P
    rw [← hSf]
    exact Sf.continuous
  have hlin : Continuous (fun u : Fin V.rank → Fin n → ℂ => fr⁻¹ * Matrix.of u) :=
    continuous_const.matrix_mul continuous_id
  have hne1 : ∀ y, fP (cLoc l τ) (1 : PX V.rank n) y ≠ 0 := fun y => by
    simp [fP, evX, gs, Complex.exp_ne_zero]
  have hBm : Measurable (A Ψ0) := by
    have hm := hB.2 (fP (cLoc l τ) 1) (hSF _ _ _ hcpos 1)
    have hcont := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hC.hθ _ _ _ hm).1
    have e : A Ψ0 = fun z => tens θ τ fr (fP (cLoc l τ) 1) (A Ψ0) z / fP (cLoc l τ) 1 (fr⁻¹ * compAt θ τ z) := by
      funext z
      simp only [tens]
      exact (mul_div_cancel_left₀ _ (hne1 _)).symm
    rw [e]
    refine (hcont.div ((hfPc 1).comp ?_) fun z => hne1 _).measurable
    exact continuous_const.matrix_mul (GlobalTheory.RealWeil.continuous_compAt hC.hθ τ V.rank n)
  let a0 : (Fin V.rank → Fin n → ℂ) → ℂ := fun u => fP (cLoc l τ) 1 (fr⁻¹ * Matrix.of u)
  have ha0c : Continuous a0 := (hfPc 1).comp hlin
  have haFc : ∀ P b, Continuous (aF P b) := fun P b =>
    ((Complex.continuous_exp.comp (continuous_const.mul (Continuous.matrix_trace (continuous_const.matrix_mul
      (continuous_pi fun i => continuous_pi fun j => (continuous_evX (Qp ε i j)).comp hlin))))).mul
      ((hfPc P).comp hlin))
  have hTF : ∀ (P : PX V.rank n) (b : Matrix (Fin n) (Fin n) ℂ) (Nb : GR n),
      (∀ z, aF P b (piT θ τ z) * A Ψ0 z = (ω (ι Nb) (ω x⁻¹ (phiS θ τ fr (cLoc l τ) Ψ0 P))).1 z) →
      ∃ κ : ℂ, (∫ z, aF P b (piT θ τ z) * A Ψ0 z ∂μ = κ * ∫ u, aF P b u) ∧
        ∫ z, a0 (piT θ τ z) * A Ψ0 z ∂μ = κ * ∫ u, a0 u := by
    intro P b Nb hpt
    have hint1 : Integrable (fun z => aF P b (piT θ τ z) * A Ψ0 z) μ := by
      simp_rw [hpt]
      exact GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hC.hθ hμ1 (ω (ι Nb) (ω x⁻¹ (phiS θ τ fr (cLoc l τ) Ψ0 P))).2
    have hint2 : Integrable (fun z => a0 (piT θ τ z) * A Ψ0 z) μ := by
      have := GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hC.hθ hμ1 (hB.2 (fP (cLoc l τ) 1) (hSF _ _ _ hcpos 1))
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      rfl
    obtain ⟨κ, hκ⟩ := LocCellT.tauFact μ (piT θ τ) hπc S hS1 (A Ψ0) hBm hBinv
      (fun u => ‖aF P b u‖ + ‖a0 u‖) ((haFc P b).norm.add ha0c.norm)
      (fun u => add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.2 (hne1 _)))
      ((hint1.norm.add hint2.norm).congr (Filter.Eventually.of_forall fun z => by
        simp only [Pi.add_apply, norm_mul]; ring))
    refine ⟨κ, hκ _ (haFc P b).measurable ⟨1, fun u => ?_⟩, hκ _ ha0c.measurable ⟨1, fun u => ?_⟩⟩
    · simp only [one_mul]; exact le_add_of_nonneg_right (norm_nonneg _)
    · simp only [one_mul]; exact le_add_of_nonneg_left (norm_nonneg _)
  obtain ⟨c', hc'pos, hcov⟩ := cov (n := n) fr hC.hfr.1
  have hy0' : mR y0 = JJ n * nU 0 := by
    rw [hy0]
    simp [nU]
  obtain ⟨N0, hpt0, -⟩ := key 1 y0 0 (by simp) hy0'
  obtain ⟨κ, -, hκ0⟩ := hTF 1 0 N0 hpt0
  have hint0 : ∫ u, a0 u ≠ 0 := by
    have e : (∫ u, a0 u) = (c' : ℂ) * ∫ y, fP (cLoc l τ) (1 : PX V.rank n) y := hcov (fP (cLoc l τ) 1)
    rw [e]
    exact mul_ne_zero (by exact_mod_cast hc'pos.ne') (int_gauss_ne hSF hcpos)
  have hcell : ∀ (P : PX V.rank n) (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
      sLd L (cLoc l τ) P g = κ * c' / Ψ0 0 * secN ε (cLoc l τ) (tLoc l τ) P b := by
    intro P g b hb hgb
    obtain ⟨Nb, hpt, hv⟩ := key P g b hb hgb
    obtain ⟨κ', h1, h2⟩ := hTF P b Nb hpt
    have hk : κ' = κ := mul_right_cancel₀ hint0 (h2.symm.trans hκ0)
    have hcovP : ∫ u, aF P b u = (c' : ℂ) *
        ∫ y, Complex.exp (Complex.I * tLoc l τ * (b * gramX ε y).trace) * fP (cLoc l τ) P y :=
      hcov (fun y => Complex.exp (Complex.I * tLoc l τ * (b * gramX ε y).trace) * fP (cLoc l τ) P y)
    have hsec : (∫ y, Complex.exp (Complex.I * tLoc l τ * (b * gramX ε y).trace) * fP (cLoc l τ) P y) =
        secN ε (cLoc l τ) (tLoc l τ) P b := by
      unfold secN
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [fP]
      ring
    rw [h1, hk, hcovP, hsec] at hv
    field_simp
    rw [hv]
    ring
  refine ⟨κ * c' / Ψ0 0, ?_, hcell⟩
  intro hC0
  obtain ⟨e, he⟩ := hLl D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hTM L hL
  have hsign : (tLoc l τ = cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε true ∧ (pqOf ε l τ).2 = cnt ε false) ∨
      (tLoc l τ = -cLoc l τ ∧ (pqOf ε l τ).1 = cnt ε false ∧ (pqOf ε l τ).2 = cnt ε true) := by
    unfold tLoc cLoc pqOf
    rcases lt_or_gt_of_ne (hl0 τ) with h | h
    · right
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_of_neg h]; ring
      · simp [if_neg (not_lt.2 h.le)]
      · simp [if_neg (not_lt.2 h.le)]
    · left
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_of_pos h]
      · simp [if_pos h]
      · simp [if_pos h]
  have hS1 : sLd L (cLoc l τ) 1 1 = 1 := by
    have h := congrFun (hL 1 Ψ0 hΨ0a 1) 0
    rw [map_one, map_one, hphi 1] at h
    simp only [Module.End.one_apply, tens] at h
    have h0 : fr⁻¹ * compAt θ τ (0 : Mx D V.rank n) = 0 := by simp [compAt]
    rw [h0] at h
    have h' := mul_right_cancel₀ hΨ00 h
    simp only [sLd]
    calc L 1 (fP (cLoc l τ) 1) 0 = L 1 (fP (cLoc l τ) 1) (0 : Matrix (Fin V.rank) (Fin n) ℂ) := rfl
      _ = fP (cLoc l τ) 1 (0 : Matrix (Fin V.rank) (Fin n) ℂ) := h'.symm
      _ = 1 := by simp [fP, evX, gs]
  have hv := hLv V.rank n ε (cLoc l τ) (tLoc l τ) (pqOf ε l τ).1 (pqOf ε l τ).2 e hcpos hsign
    (sLd L (cLoc l τ) 1) (κ * c' / Ψ0 0) (hLc D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hTM L hL 1) hS1
    (fun y g hy => he 1 y g hy) (fun g b hb hgb => hcell 1 g b hb hgb) y0
  rw [hcell 1 y0 0 (by simp [Matrix.IsHermitian]) hy0', hC0, zero_mul] at hv
  have hdet : (mR y0).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y0.1.isUnit
    exact this.ne_zero
  have hu1 : (u1 (mR y0)).det ≠ 0 := by
    rw [hy0]
    simp only [u1, JJ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, add_zero, smul_neg,
      Matrix.det_neg, Matrix.det_smul, Matrix.det_one]
    simp [Complex.I_ne_zero]
  have hu2 : (u2 (mR y0)).det ≠ 0 := by
    rw [hy0]
    simp only [u2, JJ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, add_zero, smul_neg, neg_neg,
      Matrix.det_smul, Matrix.det_one]
    simp [Complex.I_ne_zero]
  have : F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e y0 ≠ 0 := by
    unfold F0 f0
    exact mul_ne_zero (zpow_ne_zero _ hdet) (mul_ne_zero (zpow_ne_zero _ hu1) (zpow_ne_zero _ hu2))
  exact this hv.symm

end PositivityTheory.Rg.Sw.Glob
end
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem lIcell_of' (hAw : AwayAct) (hLc : LIcont) (hLl : LIlaw) (hLv : LIvac) : LIcell :=
  lIcell_of hAw decompAway unipTau awayIn schFP lNe hLc hLl hLv

end PositivityTheory.Rg.Sw.Glob
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem locInst_of_cell_kvac (hc : LIcell) (hk : LIkvac) (hT : TensMem) : LocInst :=
  locInst_of hT lIl lIlin lIlaw hc lIcont lIrho lIkact lIvac hk

theorem locInst_of_cell (hc : LIcell) (hT : TensMem) : LocInst := locInst_of_cell_kvac hc lIkvac hT

theorem locInst_of_away (hA : AwayAct) (hT : TensMem) : LocInst :=
  locInst_of_cell (lIcell_of' hA lIcont lIlaw lIvac) hT

end PositivityTheory.Rg.Sw.Glob
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem top5 (hLF : LocFact) (hAA : AwayAct) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top3 hLF hAA (locInst_of_away hAA tensMem) hLC hDO hId hC

end PositivityTheory.Rg.Sw.Glob
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LieCPfH

variable {D : D7} {n : ℕ}

theorem sgn_sq {m : ℕ} (ε : Fin m → Bool) (a : Fin m) : sgn ε a * sgn ε a = 1 := by
  unfold sgn; split_ifs <;> simp

theorem diag_sgn_sq {m : ℕ} (ε : Fin m → Bool) :
    Matrix.diagonal (sgn ε) * Matrix.diagonal (sgn ε) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact sgn_sq ε a

theorem exp_preserves {m : ℕ} (ε : Fin m → Bool) (X : Matrix (Fin m) (Fin m) ℂ) (hX : IsUe ε X) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • X))ᴴ * Matrix.diagonal (sgn ε) * NormedSpace.exp ((t : ℂ) • X) =
      Matrix.diagonal (sgn ε) := by
  set J := Matrix.diagonal (sgn ε) with hJdef
  have hJJ : J * J = 1 := diag_sgn_sq ε
  have hJu : IsUnit J := by
    refine (Matrix.isUnit_iff_isUnit_det J).2 ?_
    have h := congrArg Matrix.det hJJ
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h)
  have hJinv : J⁻¹ = J := Matrix.inv_eq_left_inv hJJ
  set Y : Matrix (Fin m) (Fin m) ℂ := (t : ℂ) • X with hY
  have hXs : Xᴴ = J * (-X) * J := by
    have h1 : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
    calc Xᴴ = Xᴴ * J * J := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(J * X) * J := by rw [h1]
      _ = J * (-X) * J := by rw [Matrix.mul_neg, Matrix.neg_mul]
  have hYs : Yᴴ = J * (-Y) * J⁻¹ := by
    rw [hJinv, hY, Matrix.conjTranspose_smul, hXs]
    have : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    rw [this]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  have hE : (NormedSpace.exp Y)ᴴ = J * NormedSpace.exp (-Y) * J := by
    rw [← Matrix.exp_conjTranspose, hYs, Matrix.exp_conj J (-Y) hJu, hJinv]
  have hneg : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl Y).neg_left), neg_add_cancel, NormedSpace.exp_zero]
  rw [hE]
  calc J * NormedSpace.exp (-Y) * J * J * NormedSpace.exp Y
        = J * (NormedSpace.exp (-Y) * NormedSpace.exp Y) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    _ = J := by rw [hneg, Matrix.mul_one]

theorem uh_frame {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : IsUe ε X) (t : ℝ) :
    (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  set E := NormedSpace.exp ((t : ℂ) • X)
  set G := gramAt D V τ
  set J := Matrix.diagonal (sgn ε)
  have hfu : IsUnit fr.det := hfr.1
  have hG : frᴴ * G * fr = J := hfr.2.1
  have hEJ : Eᴴ * J * E = J := exp_preserves ε X hX t
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hfu
  have h2 : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hGJ : G = (fr⁻¹)ᴴ * J * fr⁻¹ := by
    rw [← hG]
    calc G = ((fr⁻¹)ᴴ * frᴴ) * G * (fr * fr⁻¹) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = (fr⁻¹)ᴴ * (frᴴ * G * fr) * fr⁻¹ := by simp only [Matrix.mul_assoc]
  show (fr * E * fr⁻¹)ᴴ * G * (fr * E * fr⁻¹) = G
  calc (fr * E * fr⁻¹)ᴴ * G * (fr * E * fr⁻¹)
        = (fr⁻¹)ᴴ * Eᴴ * (frᴴ * G * fr) * E * fr⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (fr⁻¹)ᴴ * (Eᴴ * J * E) * fr⁻¹ := by rw [hG]; simp only [Matrix.mul_assoc]
    _ = G := by rw [hEJ, hGJ]

theorem isAtTau_atTau {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {M : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hM : M ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    IsAtTau θ V τ M (atTau θ V τ M) := by
  have hex : ∃ x, IsAtTau θ V τ M x := Formalism.IndefR.PublishedAut.atTauExists_of hθ V τ M hM
  unfold atTau
  rw [dif_pos hex]
  exact hex.choose_spec

theorem compAt_mul_gen (θ : InfFam D) (τ : D.what₂.Tau) {a b c : ℕ} (A : Mx D a b) (B : Mx D b c) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B := by
  unfold compAt
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem tens_comp {V : HSp D} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfu : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    (E : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V) (hh : IsAtTau θ V τ (fr * E * fr⁻¹) h)
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (x : Mx D V.rank n) :
    tens θ τ fr f Ψ (HMul.hMul (mt V h) x : Mx D V.rank n) = f (E * (fr⁻¹ * compAt θ τ x)) * Ψ x := by
  have hc : ∀ ρ, compAt θ ρ (HMul.hMul (mt V h) x : Mx D V.rank n) = compAt θ ρ (mt V h) * compAt θ ρ x := fun ρ =>
    compAt_mul_gen θ ρ (mt V h) x
  have hτ : compAt θ τ (mt V h) = fr * E * fr⁻¹ := hh.2.1
  have hρ : ∀ ρ, ρ ≠ τ → compAt θ ρ (mt V h) = 1 := fun ρ hρ => hh.2.2 ρ hρ
  have hfin : (HMul.hMul (mt V h) x : Mx D V.rank n).map (finPart D) = x.map (finPart D) := by
    rw [Matrix.map_mul, Formalism.IndefR.Fock.Der.finPart_mt hh.1, Matrix.one_mul]
  have hΨx : Ψ (HMul.hMul (mt V h) x : Mx D V.rank n) = Ψ x := hΨ.1 _ _ (fun ρ hρ' => by rw [hc, hρ ρ hρ', Matrix.one_mul]) hfin
  unfold tens
  rw [hΨx, hc, hτ]
  congr 1
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul fr hfu, Matrix.one_mul,
    Matrix.mul_assoc]

end PositivityTheory.Rg.Sw.Glob.LieCPfH

namespace PositivityTheory.Rg.Sw.Glob

open LieCPfH

set_option maxHeartbeats 1000000 in

theorem lieComm_of (hAway : AwayIn) (hLNe : LNe) (hSch : SchFP) (hOp : OpCLM) (hAF : AwayFact) (hSD : SchDeriv) :
    LieComm := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC Ψ hΨA X hX P g x
  have hl : ∀ τ', l τ' ≠ 0 := hLNe D ψ θ l hC.hψ hC.hθ hC.hl
  have hc : 0 < cLoc l τ := by
    unfold cLoc
    have := abs_pos.2 (hl τ)
    positivity
  have hΨ : AwayCls θ τ fr Ψ := hAway D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr hl Ψ hΨA
  obtain ⟨𝓕, hμ⟩ := hC.hμ
  have hfu : IsUnit fr.det := hC.hfr.1
  obtain ⟨S, S', hS, hS', hder⟩ := hSD V.rank n (cLoc l τ) hc X P
  obtain ⟨SP, hSP⟩ := hSch V.rank n (cLoc l τ) hc P
  have memQ : ∀ T : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ, tens θ τ fr T Ψ ∈ schwartzA θ V.rank n :=
    fun T => hΨ.2 T ⟨T, rfl⟩
  have hphi : ∀ (Q : PX V.rank n) (T : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ), (⇑T = fP (cLoc l τ) Q) →
      phiS θ τ fr (cLoc l τ) Ψ Q = ⟨tens θ τ fr T Ψ, memQ T⟩ := by
    intro Q T hT
    have hm : tens θ τ fr (fP (cLoc l τ) Q) Ψ ∈ schwartzA θ V.rank n := hT ▸ memQ T
    unfold phiS
    rw [dif_pos hm]
    apply Subtype.ext
    show tens θ τ fr (fP (cLoc l τ) Q) Ψ = tens θ τ fr T Ψ
    rw [hT]
  obtain ⟨x0, y, hg, hx0⟩ := hAF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC g
  obtain ⟨Ψ', hΨ', hact⟩ := hx0 Ψ hΨ
  obtain ⟨L, hL⟩ := hOp D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y
  have key : ∀ T : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ,
      (ω g ⟨tens θ τ fr T Ψ, memQ T⟩).1 = tens θ τ fr (L T) Ψ' := by
    intro T
    rw [hg, map_mul, Module.End.mul_apply]
    have h1 : ω (ι y) ⟨tens θ τ fr T Ψ, memQ T⟩ = ⟨tens θ τ fr (L T) Ψ, memQ (L T)⟩ := Subtype.ext (hL Ψ hΨ T)
    rw [h1]
    exact hact (L T) (memQ (L T))

  have hLHS : (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X P))).1 x =
      (L S') (fr⁻¹ * compAt θ τ x) * Ψ' x := by
    rw [hphi _ S' (funext hS'), key]
    rfl

  have hgc : ∀ t : ℝ, (ω g (phiS θ τ fr (cLoc l τ) Ψ P)).1
      (HMul.hMul (mt V (atTau θ V τ (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹))) x : Mx D V.rank n) =
        (L (S t)) (fr⁻¹ * compAt θ τ x) * Ψ' x := by
    intro t
    have hM := uh_frame hC.hfr hX t
    have hh := isAtTau_atTau hC.hθ V τ hM
    have hΦt : ∀ x', (⟨tens θ τ fr (S t) Ψ, memQ (S t)⟩ : schwartzA θ V.rank n).1 x' =
        (phiS θ τ fr (cLoc l τ) Ψ P).1 (mt V (atTau θ V τ (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹)) ⬝ x') := by
      intro x'
      rw [hphi P SP hSP]
      show tens θ τ fr (S t) Ψ x' = tens θ τ fr SP Ψ (HMul.hMul (mt V _) x' : Mx D V.rank n)
      rw [tens_comp hfu hΨ _ _ hh, hSP]
      unfold tens
      exact congrArg (· * Ψ x') (hS t _)
    have e := GCommH.gComm hC.hψ hC.hχ hC.hη hC.hθ hμ hC.hω (phiS θ τ fr (cLoc l τ) Ψ P) ⟨tens θ τ fr (S t) Ψ, memQ (S t)⟩
      _ hΦt g x
    rw [← e, key]
    rfl

  let ev : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℝ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℝ (fr⁻¹ * compAt θ τ x)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℝ (Fin V.rank → Fin n → ℂ) ℂ)
  have hev : ∀ T, ev T = T (fr⁻¹ * compAt θ τ x) := fun T => rfl
  have hT : Filter.Tendsto (fun t : ℝ => (ev.comp L) (t⁻¹ • (S t - S 0))) (nhdsWithin 0 {0}ᶜ)
      (nhds ((ev.comp L) S')) := ((ev.comp L).continuous.tendsto S').comp hder
  have hd : HasDerivAt (fun t : ℝ => ev (L (S t))) (ev (L S')) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine hT.congr' (Filter.Eventually.of_forall fun t => ?_)
    simp only [slope_def_module, sub_zero, map_smul, map_sub, ContinuousLinearMap.comp_apply]
  have hd' : HasDerivAt (fun t : ℝ => (L (S t)) (fr⁻¹ * compAt θ τ x) * Ψ' x)
      ((L S') (fr⁻¹ * compAt θ τ x) * Ψ' x) 0 := by
    simpa only [hev] using hd.mul_const (Ψ' x)
  unfold DX
  rw [hLHS, ← hd'.deriv]
  congr 1
  funext t
  exact (hgc t).symm

end PositivityTheory.Rg.Sw.Glob
end
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem top6 (hF : FTfact) (hG : GenA) (hSD : SchDeriv) (hDO : DerivOne) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  have hAA : AwayAct := awayAct_of hG hF decompAway
  top5 (locFact_of decomp (opGen_of hF)) hAA
    (lieComm_of awayIn lNe schFP (opCLM_of' hF) (awayFact_of hAA decompAway) hSD) hDO hId hC

end PositivityTheory.Rg.Sw.Glob
end
