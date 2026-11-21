import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ExistsUnitaryDiag
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousAtMN
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RealParExplicit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRange
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocFactPf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ValZeroOfTens
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitSt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.InvGroup
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LamTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseTau
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TwoSided

section
noncomputable section

namespace PositivityTheory.Rg.Sw.Glob

theorem holValueAt_finsum {ι : Type} (T : Finset ι) {f : ι → ℂ → ℂ} {c : ι → ℂ} {s₀ : ℂ}
    (h : ∀ i ∈ T, GlobalTheory.Cont.HolValueAt (f i) s₀ (c i)) :
    GlobalTheory.Cont.HolValueAt (fun s => ∑ i ∈ T, f i s) s₀ (∑ i ∈ T, c i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using GlobalTheory.Cont.holValueAt_const 0 s₀
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cosetSum_finsum {G : Type} [Group G] (Pp Γ : Subgroup G) {ι : Type} (T : Finset ι) (f : ι → G → ℂ) (g : G)
    (h : ∀ i ∈ T, GlobalTheory.Eis.CosetConv Pp Γ (f i) g) :
    GlobalTheory.Eis.cosetSum Pp Γ (fun x => ∑ i ∈ T, f i x) g = ∑ i ∈ T, GlobalTheory.Eis.cosetSum Pp Γ (f i) g := by
  unfold GlobalTheory.Eis.cosetSum GlobalTheory.Eis.term
  exact Summable.tsum_finsetSum fun i hi => (h i hi).of_norm

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

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ}
    {Ψ : Mx D m n → ℂ} {Q : PX m n} (h : tens θ τ fr (fP c Q) Ψ ∈ schwartzA θ m n) :
    (phiS θ τ fr c Ψ Q).1 = tens θ τ fr (fP c Q) Ψ := by
  unfold phiS
  rw [dif_pos h]

theorem perPsi (hA : AbsThm) (hTM : TensMem) (hLo : LocOpEx) (hLi : LocInst) (hLS : LinSec) (hGS : GSplit)
    (hIa : GIauto) (hIk : GIk) (hIi : GIinv) (hId : GIdil) (hEis : EisStrong) (hLB : GLamBd) (hLsg : GLsing)
    (hCo : PositivityTheory.PfSWUS.CoefND) (hLZ : LNZ)
    {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ)
    (Q : PX V.rank n) (g : G D n) :
    HolValueAt (PositivityTheory.PfSWUS.eis ω H (phiS θ τ fr (cLoc l τ) Ψ Q) g) (s0 V n)
      (thetaInt ω ν (phiS θ τ fr (cLoc l τ) Ψ Q) g) := by
  have hl0 := hLZ D ψ θ l hcx.hψ hcx.hθ hcx.hl
  have hmem := hTM D n V θ l s τ ε fr hcx.hθ hl0 hcx.hs hcx.hfr Ψ hΨ
  obtain ⟨L, hL⟩ := hLo D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx
  obtain ⟨sL, ρ, p, q, e, hgood, hLD, hsL, hρ⟩ := hLi D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨sec, I, hsec, hI⟩ := hLS D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ
  have hstd1 : PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ 1) :=
    ⟨hcx.hψ, hcx.hχ, hcx.hη, hcx.hθ, hcx.hμ, hcx.hω, hcx.hH, hcx.hl, hcx.hs, hcx.hν,
      by rw [phiS_val (hmem 1).1]; exact (hmem 1).2⟩
  have hsecSec : IsSection χ (s0 V n) (fun x => sec 1 x) := by
    obtain ⟨𝓕, h𝓕⟩ := hcx.hμ
    have := GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hcx.hψ χ hcx.hχ hcx.hη θ hcx.hθ μ 𝓕 h𝓕 ω hcx.hω
      l hcx.hl s hcx.hs _ hstd1.hΦ
    rw [hsec 1]
    exact this
  have hn0 : 0 < n := hcx.hn
  have hGD : GlobData ε (cLoc l τ) sL ρ (G D n) (P D n) (GF D n) ι (s0 V n) H sec I (lamSet ψ) := {
    ιcont := hcx.hι.1
    split := by
      intro g
      obtain ⟨x, y, S, r, hr, hg, hx⟩ := hGS D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL Ψ hΨ g
      refine ⟨x, y, S, r, hr, hg, fun y' => ⟨(hx y').1, fun Q' => ?_⟩⟩
      rw [hsec Q', hsL Q' y']
      exact (hx y').2 Q'
    Icont := by
      rw [hI 1]
      exact (hIa D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ).1
    Ileft := by
      rw [hI 1]
      exact (hIa D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ).2
    Ik := by
      intro Q' g k hk
      rw [hI Q', hI (ρ k Q')]
      exact hIk D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL ρ hρ Ψ hΨ Q' g k hk
    Iinv := by
      intro g a b Q'
      rw [hI]
      exact hIi D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ g a b Q'
    Idil := by
      intro g X a ha
      obtain ⟨U, F, hU, hU', hFc, hF⟩ := hId D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ g X a ha
      refine ⟨U, F, hU, hU', hFc, fun y => ⟨(hF y).1, fun t => ?_, fun r => ?_⟩⟩
      · rw [hI]
        exact (hF y).2.1 t
      · rw [hI]
        exact (hF y).2.2 r
    eis := hEis D n hn0 χ V.rank hcx.hχ hcx.hη H hcx.hH (s0 V n) _ hsecSec (s0 V n)
    Λadd := fun L' hL' => (hLB D n ψ hcx.hψ L' hL').1
    Λbd := fun L' hL' => (hLB D n ψ hcx.hψ L' hL').2
    Λsing := fun F hF hinv hz => hLsg D n ψ θ τ ι hcx.hψ hcx.hθ hcx.hι F hF hinv hz
    Λval := by
      rintro L' ⟨nb, lam, 𝓖, β, g', hcd, hβ, rfl⟩
      have := hCo D n V ψ χ θ μ ω H l s ν _ hstd1 hcx.hr nb lam 𝓖 hcd β hβ g'
      rw [hI 1, hsec 1]
      exact this }
  have := hA V.rank n ε (cLoc l τ) (tLoc l τ) p q e sL ρ hLD hgood (G D n) (P D n) (GF D n) ι (s0 V n) H sec I
    (lamSet ψ) hGD Q g
  rw [hsec Q, hI Q] at this
  exact this

theorem main : MainSt := by
  intro hA hFr hEmb hSig hSp hTM hLo hLi hLS hGS hIa hIk hIi hId hEis hLB hLsg hCo hCR hTL hLZ
  intro D n V ψ χ θ μ ω H l s ν Φ hStd hR hn g
  obtain ⟨τ, hτ⟩ := hSig D n V s hR hStd.hs
  obtain ⟨ε, fr, hfr⟩ := hFr D V τ s (hStd.hs τ)
  obtain ⟨ι, hι⟩ := hEmb D n θ τ hStd.hθ
  have hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι :=
    ⟨hStd.hψ, hStd.hχ, hStd.hη, hStd.hθ, hStd.hμ, hStd.hω, hStd.hH, hStd.hl, hStd.hs, hStd.hν, hR, hn, hfr, hι,
      hτ ε fr hfr⟩
  have hl0 := hLZ D ψ θ l hStd.hψ hStd.hθ hStd.hl
  obtain ⟨k, Pi, Ψi, hΨ, hsum⟩ := hSp D n V θ l s τ ε fr hStd.hθ hfr Φ.1 hStd.hΦ
  have hmem : ∀ i, tens θ τ fr (fP (cLoc l τ) (Pi i)) (Ψi i) ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) (Pi i)) (Ψi i) ∈ fockA θ V n l s :=
    fun i => hTM D n V θ l s τ ε fr hStd.hθ hl0 hStd.hs hfr (Ψi i) (hΨ i) (Pi i)
  let Φi : Fin k → schwartzA θ V.rank n := fun i => phiS θ τ fr (cLoc l τ) (Ψi i) (Pi i)
  have hval : ∀ i, (Φi i).1 = tens θ τ fr (fP (cLoc l τ) (Pi i)) (Ψi i) := fun i => phiS_val (hmem i).1
  have hΦeq : Φ = ∑ i, Φi i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [hval]
    exact hsum
  have hstdT : ∀ T : Finset (Fin k), PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (∑ i ∈ T, Φi i) := fun T =>
    ⟨hStd.hψ, hStd.hχ, hStd.hη, hStd.hθ, hStd.hμ, hStd.hω, hStd.hH, hStd.hl, hStd.hs, hStd.hν, by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ => by rw [hval]; exact (hmem i).2⟩
  have hstdi : ∀ i, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (Φi i) := fun i =>
    ⟨hStd.hψ, hStd.hχ, hStd.hη, hStd.hθ, hStd.hμ, hStd.hω, hStd.hH, hStd.hl, hStd.hs, hStd.hν, by
      rw [hval]; exact (hmem i).2⟩
  have key : ∀ i, HolValueAt (PositivityTheory.PfSWUS.eis ω H (Φi i) g) (s0 V n) (thetaInt ω ν (Φi i) g) := fun i =>
    perPsi hA hTM hLo hLi hLS hGS hIa hIk hIi hId hEis hLB hLsg hCo hLZ hcx (hΨ i) (Pi i) g
  have hth : ∀ T : Finset (Fin k), thetaInt ω ν (∑ i ∈ T, Φi i) g = ∑ i ∈ T, thetaInt ω ν (Φi i) g := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have h0 := hTL D n V ψ χ θ μ ω H l s ν 0 0 (by simpa using hstdT ∅) (by simpa using hstdT ∅) hR g
      rw [add_zero] at h0
      simp only [Finset.sum_empty]
      linear_combination -h0
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hTL D n V ψ χ θ μ ω H l s ν _ _ (hstdi a) (hstdT T) hR g, ih]
  choose σi hσi using fun i => hCR D n V ψ χ θ μ ω H l s ν (Φi i) (hstdi i) hR
  have hsect : ∀ z, sect ω H (∑ i, Φi i) z = fun x => ∑ i, sect ω H (Φi i) z x := by
    intro z
    funext x
    simp only [sect, map_sum, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
  have heq : EqRight (fun z => ∑ i, PositivityTheory.PfSWUS.eis ω H (Φi i) g z) (PositivityTheory.PfSWUS.eis ω H Φ g) := by
    refine ⟨∑ i, |σi i|, fun z hz => ?_⟩
    have hz' : ∀ i, σi i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (σi j)) (Finset.mem_univ i))) hz
    show ∑ i, PositivityTheory.PfSWUS.eis ω H (Φi i) g z = PositivityTheory.PfSWUS.eis ω H Φ g z
    rw [hΦeq]
    unfold PositivityTheory.PfSWUS.eis
    rw [hsect z, cosetSum_finsum _ _ _ _ _ (fun i _ => hσi i z (hz' i) g)]
  have hv : thetaInt ω ν Φ g = ∑ i, thetaInt ω ν (Φi i) g := by
    rw [hΦeq]
    exact hth Finset.univ
  rw [hv]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq

end PositivityTheory.Rg.Sw.Glob
end
end

section
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open EmbP
open Formalism.IndefR.Eqv (psiT thetaC eq_thetaC)

variable {D : D7} {n : ℕ}

theorem reidx_mul (a b : M2 n) : reidx (a * b) = reidx a * reidx b := by
  simp only [reidx, Matrix.submatrix_mul_equiv]

theorem reidx_one : reidx (1 : M2 n) = 1 := Matrix.submatrix_one_equiv _

theorem reidx_conjTranspose (a : M2 n) : reidx aᴴ = (reidx a)ᴴ := by
  simp only [reidx, Matrix.conjTranspose_submatrix]

theorem continuous_reidx : Continuous (fun a : M2 n => reidx a) :=
  continuous_id.matrix_submatrix _ _

theorem Jst_map (τ : D.what₂.Tau) : (Jst D n).map (tauE D τ) = reidx (JJ n) := by
  ext i j
  simp only [Jst, blk4, reidx, JJ, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem mR_mul_inv (a : GR n) : mR a * mR a⁻¹ = 1 := by
  rw [← mR_mul, mul_inv_cancel, mR_one]

theorem mR_inv_mul (a : GR n) : mR a⁻¹ * mR a = 1 := by
  rw [← mR_mul, inv_mul_cancel, mR_one]

theorem reidx_unitary (τ : D.what₂.Tau) (y : GR n) :
    (reidx (mR y))ᴴ * (Jst D n).map (tauE D τ) * reidx (mR y) = (Jst D n).map (tauE D τ) := by
  have h : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  rw [Jst_map, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, h]

def iotaF (τ : D.what₂.Tau) (y : GR n) : G D n :=
  (⟨⟨atMN D τ (reidx (mR y)), atMN D τ (reidx (mR y⁻¹)),
      by rw [← atMN_mul, ← reidx_mul, mR_mul_inv, reidx_one, atMN_one],
      by rw [← atMN_mul, ← reidx_mul, mR_inv_mul, reidx_one, atMN_one]⟩,
    atMN_unitary D τ (Jst D n) _ (reidx_unitary τ y)⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))


def iota (τ : D.what₂.Tau) : GR n →* G D n where
  toFun := iotaF τ
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show atMN D τ (reidx (mR 1)) = 1
    rw [mR_one, reidx_one, atMN_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    show atMN D τ (reidx (mR (a * b))) = atMN D τ (reidx (mR a)) * atMN D τ (reidx (mR b))
    rw [mR_mul, reidx_mul, atMN_mul]

theorem continuous_iota (τ : D.what₂.Tau) : Continuous (iota (D := D) (n := n) τ) := by
  have hm : Continuous fun y : GR n => mR y := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun y : GR n => mR y⁻¹ := hm.comp continuous_inv
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_atMN D τ).comp (continuous_reidx.comp hm)
  · exact (continuous_atMN D τ).comp (continuous_reidx.comp hmi)

theorem sEmb : SEmb := by
  intro D n θ τ hθ
  obtain rfl := eq_thetaC D hθ
  refine ⟨iota τ, continuous_iota τ, fun y => ⟨?_, fun τ' hτ' => ?_, ?_⟩⟩
  · have e := psi_atMN D τ τ (reidx (mR y))
    rw [if_pos rfl] at e
    exact e
  · have e := psi_atMN D τ τ' (reidx (mR y))
    rw [if_neg hτ'] at e
    exact e
  · exact fin_atMN D τ (reidx (mR y))

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

namespace PositivityTheory.Rg.Sw.Glob

theorem gIk : GIk := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι _hC L hL ρ hρ Ψ hΨ P g k hk
  have key : ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P) = phiS θ τ fr (cLoc l τ) Ψ (ρ k P) := by
    have h1 := hL k Ψ hΨ P
    rw [hρ k P hk] at h1
    have hmem : tens θ τ fr (fP (cLoc l τ) (ρ k P)) Ψ ∈ schwartzA θ V.rank n := by
      rw [← h1]; exact (ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P)).2
    apply Subtype.ext
    rw [h1]
    unfold phiS
    rw [dif_pos hmem]
  unfold thF thetaInt theta
  simp only [map_mul, Module.End.mul_apply, key]

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

namespace PositivityTheory.Rg.Sw.Glob

theorem gIauto_of (hT : PositivityTheory.PfSWUS.ThetaAuto) (hM : TensMem) : GIauto := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC Ψ hΨ
  have hm := hM D n V θ l s τ ε fr hC.hθ (lNZ D ψ θ l hC.hψ hC.hθ hC.hl) hC.hs hC.hfr Ψ hΨ 1
  have hphi : (phiS θ τ fr (cLoc l τ) Ψ 1).1 = tens θ τ fr (fP (cLoc l τ) 1) Ψ := by
    unfold phiS
    rw [dif_pos hm.1]
  have hStd : PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ 1) :=
    ⟨hC.hψ, hC.hχ, hC.hη, hC.hθ, hC.hμ, hC.hω, hC.hH, hC.hl, hC.hs, hC.hν, by rw [hphi]; exact hm.2⟩
  obtain ⟨h1, h2⟩ := hT D n V ψ χ θ μ ω H l s ν _ hStd hC.hr
  exact ⟨h1, fun γ hγ g => h2 γ hγ g⟩

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

namespace PositivityTheory.Rg.Sw.Glob

theorem convRight_of (hE : EisStrong) : ConvRight := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR
  have hn : 0 < n := by
    obtain ⟨h1, h2, -⟩ := hR
    omega
  obtain ⟨𝓕, h𝓕⟩ := hS.hμ
  have hsec : IsSection χ (s0 V n) (fun g : G D n => (ω g Φ).1 0) :=
    GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μ 𝓕 h𝓕 ω hS.hω l hS.hl s hS.hs Φ
      hS.hΦ
  obtain ⟨U, d, E, σ, -, -, -, -, -, -, -, hconv⟩ :=
    hE D n hn χ V.rank hS.hχ hS.hη H hS.hH (s0 V n) _ hsec (s0 V n)
  refine ⟨σ, fun z hz g => ?_⟩
  obtain ⟨u, hu, hb⟩ := (hconv z hz).1 {g} isCompact_singleton
  exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hb g rfl q) hu

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

namespace PositivityTheory.Rg.Sw.Glob

theorem summable_of_absTheta {D : D7} {V : HSp D} {n : ℕ} (φ : Mx D V.rank n → ℂ) (h : GA D V)
    (hh : GlobalTheory.SiegelFormula.absTheta V φ h < ⊤) :
    Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => φ (GlobalTheory.SiegelFormula.invPt V h ξ) :=
  Summable.of_enorm hh.ne

theorem thLin_of (hP : GlobalTheory.Published.WeilThetaConvergence) : ThLin := by
  intro D n V ψ χ θ μ ω H l s ν Φ Φ' hS hS' hR g
  obtain ⟨h1, h2, hr⟩ := hR
  have hn : 1 ≤ n := by omega
  have hI := GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ g
  have hI' := GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ' g
  have hae : ∀ φ : schwartzA θ V.rank n,
      ∀ᵐ q ∂autMeasure V ν, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ.1) q < ⊤ := by
    intro φ
    have hfin : GlobalTheory.SiegelFormula.absThetaInt V ν φ.1 < ⊤ := hP D n V hn (Or.inr hr) θ hS.hθ ν hS.hν φ
    have hcont : Continuous φ.1 := (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hS.hθ _ _ φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hS.hθ _ _ φ.1 φ.2)).1
    exact ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hcont) hfin.ne
  have heq : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (Φ + Φ') g) q) =ᵐ[autMeasure V ν]
      fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q + GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ' g) q := by
    filter_upwards [hae (ω g Φ), hae (ω g Φ')] with q hq hq'
    simp only [GlobalTheory.AutomorphicL2Unitary.descend] at hq hq' ⊢
    have s1 := summable_of_absTheta (ω g Φ).1 _ hq
    have s2 := summable_of_absTheta (ω g Φ').1 _ hq'
    show (∑' ξ, (ω g (Φ + Φ')).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) =
      (∑' ξ, (ω g Φ).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) + ∑' ξ, (ω g Φ').1 (GlobalTheory.SiegelFormula.invPt V _ ξ)
    rw [← s1.tsum_add s2]
    congr 1
    funext ξ
    simp [map_add]
  unfold thetaInt
  rw [MeasureTheory.average_eq, MeasureTheory.average_eq, MeasureTheory.average_eq, integral_congr_ae heq,
    integral_add hI hI', smul_add]

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

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem trace_frame {m : ℕ} {M fr : Matrix (Fin m) (Fin m) ℂ} (h1 : IsUnit fr.det) (h2 : frᴴ * M * fr = 1)
    (z : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (zᴴ * M * z) = ((∑ a, ∑ i, ‖(fr⁻¹ * z) a i‖ ^ 2 : ℝ) : ℂ) := by
  set y := fr⁻¹ * z with hy
  have hz : z = fr * y := by rw [hy, Matrix.mul_nonsing_inv_cancel_left _ _ h1]
  have e : zᴴ * M * z = yᴴ * y := by
    rw [hz, Matrix.conjTranspose_mul]
    calc yᴴ * frᴴ * M * (fr * y) = yᴴ * (frᴴ * M * fr) * y := by simp only [Matrix.mul_assoc]
      _ = yᴴ * y := by rw [h2, Matrix.mul_one]
  rw [e, Matrix.trace]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_apply, ← Complex.conj_mul']
  rfl

theorem gauss_split {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (l : D.what₂.Tau → ℝ)
    (hfr : IsTauFrame V τ s ε fr) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) :
    gauss V l s z = gs (cLoc l τ) (fr⁻¹ * z τ) * gAway V l s τ z := by
  classical
  unfold gauss gAway gs cLoc
  rw [← Complex.exp_add]
  congr 1
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ τ), trace_frame hfr.1 hfr.2.2 (z τ)]
  have hf : (Finset.univ.filter fun τ' => τ' ≠ τ) = Finset.univ.erase τ := by
    ext x; simp
  rw [hf]
  push_cast
  ring

theorem evalPoly_add {m : ℕ} (p q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (p + q) z = evalPoly p z + evalPoly q z := by
  simp [evalPoly]

theorem evalPoly_mul {m : ℕ} (p q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (p * q) z = evalPoly p z * evalPoly q z := by
  simp [evalPoly]

theorem evalPoly_C {m : ℕ} (a : ℂ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.C a : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) z = a := by
  simp [evalPoly]

theorem evalPoly_X {m : ℕ} (v : D.what₂.Tau × Fin m × Fin n × Bool) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.X v : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) z =
      if v.2.2.2 then conj (z v.1 v.2.1 v.2.2.1) else z v.1 v.2.1 v.2.2.1 := by
  simp [evalPoly]

theorem eval_bind₁' {σ ι : Type*} (f : σ → ℂ) (g : ι → MvPolynomial σ ℂ) (p : MvPolynomial ι ℂ) :
    MvPolynomial.eval f (MvPolynomial.bind₁ g p) = MvPolynomial.eval (fun i => MvPolynomial.eval f (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

def polyAt {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ :=
  MvPolynomial.bind₁ (fun k : Fin m × Fin n × Bool => if k.2.2 then
      ∑ a, MvPolynomial.C (star ((fr⁻¹) k.1 a)) * MvPolynomial.X (τ, a, k.2.1, true)
    else ∑ a, MvPolynomial.C ((fr⁻¹) k.1 a) * MvPolynomial.X (τ, a, k.2.1, false)) P

theorem evalPoly_polyAt {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (P : PX m n)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (polyAt τ fr P) z = evX P (fr⁻¹ * z τ) := by
  unfold evalPoly polyAt evX
  refine (eval_bind₁' _ _ _).trans (congrArg (fun f => MvPolynomial.eval f P) (funext fun k => ?_))
  obtain ⟨c, i, b⟩ := k
  cases b <;> simp [Matrix.mul_apply, star_sum]

theorem poly_split {m : ℕ} (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ} (hfr : IsUnit fr.det)
    (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    ∃ (k : ℕ) (Pi : Fin k → PX m n) (pi : Fin k → MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ),
      (∀ i, ∀ v ∈ (pi i).vars, v.1 ≠ τ) ∧
      ∀ z, evalPoly p z = ∑ i, evX (Pi i) (fr⁻¹ * z τ) * evalPoly (pi i) z := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨1, fun _ => MvPolynomial.C a, fun _ => 1, by simp, fun z => ?_⟩
    simp [evalPoly, evX]
  | add p q hp hq =>
    obtain ⟨k1, P1, p1, h1, e1⟩ := hp
    obtain ⟨k2, P2, p2, h2, e2⟩ := hq
    refine ⟨k1 + k2, Fin.append P1 P2, Fin.append p1 p2, ?_, fun z => ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using h1 j
      · simpa using h2 j
    · rw [Fin.sum_univ_add, evalPoly_add, e1, e2]
      simp
  | mul_X p v hp =>
    obtain ⟨k, Pi, pi, h, e⟩ := hp
    by_cases hv : v.1 = τ
    · refine ⟨k, fun i => Pi i * (if v.2.2.2 then ∑ c, MvPolynomial.C (star (fr v.2.1 c)) * MvPolynomial.X (c, v.2.2.1, true)
          else ∑ c, MvPolynomial.C (fr v.2.1 c) * MvPolynomial.X (c, v.2.2.1, false)), pi, h, fun z => ?_⟩
      have hz : z τ = fr * (fr⁻¹ * z τ) := (Matrix.mul_nonsing_inv_cancel_left _ _ hfr).symm
      have hw : (if v.2.2.2 then conj (z v.1 v.2.1 v.2.2.1) else z v.1 v.2.1 v.2.2.1) =
          evX (if v.2.2.2 then ∑ c, MvPolynomial.C (star (fr v.2.1 c)) * MvPolynomial.X (c, v.2.2.1, true)
            else ∑ c, MvPolynomial.C (fr v.2.1 c) * MvPolynomial.X (c, v.2.2.1, false)) (fr⁻¹ * z τ) := by
        rw [hv]
        conv_lhs => rw [hz]
        split_ifs <;> simp [evX, Matrix.mul_apply, map_sum]
      rw [evalPoly_mul, e, evalPoly_X, hw, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [evX, map_mul]
      ring
    · refine ⟨k, Pi, fun i => pi i * MvPolynomial.X v, fun i w hw => ?_, fun z => ?_⟩
      · have := MvPolynomial.vars_mul (pi i) (MvPolynomial.X v) hw
        rw [Finset.mem_union, MvPolynomial.vars_X] at this
        rcases this with h' | h'
        · exact h i w h'
        · rw [Finset.mem_singleton] at h'
          rw [h']
          exact hv
      · rw [evalPoly_mul, e, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [evalPoly_mul]
        ring

theorem splitFock : SplitFock := by
  intro D n V θ l s τ ε fr _ hfr Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, rfl⟩ := hφ
    obtain ⟨k, Pi, pi, hpi, e⟩ := poly_split τ hfr.1 p
    refine ⟨k, Pi, fun i x => evalPoly (pi i) (fun τ => compAt θ τ x) * gAway V l s τ (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j)), fun i => Submodule.subset_span ⟨pi i, g, hg, hpi i, rfl⟩, ?_⟩
    funext x
    rw [Finset.sum_apply, e, gauss_split l hfr, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [tens, fP]
    ring
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k1, P1, Ψ1, h1, e1⟩ := hx
    obtain ⟨k2, P2, Ψ2, h2, e2⟩ := hy
    refine ⟨k1 + k2, Fin.append P1 P2, Fin.append Ψ1 Ψ2,
      fun i => Fin.addCases (fun j => by simpa using h1 j) (fun j => by simpa using h2 j) i, ?_⟩
    rw [Fin.sum_univ_add, e1, e2]
    simp
  | smul a x _ hx =>
    obtain ⟨k, Qs, Ψi, h, e⟩ := hx
    refine ⟨k, Qs, fun i => a • Ψi i, fun i => Submodule.smul_mem _ a (h i), ?_⟩
    rw [e, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [tens, Pi.smul_apply, smul_eq_mul]
    ring

theorem tens_zero {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) : tens θ τ fr f (0 : Mx D m n → ℂ) = 0 := by
  funext x; simp [tens]

theorem tens_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) (Ψ Ψ' : Mx D m n → ℂ) : tens θ τ fr f (Ψ + Ψ') = tens θ τ fr f Ψ + tens θ τ fr f Ψ' := by
  funext x; simp [tens, mul_add]

theorem tens_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) (a : ℂ) (Ψ : Mx D m n → ℂ) : tens θ τ fr f (a • Ψ) = a • tens θ τ fr f Ψ := by
  funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring

theorem tensMem_fock {V : HSp D} {θ : InfFam D} {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ) (P : PX V.rank n) :
    tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ fockA θ V n l s := by
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, -, rfl⟩ := hφ
    refine Submodule.subset_span ⟨polyAt τ fr P * p, g, hg, ?_⟩
    funext x
    simp only [tens, fP, evalPoly_mul, evalPoly_polyAt, gauss_split l hfr]
    ring
  | zero => rw [tens_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [tens_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [tens_smul]; exact Submodule.smul_mem _ a hx

def coordCLM {m : ℕ} (v : D.what₂.Tau × Fin m × Fin n × Bool) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) v.2.2.1).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) v.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) v.1))

theorem hasTemperateGrowth_evalPoly {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (w τ))) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (MvPolynomial.C a) (fun τ => Matrix.of (w τ))) =
        fun _ => a := funext fun w => evalPoly_C a _
    rw [e]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (w τ))) =
        (fun w => evalPoly p (fun τ => Matrix.of (w τ))) + fun w => evalPoly q (fun τ => Matrix.of (w τ)) :=
      funext fun w => evalPoly_add p q _
    rw [e]
    exact hp.add hq
  | mul_X p v hp =>
    have hc : Function.HasTemperateGrowth (fun w : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if v.2.2.2 then conj (w v.1 v.2.1 v.2.2.1) else w v.1 v.2.1 v.2.2.1) := by
      split_ifs
      · exact (Complex.conjCLE.toContinuousLinearMap.comp (coordCLM v)).hasTemperateGrowth
      · exact (coordCLM v).hasTemperateGrowth
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X v) (fun τ => Matrix.of (w τ))) =
        (fun w => evalPoly p (fun τ => Matrix.of (w τ))) *
          fun w => if v.2.2.2 then conj (w v.1 v.2.1 v.2.2.1) else w v.1 v.2.1 v.2.2.1 :=
      funext fun w => by rw [evalPoly_mul, evalPoly_X]; rfl
    rw [e]
    exact hp.mul hc

theorem fockA_le_schwartzA {V : HSp D} {θ : InfFam D} {l : D.what₂.Tau → ℝ} (hl : ∀ τ, l τ ≠ 0)
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    fockA θ V n l s ≤ schwartzA θ V.rank n := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  refine Submodule.subset_span ⟨SchwartzMap.smulLeftCLM ℂ (fun w => evalPoly p (fun τ => Matrix.of (w τ))) f, g, hg, ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_evalPoly p), hf, smul_eq_mul]
  rfl

theorem tensMem : TensMem := by
  intro D n V θ l s τ ε fr _ hl hs hfr Ψ hΨ P
  have h := tensMem_fock hfr hΨ P
  exact ⟨fockA_le_schwartzA hl hs h, h⟩

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

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem thetaInt_smul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (ν : Measure (GA D V)) (Φ : schwartzA θ V.rank n) (a : ℂ) (g : G D n) :
    thetaInt ω ν (a • Φ) g = a * thetaInt ω ν Φ g := by
  have h : GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (a • Φ) g) = fun q => a * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q := by
    funext q
    simp [GlobalTheory.AutomorphicL2Unitary.descend, theta, map_smul, tsum_mul_left]
  simp only [thetaInt, h, MeasureTheory.average, MeasureTheory.integral_const_mul]

theorem tens_fP_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (Ψ : Mx D m n → ℂ) (P Q : PX m n) :
    tens θ τ fr (fP c (P + Q)) Ψ = tens θ τ fr (fP c P) Ψ + tens θ τ fr (fP c Q) Ψ := by
  funext x
  simp only [tens, fP, evX, map_add, Pi.add_apply]
  ring

theorem tens_fP_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (Ψ : Mx D m n → ℂ) (a : ℂ) (P : PX m n) :
    tens θ τ fr (fP c (a • P)) Ψ = a • tens θ τ fr (fP c P) Ψ := by
  funext x
  simp only [tens, fP, evX, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
  ring

theorem linSec_of : ThLin → LinSec := by
  intro hTL D n V ψ χ θ μ ω H l s ν τ ε fr ι c Ψ hΨ
  have hl0 : ∀ τ, l τ ≠ 0 := lNZ D ψ θ l c.hψ c.hθ c.hl
  have hm : ∀ P, tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ fockA θ V n l s :=
    fun P => tensMem D n V θ l s τ ε fr c.hθ hl0 c.hs c.hfr Ψ hΨ P
  have hphi : ∀ P, phiS θ τ fr (cLoc l τ) Ψ P = ⟨_, (hm P).1⟩ := fun P => dif_pos (hm P).1
  have hadd : ∀ P Q, phiS θ τ fr (cLoc l τ) Ψ (P + Q) = phiS θ τ fr (cLoc l τ) Ψ P + phiS θ τ fr (cLoc l τ) Ψ Q := by
    intro P Q
    rw [hphi, hphi, hphi]
    exact Subtype.ext (tens_fP_add θ τ fr _ Ψ P Q)
  have hsmul : ∀ (a : ℂ) P, phiS θ τ fr (cLoc l τ) Ψ (a • P) = a • phiS θ τ fr (cLoc l τ) Ψ P := by
    intro a P
    rw [hphi, hphi]
    exact Subtype.ext (tens_fP_smul θ τ fr _ Ψ a P)
  have hstd : ∀ P, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ P) := fun P =>
    ⟨c.hψ, c.hχ, c.hη, c.hθ, c.hμ, c.hω, c.hH, c.hl, c.hs, c.hν, by rw [hphi]; exact (hm P).2⟩
  refine ⟨{ toFun := fun P => secF ω τ fr (cLoc l τ) Ψ P
            map_add' := fun P Q => by
              funext g
              simp only [secF, hadd, map_add, Submodule.coe_add, Pi.add_apply]
            map_smul' := fun a P => by
              funext g
              simp only [secF, hsmul, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] },
          { toFun := fun P => thF ω ν τ fr (cLoc l τ) Ψ P
            map_add' := fun P Q => by
              funext g
              simp only [thF, Pi.add_apply]
              rw [hadd]
              exact hTL D n V ψ χ θ μ ω H l s ν _ _ (hstd P) (hstd Q) c.hr g
            map_smul' := fun a P => by
              funext g
              simp only [thF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
              rw [hsmul]
              exact thetaInt_smul ω ν _ a g }, fun P => rfl, fun P => rfl⟩

end PositivityTheory.Rg.Sw.Glob
end
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem locOpEx_of_locFact (hF : LocFact) : LocOpEx := locOpEx_of_fact hF awayIn schFP lNe

end PositivityTheory.Rg.Sw.Glob
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem gIwasawa : GIwasawa := GlobalTheory.StdUnn.Iwasawa.exists_mul

end PositivityTheory.Rg.Sw.Glob
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

def xyC (Z : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (Z a c) * MvPolynomial.X (c, i, b)

def vfC (c : ℝ) (Zh Za : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyC Zh a i false * pderiv (a, i, false) P + xyC Za a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyC Zh a i false * MvPolynomial.X (a, i, true) + xyC Za a i true * MvPolynomial.X (a, i, false)) * P)

theorem vfX_eq (c : ℝ) (Z : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : vfX c Z P = vfC c Z (Z.map star) P := by
  have h1 : ∀ a (i : Fin n), xyP Z a i false = xyC Z a i false := fun a i => by simp [xyP, xyC]
  have h2 : ∀ a (i : Fin n), xyP Z a i true = xyC (Z.map star) a i true := fun a i => by simp [xyP, xyC, Matrix.map_apply]
  simp only [vfX, vfC, h1, h2]

theorem xyC_add_smul (Z Z' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    xyC (Z + r • Z') a i b = xyC Z a i b + C r * xyC Z' a i b := by
  simp only [xyC, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem vfC_lin (c : ℝ) (Zh Za Zh' Za' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (P : PX m n) :
    vfC c Zh Za P + r • vfC c Zh' Za' P = vfC c (Zh + r • Zh') (Za + r • Za') P := by
  simp only [vfC, xyC_add_smul, smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem xyC_single (a b a' : Fin m) (r : ℂ) (i : Fin n) (β : Bool) :
    xyC (r • Matrix.single a b (1 : ℂ)) a' i β = if a' = a then C r * MvPolynomial.X (b, i, β) else 0 := by
  by_cases h : a' = a
  · subst h
    simp only [xyC, Matrix.smul_apply, Matrix.single_apply, true_and, smul_eq_mul, mul_ite, mul_one,
      mul_zero, if_true]
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  · simp [xyC, Matrix.single_apply, h, Ne.symm h]

theorem sgn_star (ε : Fin m → Bool) (a : Fin m) : star (sgn ε a) = sgn ε a := by
  unfold sgn; split_ifs <;> simp

theorem zRe_add_zIm (ε : Fin m → Bool) (a b : Fin m) :
    zRe ε a b + Complex.I • zIm ε a b = (1 : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem zRe_add_zIm_star (ε : Fin m → Bool) (a b : Fin m) :
    (zRe ε a b).map star + Complex.I • (zIm ε a b).map star = (-(sgn ε a * sgn ε b)) • Matrix.single b a (1 : ℂ) := by
  have hs : (starRingEnd ℂ) (sgn ε a) = sgn ε a := sgn_star ε a
  have ht : (starRingEnd ℂ) (sgn ε b) = sgn ε b := sgn_star ε b
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply,
    smul_eq_mul, Matrix.neg_apply, Matrix.single_apply, Complex.star_def]
  split_ifs <;> simp [map_add, map_mul, map_neg, map_sub, hs, ht, h2, Complex.conj_I] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem hOp_eq (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (P : PX m n) :
    hOp ε c a b P = vfX c (zRe ε a b) P + Complex.I • vfX c (zIm ε a b) P := by
  rw [vfX_eq, vfX_eq, vfC_lin, zRe_add_zIm, zRe_add_zIm_star]
  unfold vfC hOp
  simp only [xyC_single]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, add_mul, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [map_neg, map_one, map_mul, map_sub]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH
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

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

theorem isUe_zRe (ε : Fin m → Bool) (a b : Fin m) : IsUe ε (zRe ε a b) := by
  have e1 : star ((1 : ℂ) / 2) = 1 / 2 := by simp
  ext i j
  simp only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, zRe, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_sub, e1]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
    simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>
    (try subst_vars) <;> unfold sgn <;> split_ifs <;>
    first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | norm_num | (simp only [star_one, star_zero]; norm_num)

theorem isUe_zIm (ε : Fin m → Bool) (a b : Fin m) : IsUe ε (zIm ε a b) := by
  have e2 : star (-(Complex.I / 2)) = Complex.I / 2 := by
    apply Complex.ext <;> simp <;> norm_num
  ext i j
  simp only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, zIm, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_add, e2]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
    simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>
    (try subst_vars) <;> unfold sgn <;> split_ifs <;>
    first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | ring | (simp only [star_one, star_zero]; norm_num)

theorem thetaInt_at {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank n) (g : G D n) : thetaInt ω ν Φ g = thetaInt ω ν (ω g Φ) 1 := by
  have h : theta ω Φ g = theta ω (ω g Φ) 1 := by
    funext h
    simp only [theta, map_one, Module.End.one_apply]
  simp only [thetaInt, h]

theorem thetaInt_smul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (r : ℂ) (Φ : schwartzA θ V.rank n) (g : G D n) : thetaInt ω ν (r • Φ) g = r * thetaInt ω ν Φ g := by
  have h : theta ω (r • Φ) g = fun h => r * theta ω Φ g h := by
    funext h
    simp only [theta, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact tsum_mul_left
  simp only [thetaInt, h, GlobalTheory.AutomorphicL2Unitary.descend, MeasureTheory.average_eq, integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

theorem phiS_of_mem {θ : InfFam D} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (P : PX m n) (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : phiS θ τ fr c Ψ P = ⟨_, h⟩ := by
  unfold phiS; rw [dif_pos h]

theorem tens_add_smul {θ : InfFam D} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (A B : PX m n) (r : ℂ) :
    tens θ τ fr (fP c (A + r • B)) Ψ = tens θ τ fr (fP c A) Ψ + r • tens θ τ fr (fP c B) Ψ := by
  funext x
  simp only [tens, fP, evX, map_add, MvPolynomial.smul_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH

namespace PositivityTheory.Rg.Sw.Glob

open IInvH in
theorem gIinv_of (hT : TensMem) (hL : ThLin) (hC : LieComm) (hO : DerivOne) : GIinv := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ g a b P
  have hmem := fun Q => hT D n V θ l s τ ε fr hx.hθ (lNZ D ψ θ l hx.hψ hx.hθ hx.hl) hx.hs hx.hfr Ψ hΨ Q
  have hstd : ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ :=
    fun Φ hΦ => ⟨hx.hψ, hx.hχ, hx.hη, hx.hθ, hx.hμ, hx.hω, hx.hH, hx.hl, hx.hs, hx.hν, hΦ⟩

  have h0 : ∀ X, IsUe ε X → ∀ Q, thF ω ν τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q) g = 0 := by
    intro X hX Q
    unfold thF
    rw [thetaInt_at]
    exact hO D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX (ω g (phiS θ τ fr (cLoc l τ) Ψ Q))
      (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q))) (fun x => hC D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ X hX Q g x)
  rw [hOp_eq]
  set A := vfX (cLoc l τ) (zRe ε a b) P
  set B := vfX (cLoc l τ) (zIm ε a b) P
  have hA := phiS_of_mem τ fr (cLoc l τ) Ψ A (hmem A).1
  have hB := phiS_of_mem τ fr (cLoc l τ) Ψ B (hmem B).1
  have hAB := phiS_of_mem τ fr (cLoc l τ) Ψ (A + Complex.I • B) (hmem (A + Complex.I • B)).1
  have hsum : phiS θ τ fr (cLoc l τ) Ψ (A + Complex.I • B) =
      phiS θ τ fr (cLoc l τ) Ψ A + Complex.I • phiS θ τ fr (cLoc l τ) Ψ B := by
    rw [hA, hB, hAB]
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    exact tens_add_smul τ fr (cLoc l τ) Ψ A B Complex.I
  have hfA : (phiS θ τ fr (cLoc l τ) Ψ A).1 ∈ fockA θ V n l s := by rw [hA]; exact (hmem A).2
  have hfB : (Complex.I • phiS θ τ fr (cLoc l τ) Ψ B).1 ∈ fockA θ V n l s := by
    rw [hB, Submodule.coe_smul]; exact (fockA θ V n l s).smul_mem _ (hmem B).2
  unfold thF
  rw [hsum, hL D n V ψ χ θ μ ω H l s ν _ _ (hstd _ hfA) (hstd _ hfB) hx.hr g, thetaInt_smul]
  have e1 := h0 _ (isUe_zRe ε a b) P
  have e2 := h0 _ (isUe_zIm ε a b) P
  unfold thF at e1 e2
  rw [e1, e2]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

section
namespace PositivityTheory.Rg.Sw.Glob

theorem top (hA : AbsThm) (hLF : LocFact) (hAA : AwayAct)
    (hLi : LocInst) (hTA : PositivityTheory.PfSWUS.ThetaAuto) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil)
    (hE : EisStrong) (hC : PositivityTheory.PfSWUS.CoefND)
    (hW : GlobalTheory.Published.WeilThetaConvergence) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) := by
  have hTM := tensMem
  have hTL := thLin_of hW
  exact main hA sFrame sEmb sigOK splitFock hTM (locOpEx_of_locFact hLF) hLi (linSec_of hTL)
    (gSplit_of gIwasawa hAA hLF awayIn schFP hTM lNZ) (gIauto_of hTA hTM) gIk
    (gIinv_of hTM hTL hLC hDO) hId hE gLamBd (gLsing PositivityTheory.Rg.Sw.twoSided' denseTau) hC
    (convRight_of hE) hTL lNZ

end PositivityTheory.Rg.Sw.Glob
end
