import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAutomorphicOfConvergence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralTranslateSmul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.QuadraticOperatorPureTensor

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GCommH

variable {D : D7} {n : ℕ}

theorem gComm {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle}
    (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)}
    {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (Φ Φh : schwartzA θ V.rank n) (h : GA D V) (hΦh : ∀ x, Φh.1 x = Φ.1 (mt V h ⬝ x)) (g : G D n) (x : Mx D V.rank n) :
    (ω g Φh).1 x = (ω g Φ).1 (mt V h ⬝ x) := by
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hs0, hsk, _, _, hκ, hW, hT⟩ := GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hs0 θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have hlaw := fun F (hF : IsThetaFunO ψ₀ (dblSp A) V F) => (GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions D ψ₀ A V χ⁻¹ omh hW μ 𝓕 hμ F hF).1
  have hf1 : IsThetaFunO ψ₀ (dblSp A) V (omh (1, h⁻¹) f) := hW.om_pres _ f hf
  have hΦh' : Φh.1 = sch ψ₀ A V μ 𝓕 (omh (1, h⁻¹) f) := by
    funext y
    rw [hΦh, hlaw f hf h⁻¹ y, inv_inv, hfΦ]
    rfl
  have key : ∀ g0 : GA D (dblSp A), (ω (κ g0) Φh).1 x = (ω (κ g0) Φ).1 (mt V h ⬝ x) := by
    intro g0
    have hc : omh (g0, 1) (omh (1, h⁻¹) f) = omh (1, h⁻¹) (omh (g0, 1) f) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
        one_mul, mul_one, one_mul, mul_one]
    have hg1 : IsThetaFunO ψ₀ (dblSp A) V (omh (g0, 1) f) := hW.om_pres _ f hf
    calc (ω (κ g0) Φh).1 x = sch ψ₀ A V μ 𝓕 (omh (g0, 1) (omh (1, h⁻¹) f)) x := congrFun (hT g0 _ hf1 Φh hΦh') x
      _ = sch ψ₀ A V μ 𝓕 (omh (1, h⁻¹) (omh (g0, 1) f)) x := by rw [hc]
      _ = sch ψ₀ A V μ 𝓕 (omh (g0, 1) f) (mt V h⁻¹⁻¹ ⬝ x) := hlaw _ hg1 h⁻¹ x
      _ = sch ψ₀ A V μ 𝓕 (omh (g0, 1) f) (mt V h ⬝ x) := by rw [inv_inv]
      _ = (ω (κ g0) Φ).1 (mt V h ⬝ x) := (congrFun (hT g0 f hf Φ hfΦ.symm) _).symm
  have e : κ (κ.symm g) = g := κ.apply_symm_apply g
  have k := key (κ.symm g)
  rw [e] at k
  exact k

end PositivityTheory.Rg.Sw.Glob.GCommH
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

def OpCLM : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ y : GR n,
    ∃ L : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℝ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ,
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ),
        (ω (ι y) ⟨tens θ τ fr S Ψ, hΨ.2 S ⟨S, rfl⟩⟩).1 = tens θ τ fr (L S) Ψ

def AwayFact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ g : G D n,
    ∃ (x : G D n) (y : GR n), g = x * ι y ∧ ∀ Ψ, AwayCls θ τ fr Ψ → ∃ Ψ', AwayCls θ τ fr Ψ' ∧
      ∀ (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ) (hS : tens θ τ fr S Ψ ∈ schwartzA θ V.rank n),
        (ω x ⟨tens θ τ fr S Ψ, hS⟩).1 = tens θ τ fr S Ψ'

def SchDeriv : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n),
    ∃ (S : ℝ → SchwartzMap (Fin m → Fin n → ℂ) ℂ) (S' : SchwartzMap (Fin m → Fin n → ℂ) ℂ),
      (∀ t y, S t y = fP c P ((NormedSpace.exp ((t : ℂ) • X) : Matrix (Fin m) (Fin m) ℂ) * (Matrix.of y : Matrix (Fin m) (Fin n) ℂ))) ∧
      (∀ y, S' y = fP c (vfX c X P) y) ∧
        Filter.Tendsto (fun t : ℝ => t⁻¹ • (S t - S 0)) (nhdsWithin 0 {0}ᶜ) (nhds S')

end PositivityTheory.Rg.Sw.Glob
end
end
