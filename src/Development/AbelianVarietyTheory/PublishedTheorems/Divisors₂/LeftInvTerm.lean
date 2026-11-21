import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelSchwartz.Model

open GlobalTheory.StdUnn

variable {D : D7} {n : ℕ}



theorem leftInv_term {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hχ : IsHeckeChar D χ)
    (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) : LeftInv (P D n ⊓ GF D n) fun γ => (ω γ Φ).1 0 := by
  intro γ hγ g
  obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a, ha⟩ := LeftInvSect.exists_blkA hp
  obtain ⟨u, hu⟩ := LeftInvSect.det_rat hr a ha
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact absE_inclR u
  have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact hχ.2 u
  obtain ⟨m, v, b, e, hm, hv⟩ := LeftInvSect.exists_levi_unip hp a ha
  have e' : ω (γ * g) Φ = ω m (ω v (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
  have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
  show (ω (γ * g) Φ).1 0 = (ω g Φ).1 0
  rw [e', hω.levi m _ hm, h1, h2, z1, hω.unip v b hv, z2]
  simp [halfTr, npow]

theorem term_one {V : HSp D} {ψ χ θ μ} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hχ : IsHeckeChar D χ)
    (hω : IsWeilSch ψ χ θ V μ ω) (Φ : schwartzA θ V.rank n) :
    Eis.term (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) 1 (mk _ 1) = Φ.1 0 := by
  rw [Eis.term_mk (leftInv_term hχ hω Φ)]
  simp



theorem vol_ne (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] :
    autMeasure V ν Set.univ ≠ 0 ∧ autMeasure V ν Set.univ ≠ ⊤ := ⟨NeZero.ne _, measure_ne_top _ _⟩

theorem rhs_eq {V : HSp D} {θ} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank n) : (⨍ q, AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
        Φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν) = thetaInt ω ν Φ 1 := by
  unfold thetaInt theta
  rw [map_one]
  rfl

theorem at_point (H : GlobalTheory.Published.WeilSiegelFormula) {V : HSp D} (hn : 1 ≤ n) (hm : 2 * n < V.rank) {ψ χ θ μ 𝓕}
    (hψ : IsCharAF D.host.F ψ) (hχ : IsHeckeChar D χ) (hr : ResEta D χ V.rank) (hθ : IsInfFam θ)
    (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (Φ : schwartzA θ V.rank n) (g : G D n) :
    Eis.cosetSum (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) g = thetaInt ω ν Φ g := by
  have h := H D n V hn hm ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω ν hν (ω g Φ)
  refine Eq.trans ?_ h
  simp only [Eis.cosetSum, Eis.term, mul_one, map_mul, Module.End.mul_apply]

end GlobalTheory.SiegelSchwartz.Model

end
