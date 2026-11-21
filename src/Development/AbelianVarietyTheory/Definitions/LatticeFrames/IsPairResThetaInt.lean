import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FirstTermWeak
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ConclusionZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilize
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpaces

noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.OrthSumSp (posSp hypSp hypSumDec posSp_sigOK hypSp_sigOK)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSW.WeakModel

variable {D : D7}

def IsPairRes {S T' : HSp D} (ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (m : Measure (GA D T'))
    (Ψ : WO S T' → ℂ) (B : GA D S → ℂ) : Prop :=
  ∃ (E : GA D T' → ℂ → ℂ) (c : ℂ → ℂ) (s₀ : ℂ) (σ : ℝ), (∀ s : ℂ, σ < s.re → ∀ g, ThetaPairConv ω' m Ψ (fun h => E h s) g) ∧
    ∀ g, ResidueAt (fun s => c s * thetaPair ω' m Ψ (fun h => E h s) g) s₀ (B g)

theorem residueAt_zero (s₀ : ℂ) : ResidueAt (fun _ : ℂ => (0 : ℂ)) s₀ 0 :=
  ⟨_, isExtAt_const 0 s₀, laurentConst_of_tendsto (by simp)⟩

theorem IsPairRes.eq_zero {S T' : HSp D} {ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} {m : Measure (GA D T')}
    {Ψ : WO S T' → ℂ} {B : GA D S → ℂ} (h : IsPairRes ω' m Ψ B) {g : GA D S} (h0 : ∀ x, thetaKO ω' g x Ψ = 0) : B g = 0 := by
  obtain ⟨E, c, s₀, σ, -, hr⟩ := h
  have e : (fun s => c s * thetaPair ω' m Ψ (fun h => E h s) g) = fun _ => 0 := funext fun s => by
    have : (descend (GQ T') fun h => thetaKO ω' g h Ψ * E h s) = fun _ => 0 := funext fun q => by simp [AutomorphicL2Unitary.descend, h0]
    simp [thetaPair, this]
  have := hr g
  rw [e] at this
  exact CoeffAt.unique this (residueAt_zero s₀)



def Met (A T T' : HSp D) : Prop :=
  ∃ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D T →* Module.End ℂ (WO (dblSp A) T → ℂ))
    (ω' : GA D (dblSp A) × GA D T' →* Module.End ℂ (WO (dblSp A) T' → ℂ)) (a : GL (Fin A.rank) (AE D))
    (μ₀ : Measure (WO A T)) (𝓕₀ : Set (WO A T)) (m : Measure (GA D T')) (φ : WO (dblSp A) T → ℂ),
    IsWeilDatumO ψ (dblSp A) T 1 χ ω ∧ IsWeilDatumO ψ (dblSp A) T' 1 χ ω' ∧ m.IsHaarMeasure ∧ IsCovolOne (ratL T A) μ₀ 𝓕₀ ∧
    swSec A T ω μ₀ 𝓕₀ φ 1 = 1 ∧
    ∃ (Ψ : WO (dblSp A) T' → ℂ) (B : GA D (dblSp A) → ℂ), IsThetaFunO ψ (dblSp A) T' Ψ ∧ IsKFinVec ω' (Khat A a) Ψ ∧
      IsPairRes ω' m Ψ B ∧ EisCoeffAt A (flat A a (swSec A T ω μ₀ 𝓕₀ φ) (sZero A T)) (sZero A T) (-1) B


theorem isAniso_pos (D : D7) (n : ℕ) : IsAniso (posSp D n) :=
  GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite _ (posSp_sigOK D n) fun _ => .inl rfl



end GlobalTheory.RegSW.WeakModel

end
