import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ConstOneMemCuspFormsOfAnisotropic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters

noncomputable section

open scoped ComplexConjugate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.ContModel

theorem hypotheses_inhabited (n b : ℕ) (s₁ : ℂ) :
    ∃ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (μ : (AE D)ˣ →* Circle) (φ : GA D (dblSp V) → ℂ),
      V.rank = n ∧ IsMaj V a ∧ HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) ∧ IsHeckeChar D μ ∧ ResEta D μ (2 * b) ∧
        φ ∈ degPS V a μ s₁ ∧ ∀ g, φ g ≠ 0 := by
  obtain ⟨D⟩ := GlobalTheory.Mem.nonempty_record
  obtain ⟨V, a, -, -, -, -, h1, h2, -⟩ := DblModel.hypotheses_inhabited D n 0
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a h2
  refine ⟨D, V, a, 1, sph V a s₁, h1, h2, hI, ⟨continuous_const, fun _ => rfl⟩, DblModel.resEta_one D b,
    sph_mem hI s₁, fun g => ?_⟩
  rw [sph, npow_eq_exp (hgtH_pos _)]
  exact Complex.exp_ne_zero _

variable {D : D7} {V : HSp D} {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ}

theorem isEisFamily_flat (ha : IsMaj V a) (hμ : IsHeckeChar D μ) (hφ : φ ∈ degPS V a μ s₁) :
    IsEisFamily V (flat V a φ s₁) :=
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  (sphConv D V a hI).isEisFamily_flat hI hφ hμ






end GlobalTheory.Eis.ContModel

end
