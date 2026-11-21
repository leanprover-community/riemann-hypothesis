import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.SimplePoleModel

open GlobalTheory.Eis

theorem resEta_one_two_mul (D : D7) (k : ℕ) : ResEta D 1 (2 * k) :=
  ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η h x => by
    rw [pow_mul, pow_two, GlobalTheory.VolHeckeCompare.IsEta_mul_self h x, one_pow]; rfl⟩

open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem hypotheses_hold (D : D7) (V : HSp D) (k : ℕ) (s₁ : ℂ) :
    ∃ (a : GL (Fin V.rank) (AE D)) (φ : GA D (dblSp V) → ℂ), IsMaj V a ∧
      HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) ∧ IsHeckeChar D 1 ∧ ResEta D 1 (2 * k) ∧
      φ ∈ degPS V a 1 s₁ ∧ ∀ g, φ g ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_isMaj V
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  refine ⟨a, sph V a s₁, ha, hI, ⟨continuous_const, fun _ => rfl⟩, resEta_one_two_mul D k, sph_mem hI s₁, fun g => ?_⟩
  simp only [sph, npow_eq_exp (hgtH_pos _)]
  exact Complex.exp_ne_zero _





end GlobalTheory.Eis.SimplePoleModel

end
