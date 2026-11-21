import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalMemOfLeSup

section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

theorem cofin_monic_on_killed : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ)
    (J : Set (Module.End ℂ (Sm E n))), Cofin J → ∀ z ∈ Zalg E n, ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ φ : Sm E n, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 :=
  fun E _ _ _ n J hJ z hz => GlobalTheory.CompanionTheory.Affgl.minpoly_on_killed E n J hJ z hz

end GlobalTheory.CompanionTheory.CTFin
end

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofinite_center_monic_annihilator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (J : Set (Module.End ℂ (Sm E n))), Cofin J → ∀ z ∈ Zalg E n, ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E n, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed
