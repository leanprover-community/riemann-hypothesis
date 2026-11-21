import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpMultiplicityRestrictFiniteExt

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeJumpMultiplicity_restrict_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ a = multV (P.PD K) ρ (τ.comp (IntermediateField.inclusion h)) a := by
  first | exact @GlobalTheory.JumpRestrict.multV_restrict | exact GlobalTheory.JumpRestrict.multV_restrict | (intros; apply GlobalTheory.JumpRestrict.multV_restrict <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.ResFinite

theorem adm12_elementDenominator : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm12 D := by
  intro D l _ K K' hKK hle LL T hc
  have hT := D.locT l
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) hT K' LL T.V T.ρ hc).1
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (D.loc l) (D.locA l) hT K' K LL hKK T.V T.ρ).1 hc
  · intro τ a
    exact GlobalTheory.T.hodgeJumpMultiplicity_restrict_finite_ext l (D.loc l) (D.locA l) hT K' K LL hKK T.V T.ρ hdr τ a

end GlobalTheory.Per.ResFinite
end
