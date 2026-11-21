import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ColsDim
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.LemmaN
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.IdCell
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.GramJoint
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DiamondFree
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMDegEq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMDiscSq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMEulerEq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FinOrdRedOne
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FlagRelevScalar
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RootUnitModP
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitNormRoot
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensInert
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FlagGramNonneg
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiaFixDim
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Closed




theorem rootModP₂ (E : Type) [Field E] [NumberField E] :
    Formalism.L2.SG.IdCell.RootModP E := root_of_unity_mod_p E

theorem GramDetFlag_holds : Formalism.L2.SG.GramJoint.GramDetFlag := Formalism.L2.SG.GramJoint.gramDetFlag

theorem GNonnegAt_holds : Formalism.L2.SG.GramJoint.GNonnegAt := by
  have h : PI.FlagGramNonneg := flag_gram_nonneg
  intro E _ _ _ S τ hτ hsig r T T' hr hT hT' F F'
  obtain ⟨p, hp⟩ : ∃ p, Formalism.UG.HasSignature (S.gram.map τ) p (r + 1) := ⟨(S.sig τ).1, hr ▸ hsig τ⟩
  exact h E S.V S.hT S.herm S.nondeg S.rank S.frame τ hτ p r T T' hp hT hT' F.e F'.e F.z F'.z
    ⟨F.e_indep, F.e_iso, F.z_orth, F.z_norm⟩ ⟨F'.e_indep, F'.e_iso, F'.z_orth, F'.z_norm⟩

theorem DNeZeroAt_holds : Formalism.L2.SG.GramJoint.DNeZeroAt := Formalism.L2.SG.GramJoint.dNeZeroAt_of GNonnegAt_holds






theorem DegEq_holds : Formalism.L2.SG.MassRatio.DegEq := Formalism.L2.SG.MassRatio.cm_degree_eq
theorem DiscSq_holds : Formalism.L2.SG.MassRatio.DiscSq := Formalism.L2.SG.MassRatio.cm_discriminant_square
theorem EulerEq_holds : Formalism.L2.SG.MassRatio.EulerEq := Formalism.L2.SG.MassRatio.mass_ratio_euler_eq
theorem FormsEq_holds : Formalism.L2.SG.MassRatio.FormsEq :=
  Formalism.L2.SG.MassRatio.formsEq_of DegEq_holds DiscSq_holds EulerEq_holds
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem MassRatio_holds : Formalism.L2.SG.MassRatio.MassRatio :=
  Formalism.L2.SG.MassRatio.massRatio_of_siegel FormsEq_holds Formalism.HermitianLattices.Ext.L3.siegelMassRatio

end Formalism.L2.SG.Closed
