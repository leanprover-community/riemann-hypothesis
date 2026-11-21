import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.AreaCmLNe
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.MkLeOfDenseRange
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Inert57

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

abbrev L7 : PeriodPair := cmL 1 1 7 (by norm_num) (by norm_num) 1 one_ne_zero




abbrev h7 : Matrix (Fin 1) (Fin 1) ℂ := (((area L7 : ℝ) : ℂ)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℂ)












end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
