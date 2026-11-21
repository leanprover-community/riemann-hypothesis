import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.IntegralModelsLocalData
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.LogDiscriminantLeSquareSizeFamily

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.MainNotions

section WeightAlgebra

variable {D : D7}


end WeightAlgebra

section P08F

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : Formalism.MainNotions.DIV.Align.PrinLevF Fm) (BF : WeightFamilies.ProvF Fm)
  (PF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WeightAlgebra.Prov (Fm.D x i) (BF x hx i) (PF x hx i))

end P08F

section BoundaryLocalData

variable (D : D7) (X : ModuliIntegralCharts.Prov D)

end BoundaryLocalData

section IntegralModelsLocalData

variable (D : D7) (XD : DivX D) (X : IntegralModelsLocalData.Prov D XD)

end IntegralModelsLocalData

section WeightThresholdDefs

variable (D : D7) (V : DivX D) (P : Formalism.MainNotions.DIV.Align.PrinLev V) (X : IntegralModelsLocalData.Prov D V)

end WeightThresholdDefs

section WeightThresholdDefs

variable (D : D7) (V : DivX D) (P : Formalism.MainNotions.DIV.Align.PrinLev V) (X : IntegralModelsLocalData.Prov D V)

end WeightThresholdDefs

section WeightThresholdDefs

variable (D : D7) (V : DivX D) (P : Formalism.MainNotions.DIV.Align.PrinLev V) (X : IntegralModelsLocalData.Prov D V)

end WeightThresholdDefs

section Fam66x

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : Formalism.MainNotions.DIV.Align.PrinLevF Fm) (XF : IntegralModelsLocalData.ProvF Fm)

end Fam66x

section Base

variable {D : D7}

noncomputable def zText (L : SizeData₂ D) : ℝ := (D.R.f : ℝ) * (D.R.r : ℝ) + L.sc.L + logdE D

end Base

end Formalism.MainNotions.DIV
