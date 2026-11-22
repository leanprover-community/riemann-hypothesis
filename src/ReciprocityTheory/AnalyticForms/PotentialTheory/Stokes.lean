module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesD

@[expose] public section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

theorem stokes : StokesStatement := st_stokes_of ReciprocityTheory.AnForm.A.parts_thm
theorem byPartsSymm : ByPartsSymmStatement := st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm
theorem byPartsNonpos : ByPartsNonposStatement :=
  st_byPartsNonpos_of ReciprocityTheory.AnForm.A.parts_thm ReciprocityTheory.AnForm.A.gradDensNonneg_thm
theorem massIndep : MassIndepStatement := st_massIndep_of ReciprocityTheory.AnForm.A.parts_thm

end

end ReciprocityTheory.AnForm.M
