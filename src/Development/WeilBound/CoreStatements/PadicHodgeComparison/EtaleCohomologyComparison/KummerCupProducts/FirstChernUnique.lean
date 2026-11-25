module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForE
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleChernClassEqKummerClass
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.Inputs

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.E

theorem etMap (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : EtMap l K :=
  Main.etale_comparison_map etIn l (CrystallineSemistableComparison.R.forE l) K

end CrystallineSemistableComparison.E
