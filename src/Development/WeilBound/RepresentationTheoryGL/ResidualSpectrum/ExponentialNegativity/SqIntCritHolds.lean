import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOf
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

section
namespace PositivityTheory.Rg.Rs

theorem sqIntCrit_of_finTr (h : FinTr) : SqIntCrit := sqIntCrit_of initBnd_holds h boxvol_holds

end PositivityTheory.Rg.Rs
end

section
namespace PositivityTheory.Rg.Rs

theorem sqIntCrit_holds : SqIntCrit := sqIntCrit_of_finTr finTr_holds

end PositivityTheory.Rg.Rs
end
