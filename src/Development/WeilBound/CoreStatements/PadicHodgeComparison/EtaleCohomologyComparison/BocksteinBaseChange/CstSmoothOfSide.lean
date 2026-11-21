import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CstSmooth
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmooth2

section
noncomputable section

namespace CrystallineSemistableComparison.Out

theorem cstSmooth_of_side (h : EtSideS) : CstSmooth := CrystallineSemistableComparison.cstSmooth_of_side h

end CrystallineSemistableComparison.Out
end
end

section
namespace CrystallineSemistableComparison.Close

theorem cstSmooth_of_side (h : CrystallineSemistableComparison.Out.EtSideS) : CrystallineSemistableComparison.Out.CstSmooth := CrystallineSemistableComparison.Out.cstSmooth_of_side h

end CrystallineSemistableComparison.Close
end
