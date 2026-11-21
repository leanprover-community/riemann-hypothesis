import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.SupportG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolSemiDirect
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolumeUnipotentOne
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VolStabSW
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SupportDatum
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiffGenLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound

namespace Formalism.L2.SG.Closed



theorem NormProd_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.SupportG.NormProd D := by
  intro δ M hA x hx
  exact local_product_formula D.host.F D.host.E (Formalism.MainNotions.BridgeLemma.szf_finrankFE D) D.conjF D.s.atP M
    (fun p => (hA p).1) x hx





end Formalism.L2.SG.Closed
