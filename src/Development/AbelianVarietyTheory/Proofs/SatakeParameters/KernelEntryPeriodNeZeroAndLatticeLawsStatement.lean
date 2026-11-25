module

public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelEntry_period_ne_zero_and_lattice_laws : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), t.δ ≠ 0 ∧ t.B.LatAll ∧ t.B.VecP t.χ ∧ t.B.EqP t.χ := by
  first | exact @GlobalTheory.TieBase.base_data
