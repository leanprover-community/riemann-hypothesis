import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtOfDifferentiableOnFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivCompCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfPiNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartOfHilbertBlumenthal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateExistenceOfPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetDeterminantOfDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermExistenceOfChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetZetaOfDeRham

section
set_option autoImplicit false

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An

namespace GlobalTheory.LatJet.An

theorem jetAnalytic_of_periods :
    GlobalTheory.Published.GaussManinPeriods → GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.HilbertBlumenthal →
      GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
      GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetAnalytic :=
  fun hGM _ hHB _ hDR _ hS =>
    have hC : JetCalc := GlobalTheory.T.jet_calculus_statement
    jetAnalytic_of_steps hC (Chain.jetChain_of_jetCalc hC)
      (GlobalTheory.T.germ_existence_of_chart (GlobalTheory.T.chart_of_hilbert_blumenthal hHB) (holLift_of_jetCalc hC))
      (GlobalTheory.T.coordinate_existence_of_periods hGM hC GlobalTheory.T.diagonal_frame_statement) (GlobalTheory.T.jet_zeta_of_de_rham hDR hC) (GlobalTheory.T.jet_determinant_of_de_rham hDR hC) hS

end GlobalTheory.LatJet.An
end

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_analytic_of_periods : GlobalTheory.Published.GaussManinPeriods → GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.HilbertBlumenthal → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetAnalytic := by
  atlas_forward_decl GlobalTheory.LatJet.An.jetAnalytic_of_periods
