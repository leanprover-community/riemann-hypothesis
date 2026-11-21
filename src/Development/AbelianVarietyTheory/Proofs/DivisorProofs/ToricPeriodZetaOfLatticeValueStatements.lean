import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions

section
theorem GlobalTheory.JoinFun.joinOut_of_lat : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatVal.LatIntRam → GlobalTheory.LatVal.LatIntUnr → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  intro hEM hHCF hSKDR hHT hRam hUnr hLatAlg hLatConj
  have hZD := GlobalTheory.ZetaDenom.zetaDenominators hSKDR
  have hField := GlobalTheory.SqTop.fieldDat
  have hAbs := GlobalTheory.Published.HeckeTateFunctionalEquation.abs hHT
  have hLNe := GlobalTheory.SqTop.lNe_of_functionalEquation hAbs GlobalTheory.HeckeStrip.completedLBoundedInStrips hField
  exact ⟨GlobalTheory.ToricDenomRow.toricDenominator hZD hRam hUnr,
    GlobalTheory.TransportProof.transport_of hHCF hLatAlg hLatConj,
    GlobalTheory.TwistedTransportProof.main (GlobalTheory.LatVal.periodEx_of_mainTheorem hEM) hLatAlg hLatConj, hZD,
    GlobalTheory.SqTop.refl_of_functionalEquation hHT hField hLNe⟩
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPeriodZeta_of_latticeValue_statements : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatVal.LatIntRam → GlobalTheory.LatVal.LatIntUnr → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  atlas_forward_decl GlobalTheory.JoinFun.joinOut_of_lat
