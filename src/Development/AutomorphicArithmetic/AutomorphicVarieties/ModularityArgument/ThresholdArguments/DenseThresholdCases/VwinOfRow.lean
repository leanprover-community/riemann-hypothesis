import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLiteratureInputs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WindowBoundOfLiteratureLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideExtra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.SerreTate

namespace UpperTheory.LiteratureTheorems

theorem vwin_of_literature (O : OpenLiteratureStatements) : UpperTheory.Top.VWin := by
  let N := literature_nonexistence O
  apply UpperTheory.V.v_window_of_literal_automorphy_n
  exact {
    loc := { N.loc with }
    aut := { N.aut with gal := N.aut.car }
    coh := N.coh
    cm := {
      gm := grothendieck_deformation_of_literature O
      dr := abelian_de_rham_of_literature O
      dual := GlobalTheory.abelianDualCrystal_of_dual_of_smoothLift
        (dual_abelian_scheme_of_literature O) GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations
      per := GlobalTheory.PeriodFamily.periodComparison_holds
      gmp := GlobalTheory.GaussManinTop.main
      st := UpperTheory.Lit.serreTateGoodReduction
      cm := ellipticMainTheoremCM' O
      hj := hilbertClassFieldJ' O
      dri := siegel_klingen_deligne_ribet_of_literature O
      pz := partial_zeta_functional_equation_of_literature O
      fe := N.fe } }

end UpperTheory.LiteratureTheorems

theorem UpperTheory.One.vwin_of_row (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.Top.VWin :=
  UpperTheory.LiteratureTheorems.vwin_of_literature ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩
