import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow

theorem UpperTheory.FinalTheorems.everyCharacter_of_row (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.EveryCharacter :=
  let O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements := ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin O (UpperTheory.LiteratureTheorems.vwin_of_literature O)
