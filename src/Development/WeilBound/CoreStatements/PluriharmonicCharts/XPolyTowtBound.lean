module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace PositivityTheory.Xgp.poly_towt_bound

theorem gapX_hom {Ψ : Type} {N : ℕ} (p : Ψ × Fin N) : (gapX p).IsHomogeneous 1 := by
  unfold gapX
  refine (isHomogeneous_X ℝ p).sub ?_
  split_ifs
  · exact isHomogeneous_X ℝ _
  · exact isHomogeneous_zero _ _ _

end PositivityTheory.Xgp.poly_towt_bound

