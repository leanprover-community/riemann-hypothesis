module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubicExponentialFactor
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglChordFactor
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglTriFactor
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhiCubeOfFactor
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FormalGroupLawFirstHalfHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

theorem lemma_three_one_third_holds : LemmaThreeOneThird := by
  intro p hp g hOk hI
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact formal_group_tri_factor p g.W g.wq g.ex h1 h2 h3 h4 h6 hΔ hW he0 hel hI

theorem lemma_three_one_second_holds : UnitTraceSumSecondBound := by
  intro p hp g hOk hI
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact fglChordFactor p g.W g.wq g.ex h1 h2 h3 h4 h6 hΔ hW he0 hel hI

theorem cube3OfDet_holds : Cube3OfDet := by
  intro p hp g hOk hE hQ hn
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact thetaCube_triple_relation p g.W g.wq g.l g.ex (ePhi1 g.lam g.abelian₂ g.C g.wq) _ h1 h2 h3 h4 h6 hW he0 hel hE hQ hn

theorem cube_second_of_determinant_formula (D : Formalism.BasicNotions.D7) (hQ : PAdicFrobeniusStickelberger D) : cube3 D :=
  cube_second_identity_of_determinant lemma_three_one_third_holds cube3OfDet_holds D hQ (addInt_holds D)

theorem cube_first_of_addition_holds : CubeIdentityFromAdditionFormula := by
  intro p hp g hOk hE hId hn
  obtain ⟨_, hW, he0, hel⟩ := hOk
  exact phiCubeOfFactor p _ g.ex _ _ he0 hel hE hId hn

theorem cube_first_of_addition_formula (D : Formalism.BasicNotions.D7) (hQ : PAdicSigmaAdditionFormula D) : cube2 D :=
  addition_identity_of_sigma_formula lemma_three_one_second_holds cube_first_of_addition_holds D hQ (ePhiOne_holds D) (addInt_holds D)

theorem theorem_of_cube_of_addition_formulas (D : Formalism.BasicNotions.D7) (hQ : PAdicSigmaAdditionFormula D) (hQd : PAdicFrobeniusStickelberger D) : cube D :=
  cube_of cube_of_two_identities_holds D (cube_first_of_addition_formula D hQ) (cube_second_of_determinant_formula D hQd)

end Formalism.MainNotions.Ext.CutA
