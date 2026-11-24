module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FlagChartsCoverFramedFieldPointsStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRingStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem evLaws_genFr_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c ∧ IntDiagUnit Xo c ∧ GenFrEx Xo c ∧ ∀ h : GenFrEx Xo c, Atlas h := by
  intro E _ _ _ H Dw l Xo c
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨-, -, hwd, hwt, hint, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hB E H Dw l Xo c
  have hbc : FrBC Xo c := fun S T _ _ _ _ φ y =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y
  exact ⟨⟨hwd, GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c, hwt, hbc⟩, hint, genFrEx_of hT,
    GlobalTheory.T.flagCharts_cover_framed_fieldPoints hT E H Dw l Xo c hbc⟩

end GlobalTheory.Reg
