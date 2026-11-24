module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
private theorem nonempty_irreducibleComponents_of_point {X : Type*} [TopologicalSpace X] (x : X) :
    Nonempty (irreducibleComponents X) :=
  ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Reg.evLaws_genFr_nonempty_comp : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Reg.EvLaws Xo c ∧ _root_.Formalism.L2.Pj.IntDiagUnit Xo c ∧ _root_.Formalism.L2.Pj.GenFrEx Xo c ∧
      (1 ≤ Dw.p + Dw.q → Nonempty (_root_.Formalism.L2.Pj.Comp Xo c)) := by
  intro E _ _ _ H Dw l Xo c
  have hsec : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := _root_.GlobalTheory.allSixLaws.1.secBaseChange
  have htw : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := _root_.GlobalTheory.allSixLaws.2.1.secTwist
  obtain ⟨-, -, hwd, hwt, hdiag, -, -⟩ :=
    _root_.GlobalTheory.Frames.algebraic_laws hsec E H Dw l Xo c
  refine ⟨⟨hwd, _root_.GlobalTheory.Frames.allTest_of_secBaseChange hsec E H Dw l Xo c, hwt, ?_⟩, hdiag,
    _root_.Formalism.L2.Pj.genFrEx_of htw, ?_⟩
  · intro S T _ _ _ _ φ y
    exact _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap hsec E H Dw l Xo c S T φ y
  · intro hpq
    obtain ⟨x⟩ := (_root_.GlobalTheory.PeriodExists.typeFn_period_exist E H Dw).2.2
      _root_.GlobalTheory.closing_of_abelianSchemeLaws hpq l Xo c
    unfold _root_.Formalism.L2.Pj.Comp
    exact nonempty_irreducibleComponents_of_point x

end GlobalTheory.Reg
