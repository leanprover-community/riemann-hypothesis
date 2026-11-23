module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.TauDefs
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.AddLeMulPowOfSqLeOfLeMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.CoreInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.FvecCastSucc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.HermitianXiOrthogonal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.IsoRightInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.NsqMulVecLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.SecondOrderNormBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnipotentFixesFrameVector
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnitriangularInverseBoundOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.PolynomialProperness

theorem polyProper_of_mx (hMX : MXFacts) : Formalism.FourierDecayAlt.C2.PolyProper := by
  have hT := tauMem_of hMX TauN.neFacts
  have hU := Formalism.FourierDecayAlt.P.unipotent_map_frame
  exact polyProper_of_steps gvGroup normInv gnFacts fmulBound zhatMove
    (frameS_of hU gvGroup) (frameSg_of hU hT gvGroup) (frameSg'_of hU hT gvGroup) (unitriangular_inverse_bound second_order_norm_bound)
    (coreInst_of isoCore hpkInvol gnFacts frameInd)

end PI.PolynomialProperness
