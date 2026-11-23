module

public import Formalism.HermitianCurvature.ArchimedeanUniformConstantsCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothAtBuiltPlace
public import Formalism.HermitianCurvature.JcRadialModuleFormOfParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory

theorem carrierNeedsFromD :
    Formalism.FourierDecayAlt.P5.ThmPActualCpt ∧ Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 ∧ Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt :=
  ⟨Formalism.FourierDecayAlt.P.CutSE.actual_compact_theorem, Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.model_place_built_holds,
    Formalism.FourierDecayAlt.Final.pb_builtBounds2Cpt⟩

end GlobalTheory
