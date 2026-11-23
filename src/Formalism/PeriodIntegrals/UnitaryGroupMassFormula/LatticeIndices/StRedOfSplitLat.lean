module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PhiBijective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PairMatrixSecondSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport
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

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem coreAll : CoreAll := by
  intro K T _ _ _ O n _ _ θ s J P hs hJ hJu
  exact MassDataIdxCore.coreAll_gen O hs J P hJ hJu

def LatBasisAll {D : D7} (X : HidaSetting D) (p : TypX X) : Prop :=
  ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → ∃ P, LatBasis X p θ P

theorem stRed_of_splitLat {D : D7} (X : HidaSetting D) (p : TypX X) (hS : StSplitLat X p) : StRed X p :=
  stRed_of_core X p (stResZ_holds X p) hS coreAll

theorem stRed_of_emb {D : D7} (X : HidaSetting D) (p : TypX X) (hE : EmbP X p) (hL : LatBasisAll X p) :
    StRed X p := by
  obtain ⟨θ, hθ⟩ := splitTheta_of X p hE
  obtain ⟨P, hP⟩ := hL θ hθ
  exact stRed_of_splitLat X p ⟨θ, hθ, P, hP⟩

end MassDataIdxSteps
