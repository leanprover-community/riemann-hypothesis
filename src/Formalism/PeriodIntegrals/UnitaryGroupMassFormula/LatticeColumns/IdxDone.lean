module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LocRed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LevelComponentsSurjective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.PrincipalCongruenceLeLevel
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxProd

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

theorem global_index_eq_prod_local : IdxProdH := idxProdH_of level_components_surjective level_membership_local

def LocRedRest : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X,
      MassDataIdxSteps.StResZ X p ∧ HLatGL X u p ∧ HImU X hb u p

theorem locRedH_of_rest (h : LocRedRest) : LocRedH :=
  locRedH_of fun X hb hK u hT hL p =>
    ⟨(h X hb hK u hT hL p).1, (h X hb hK u hT hL p).2.1, hKerIn_of_levelSubgroupCharacter_of_normalized X hb hK hL u p, (h X hb hK u hT hL p).2.2⟩

theorem idxCountStep_of_rest (h : LocRedRest) : IdxCountStep :=
  idxCountStep_of global_index_eq_prod_local (locRedH_of_rest h)

end PIW.MassDataColumns
