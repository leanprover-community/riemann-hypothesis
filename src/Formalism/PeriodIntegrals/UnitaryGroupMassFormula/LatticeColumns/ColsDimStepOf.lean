module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Development
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.PoincareInHH

def NeatKuStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter),
    Formalism.L2.SG.ColsDim.StabTriv (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK)

def ClassFinStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter),
    Finite (Formalism.L2.SG.ColsDim.Classes (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK))

def ClassCountStep' : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    AdBridgeGF X.B.I → X.MeasTie hb → X.LevelSubgroupNormalized →
    Formalism.L2.SG.ColsDim.StabTriv (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK) →
    Finite (Formalism.L2.SG.ColsDim.Classes (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK)) →
    (Nat.card (Formalism.L2.SG.ColsDim.Classes (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK)) : ℝ) =
      covol (X.measW u).μH /
        ((X.muH u Set.univ).toReal * ((X.measW u).μHf (Subtype.val ⁻¹' K2u X hb u)).toReal)

theorem colsDimStep_of' (hGF : ∀ I : Formalism.MainNotions.S.AutInst, AdBridgeGF I) (hN : NeatKuStep) (hF : ClassFinStep)
    (hC : ClassCountStep') : ColsDimStep := by
  intro D X hb hK u hMT hL
  have hS := hN X u hK
  have hFin := hF X u hK
  have hcount := hC X hb hK u (hGF _) hMT hL hS hFin
  have hdim := (Formalism.L2.SG.ColsDim.columns_dimension _ _ _ ℂ _ (PoincareSetting.iotaI X u) (PoincareSetting.iotaF X u)
    (PoincareSetting.Ku X u hK) (PoincareSetting.Ku X u hK) (PoincareSetting.psiK X u hK) (PoincareSetting.piRep X u) le_rfl hS hFin
    inferInstance).2
  have hdim' : Module.finrank ℂ (PoincareSetting.Cu X u hK) = Module.finrank ℂ (X.Vpi u) *
      Nat.card (Formalism.L2.SG.ColsDim.Classes (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK)) := hdim
  rw [hdim', Nat.cast_mul, hcount]

end PIW.MassDataColumns
