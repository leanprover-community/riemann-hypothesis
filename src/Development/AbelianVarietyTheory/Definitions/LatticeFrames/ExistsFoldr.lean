module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
namespace GlobalTheory.SeeSaw.GModel
variable {D : D7} {c : Comm D} {v : VCom c}

section Rel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Rel

section Mu
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Mu


open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct in
variable {D : _root_.Formalism.BasicNotions.D7} {c : _root_.GlobalTheory.SeeSaw.Comm D} {v : _root_.GlobalTheory.SeeSaw.VCom c} in
theorem _root_.GlobalTheory.SeeSaw.GModel.phi_sb (G : _root_.GlobalTheory.SeeSaw.GLoc v) :
    (∀ j a H, (G.S.T (Fin D.R.t)).Phi j a H ∈
      _root_.GlobalTheory.SplitWeil.SB _) ∧
    (G.S.T (Fin D.R.t)).PhiTop ∈ _root_.GlobalTheory.SplitWeil.SB _ := by
  have hreg : (G.S.T (Fin D.R.t)).Regular := by
    unfold _root_.GlobalTheory.SymChain.SymData.T _root_.GlobalTheory.StepData.typeChain
    exact _root_.GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _
  obtain ⟨hstep, htop, -⟩ := hreg
  exact ⟨hstep, htop⟩

end GlobalTheory.SeeSaw.GModel
end
