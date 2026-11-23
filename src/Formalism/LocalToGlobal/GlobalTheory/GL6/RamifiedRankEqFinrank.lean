module

public import Formalism.LocalRingCardinality.DataKernels
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions

section Model

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc}


open Classical in
structure FreeRankModel (A : ColumnsAtT R C) where
  H : Type
  [grp : Group H]
  [finH : Fintype H]
  X : Type
  [finX : Fintype X]
  [act : MulAction (A.vT → H) X]
  e : ∀ v, (A.Fv v)ˣ ≃* H
  E : A.Mu0 ≃ₗ[ℂ] (X → ℂ)
  free : ∀ (g : A.vT → H) (x : X), g • x = x → g = 1
  intertw : ∀ v (a : (A.Fv v)ˣ) (φ : A.Mu0) (h : A.rhoT v a (φ : C.cls 0 → C.Y 0 → ℂ) ∈ A.Mu0) (x : X),
    E ⟨A.rhoT v a φ, h⟩ x = E φ ((Pi.mulSingle v (e v a) : A.vT → H) • x)

attribute [instance] FreeRankModel.grp FreeRankModel.finH FreeRankModel.finX FreeRankModel.act

variable (A : ColumnsAtT R C)




end Model

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
