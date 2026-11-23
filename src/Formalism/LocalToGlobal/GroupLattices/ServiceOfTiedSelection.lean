module

public import Formalism.SharpRestriction.ParamsHeightRankConstant
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

@[expose] public section

noncomputable section

namespace Formalism.L2.G.ServT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2

theorem closed_imp_class {𝒞 : FamClass} {P Q : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (hP : Closed 𝒞 P)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), 𝒞 Fm → P Fm CH → Q Fm CH) : Closed 𝒞 Q := by
  unfold Closed at hP ⊢
  obtain ⟨ε1, hε1, hP⟩ := hP
  refine ⟨ε1, hε1, fun eps he he1 => ?_⟩
  obtain ⟨K, hK⟩ := hP eps he he1
  exact ⟨K, fun Fm CH hc hL => h Fm CH hc (hK Fm CH hc hL)⟩

end Formalism.L2.G.ServT

end
