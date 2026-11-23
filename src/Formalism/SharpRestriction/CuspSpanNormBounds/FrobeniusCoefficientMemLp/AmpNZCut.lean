module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpUnif
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpBig
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

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.LemmaJ

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.S.ThB

def AmpNZCoef : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl → ∀ (D : D7) (large₂ : SizeData₂ D),
    Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ τ w w', HypTT D w w' → ∀ θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W)
      (A : LocS W) (hA : GoodS D (lamD D τ) A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
      ∃ f : MatKR D.R.k D.R.rS →
          ((toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').Wq →L[ℂ] (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT').Wp),
        OrbEq D hW hA hT hT' f ∧ jNorm2 (toBessel D τ w w' θ W (lamD D τ) A hW hA hT hT') f μsec ≠ 0

theorem ampNZ_of (h : AmpNZCoef) : AmpNZ := by
  intro Cg cb Cu cT CT C0
  obtain ⟨A1, B1, h'⟩ := h Cg cb Cu cT CT C0
  refine ⟨A1, B1, fun C' Cl hC' hCl D large₂ hH τ w w' hTT θ W hW A hA hT hT' μsec hsec => ?_⟩
  obtain ⟨f, hOrb, hne⟩ := h' C' Cl hC' hCl D large₂ hH τ w w' hTT θ W hW A hA hT hT' μsec hsec
  rw [← big_cell_eq D τ w w' θ W hW (lamD D τ) A hA hT hT' f hOrb μsec hsec]
  exact hne

end Formalism.MainNotions.S.Pv.LemmaJ
