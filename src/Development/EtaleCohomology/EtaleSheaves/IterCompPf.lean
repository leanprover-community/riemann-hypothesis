module

public import Development.EtaleCohomology.EtaleSheaves.ChowGraphCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterCompPf

theorem isLine_iso_comp {L L' S : Scheme.{0}} (e : L' ⟶ L) [IsIso e] {l : L ⟶ S} (h : IsLine l) :
    IsLine (e ≫ l) :=
  h.bc (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ l) l (𝟙 S))

theorem iterLine_iso_comp {T S Y : Scheme.{0}} {k : T ⟶ S} (hk : IterLine k) (e : Y ⟶ T) [IsIso e] :
    IterLine (e ≫ k) := by
  cases hk with
  | iso k' hk' => exact IterLine.iso _ inferInstance
  | comp l k' hl hk' =>
    rw [← Category.assoc]
    exact IterLine.comp _ _ (isLine_iso_comp e hl) hk'

theorem IterComp_of : LateralTheory.E.ChowGraphCut.IterComp := by
  intro P T S l k hl hk
  induction hl with
  | iso e he => exact iterLine_iso_comp hk e
  | comp l₁ k₁ hl₁ _ ih =>
    rw [Category.assoc]
    exact IterLine.comp _ _ hl₁ ih

end LateralTheory.E.IterCompPf

end
