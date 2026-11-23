module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem secM_mul_mem (y : (Σ k, ι k) → Ω) {d e : K → ℕ} {s t : Ω} (hs : s ∈ secM y d)
    (ht : t ∈ secM y e) : s * t ∈ secM y (d + e) := by
  have hgen : ∀ g : MRing ι, IsMultiHomog g d → aeval y g * t ∈ secM y (d + e) := by
    intro g hg
    change t ∈ Submodule.span ℤ _ at ht
    change _ ∈ Submodule.span ℤ _
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, ProjLine.mhMul hg hh, by rw [map_mul]⟩
    | zero => simp
    | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
    | smul n x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  change s ∈ Submodule.span ℤ _ at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hgen g hg
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul n x _ hx => rw [smul_mul_assoc]; exact zsmul_mem hx n

end GroundTheory.Heights₂.Heights.HilbertSamuel
