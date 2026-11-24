module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviModerateGrowth
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.constant_term_slice_levi_moderate_growth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (g : GA E (a - r)), ∃ (C : ℝ) (M : ℕ), ∀ y, ‖GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y)‖ ≤ C * height y ^ M := by
  first | exact @GlobalTheory.SliceTwo.Growth.norm_slice_le | exact GlobalTheory.SliceTwo.Growth.norm_slice_le | (intros; apply GlobalTheory.SliceTwo.Growth.norm_slice_le <;> assumption)
