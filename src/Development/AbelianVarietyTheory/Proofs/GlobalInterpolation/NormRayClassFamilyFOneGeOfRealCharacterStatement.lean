module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRayClassFamilyFOneGeOfRealCharacter
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.norm_rayClassFamily_F_one_ge_of_real_character : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), χ * χ = 1 → c / 𝓕.B ^ A ≤ ‖𝓕.F χ 1‖ := by
  first | exact @GlobalTheory.Hk.RealChar.norm_F_one_ge | exact GlobalTheory.Hk.RealChar.norm_F_one_ge | (intros; apply GlobalTheory.Hk.RealChar.norm_F_one_ge <;> assumption)
