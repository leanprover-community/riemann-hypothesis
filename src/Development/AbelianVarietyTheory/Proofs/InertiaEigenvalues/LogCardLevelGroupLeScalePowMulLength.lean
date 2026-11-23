module

public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogLevelGroupLeAndLevelLarge
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem log_card_levelGroup_le_scale_pow_mul_length : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C * x ^ C * (Fm.L x i).sc.L := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.log_levelGroup_le_and_level_large eps Fm
  refine ⟨15, max x0 1, fun x hx hx1 i => ?_⟩
  have h := (hx0 x (le_trans (le_max_left _ _) hx) hx1 i).1
  have h1x : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hL : 1 ≤ (Fm.L x i).sc.L := Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hp : (0 : ℝ) ≤ x ^ (15 : ℝ) := Real.rpow_nonneg (by linarith) _
  unfold Formalism.BasicNotions.lam0 at h
  calc Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ x ^ (15 : ℝ) := h
    _ ≤ 15 * x ^ (15 : ℝ) := by linarith
    _ = 15 * x ^ (15 : ℝ) * 1 := by ring
    _ ≤ 15 * x ^ (15 : ℝ) * (Fm.L x i).sc.L := by gcongr

end GlobalTheory.NLink
