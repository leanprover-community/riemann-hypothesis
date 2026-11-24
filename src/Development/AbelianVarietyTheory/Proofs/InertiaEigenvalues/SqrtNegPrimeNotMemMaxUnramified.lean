module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
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
import Formalism.ConjugateSelfDual.Statement

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory

theorem sqrt_neg_l_not_mem_Kur : ∀ (l : ℕ) [Fact l.Prime] (y : Om l), y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l := by
  intro l _ y hy hK
  have hl1 : (1 : ℝ) < (l : ℝ) := Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖y‖ ^ 2 = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hy, norm_neg]
    exact Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hn
    have : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero hl0.ne'
    exact this (by rw [← hn]; norm_num)
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow hK hy0
  rw [hk, ← zpow_natCast, ← zpow_mul, ← zpow_neg_one] at hn
  have h := zpow_right_injective₀ hl0 hl1.ne' hn
  omega

end GlobalTheory
