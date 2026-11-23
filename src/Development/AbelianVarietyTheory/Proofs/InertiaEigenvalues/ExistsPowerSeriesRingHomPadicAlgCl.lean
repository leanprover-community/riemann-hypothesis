module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.HV

namespace GlobalTheory

namespace PowerSeriesEvalAlgCl

theorem isIntegral_iff_norm_le_one {l : ℕ} [Fact l.Prime] (y : PadicAlgCl l) :
    IsIntegral ℤ_[l] y ↔ ‖y‖ ≤ 1 := by
  have hm : (minpoly ℚ_[l] y).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
  have key : ‖y‖ ≤ 1 ↔ ∀ n, ‖(minpoly ℚ_[l] y).coeff n‖ ≤ 1 := spectralValue_le_one_iff hm
  rw [key]
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · obtain ⟨q, hq, -, hq'⟩ := lifts_and_degree_eq_and_monic
      ((lifts_iff_coeff_lifts (f := algebraMap ℤ_[l] ℚ_[l]) _).2 fun n => ⟨⟨_, h n⟩, rfl⟩) hm
    refine ⟨q, hq', ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq]
    exact minpoly.aeval ℚ_[l] y

theorem exists_coef_ge_finset {l : ℕ} [Fact l.Prime] (c : Coef l) (s : Finset (PadicAlgCl l))
    (hs : ∀ y ∈ s, IsIntegral ℤ_[l] y) : ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ y ∈ s, y ∈ c'.O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c₁, h₁, h₂⟩ := ih fun y hy => hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨c₂, h₃, h₄⟩ := (coefSup l).2.2.1 c₁ a (hs a (Finset.mem_insert_self _ _))
    refine ⟨c₂, h₁.trans h₃, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact h₄
    · exact h₃ (h₂ y hy)

end PowerSeriesEvalAlgCl

end GlobalTheory
