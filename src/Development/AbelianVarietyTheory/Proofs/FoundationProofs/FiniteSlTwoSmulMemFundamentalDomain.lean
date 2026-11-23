module

public import Mathlib.NumberTheory.Modular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem finite_smul_mem_fd : ∀ τ : ℍ, {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd}.Finite := by
  intro τ
  have hP : {p : Fin 2 → ℤ | ¬ (2 * τ.im < Complex.normSq ((p 0 : ℂ) * τ + p 1))}.Finite :=
    Filter.eventually_cofinite.1
      ((ModularGroup.tendsto_normSq_coprime_pair τ).eventually_gt_atTop (2 * τ.im))
  have hrow : ∀ p : Fin 2 → ℤ, {γ : SL(2, ℤ) | γ 1 = p ∧ |(γ • τ).re| ≤ 1 / 2}.Finite := by
    intro p
    by_cases hp : IsCoprime (p 0) (p 1)
    · have h := Filter.eventually_cofinite.1
        ((ModularGroup.tendsto_abs_re_smul τ hp).eventually_gt_atTop (1 / 2 : ℝ))
      refine (h.image Subtype.val).subset ?_
      rintro γ ⟨h1, h2⟩
      exact ⟨⟨γ, h1⟩, not_lt.2 h2, rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro γ ⟨h1, -⟩
      exact hp (h1 ▸ ModularGroup.bottom_row_coprime γ)
  refine (hP.biUnion fun p _ => hrow p).subset ?_
  intro γ hγ
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  have hpos := (γ • τ).im_pos
  have hhalf : (1 : ℝ) / 2 ≤ (γ • τ).im := by nlinarith
  rw [ModularGroup.im_smul_eq_div_normSq, le_div_iff₀ (Complex.normSq_pos.2 (denom_ne_zero _ _))] at hhalf
  rw [Set.mem_iUnion₂]
  refine ⟨γ 1, ?_, rfl, hγ.2⟩
  simp only [Set.mem_setOf_eq, not_lt]
  simp [UpperHalfPlane.denom] at hhalf ⊢
  linarith

end GlobalTheory.EisM
