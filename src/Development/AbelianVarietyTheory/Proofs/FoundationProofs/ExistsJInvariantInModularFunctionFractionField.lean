module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralCuspExpansionJInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOneStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem j_in_frac : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), ∃ a : GlobalTheory.FN.ring ε.range, (a : ℍ → ℂ) = jT ∧ (∀ γ : SL(2, ℤ), T.sl (ofSL γ) (T.io a) = T.io a) ∧ (T.exp (T.io a)).coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → (T.exp (T.io a)).coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, (T.exp (T.io a)).coeff r = n := by
  intro Ω _ _ _ ε T
  have hlv := (GlobalTheory.T.lv_jT_one_and_jT_smul_eq ε.range).1
  let a : GlobalTheory.FN.ring ε.range := ⟨jT, mem_ring_of_inR ⟨1, 1, one_pos, hlv⟩⟩
  have ha : (a : ℍ → ℂ) = jT := rfl
  obtain ⟨h, hexp, h1, h2, h3⟩ := GlobalTheory.T.exists_integral_cuspExpansion_jInvariant Ω ε
  have heq : T.exp (T.io a) = h :=
    (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 jT _ _ (T.exp_io a) hexp
  refine ⟨a, ha, fun γ => ?_, ?_, ?_, ?_⟩
  · apply T.sl_io
    rw [ha, (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.1 γ jT]
    funext τ
    exact ((GlobalTheory.T.lv_jT_one_and_jT_smul_eq ε.range).2 γ τ).symm
  · rw [heq]; exact h1
  · rw [heq]; exact h2
  · rw [heq]; exact h3

end GlobalTheory.FN
