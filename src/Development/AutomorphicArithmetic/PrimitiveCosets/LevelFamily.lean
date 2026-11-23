module

public import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
public import Development.AutomorphicArithmetic.PrimitiveCosets.GChiEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia
import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.SChain

@[expose] public section

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

open Classical in
private noncomputable def UpperTheory.Comparison₂.level_family_wt (Λ : Level) (ψ : PChar) : ℝ :=
  if ψ = PChar.one then 1 else Λ.wt ψ

private theorem UpperTheory.Comparison₂.level_family_wt_pos (Λ : Level) (ψ : PChar) : 0 < UpperTheory.Comparison₂.level_family_wt Λ ψ := by
  unfold UpperTheory.Comparison₂.level_family_wt Level.wt
  split_ifs
  · exact one_pos
  · exact one_pos
  · positivity

private theorem UpperTheory.Comparison₂.level_family_adm (ψ : PChar) : ψ.N = 1 ∨ ψ.χ ≠ 1 := by
  by_cases h : ψ.χ = 1
  · left
    have hp := ψ.prim
    rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
    exact hp.symm
  · exact Or.inr h

private theorem UpperTheory.Comparison₂.level_family_sum (Λ : Level) (y : ℝ) :
    ∑ ψ ∈ Λ.KEPT, UpperTheory.Comparison₂.level_family_wt Λ ψ * (Deduction.Gchi ψ.χ y).re = Λ.Gm y := by
  classical
  rw [← Finset.add_sum_erase _ _ Λ.one_mem, Level.Gm, Level.Nt]
  congr 1
  · have h1 : UpperTheory.Comparison₂.level_family_wt Λ PChar.one = 1 := by
      simp [UpperTheory.Comparison₂.level_family_wt]
    have hG : Formalism.Gz y = An.G y := by
      unfold Formalism.Gz Formalism.Sz An.G
      have hsum : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)) =
          ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / n - 1) 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
        have hn_pos : 0 < n := Nat.zero_lt_of_lt hn₁
        have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' hn_pos.ne').mp hn₂
        have hnonneg : 0 ≤ y / (n : ℝ) - 1 := by
          rw [sub_nonneg, le_div_iff₀ (Nat.cast_pos.mpr hn_pos), one_mul]
          exact hny
        rw [max_eq_left hnonneg]
      rw [hsum]
      ring
    rw [h1, one_mul, ← gChi_eq, hG]
    simp only [An.gChi, PChar.one]
    exact (congrArg Complex.re (ite_eq_left rfl)).trans (Complex.ofReal_re _)
  · refine Finset.sum_congr (by congr) fun ψ hψ => ?_
    have hne : ψ ≠ PChar.one := Finset.ne_of_mem_erase hψ
    simp only [UpperTheory.Comparison₂.level_family_wt, ite_eq_right hne, gChi_eq]

theorem UpperTheory.Comparison₂.level_family :
    ∀ Λ : Level, ∃ F : Deduction.CharFamily, (∀ y, Deduction.Gm F y = Λ.Gm y) ∧ ∀ θ, Deduction.ZeroFree F θ ↔ Λ.ZeroFreeAbove θ := by
  intro Λ
  refine ⟨@Deduction.CharFamily.mk Λ.KEPT _ (fun i => i.1.N) (fun i => i.1.ne) (fun i => i.1.χ) (fun i => UpperTheory.Comparison₂.level_family_wt Λ i.1) (fun i => UpperTheory.Comparison₂.level_family_wt_pos Λ i.1) (fun i => UpperTheory.Comparison₂.level_family_adm i.1), fun y => ?_, fun θ => ?_⟩
  · rw [← UpperTheory.Comparison₂.level_family_sum Λ y, Deduction.Gm]
    exact Finset.sum_coe_sort Λ.KEPT (fun ψ => UpperTheory.Comparison₂.level_family_wt Λ ψ * (Deduction.Gchi ψ.χ y).re)
  · simp only [Deduction.ZeroFree, Level.ZeroFreeAbove, PChar.ZeroFreeAbove]
    constructor
    · intro h ψ hψ s hs
      exact h ⟨ψ, hψ⟩ s hs
    · intro h i s hs
      exact h i.1 i.2 s hs
