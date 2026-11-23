module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.InductionParabolicGroups
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
private theorem block_zj_eq_diagonal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ)
    (j : Fin h) :
    ((leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1 := by
  ext i l
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, l'⟩, rfl⟩ := (stdBlocks d hd).surjective l
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hil : i' = l'
    · subst hil
      by_cases haj : a ≤ j
      · simp [Zl.JC.zj, Zl.JC.blockIdx, haj, Matrix.GeneralLinearGroup.scalar]
      · simp [Zl.JC.zj, Zl.JC.blockIdx, haj]
    · have hne : (stdBlocks d hd) ⟨a, i'⟩ ≠ (stdBlocks d hd) ⟨a, l'⟩ := fun e => hil (by
        simpa using (stdBlocks d hd).injective e)
      rw [Matrix.diagonal_apply_ne _ hne]
      by_cases haj : a ≤ j
      · simp [Zl.JC.zj, haj, Matrix.GeneralLinearGroup.scalar, hil]
      · simp [Zl.JC.zj, haj, hil]
  · have hne : (stdBlocks d hd) ⟨a, i'⟩ ≠ (stdBlocks d hd) ⟨b, l'⟩ := fun e => hab (by
      simpa using congrArg Sigma.fst ((stdBlocks d hd).injective e))
    rw [leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ hne]



theorem _root_.GlobalTheory.T.block_central_element_commutes_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h), ∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd), leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * y = y * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) := by
  intro k _ _ _ _ h N d hd t j y hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, block_zj_eq_diagonal]
  ext i l
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hil : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l
  · rw [hil]
    exact mul_comm _ _
  · have h0 : (y : Matrix (Fin N) (Fin N) k) i l = 0 :=
      GroundTheory.Automorphic.Parabolic.mem_levi.1 hy i l hil
    rw [h0, mul_zero, zero_mul]

