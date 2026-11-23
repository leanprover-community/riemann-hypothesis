module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCutUnipBMulLevSet
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem rowCutInf_unipB_mul_levSetInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n),
    ∀ g ∈ levSetInf E n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) =
      rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧
    ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  intro E _ _ n ρ g hg
  have hw : ∀ w, compGL w g ∈ levSet n (ρ + 1) := hg
  have hc : ∀ w (x : GL (Fin n) (Cinf E)) j,
      rowCut ρ ((compGL w x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) j =
        rowCutInf ρ (x : Matrix (Fin n) (Fin n) (Cinf E)) j w := by
    intro w x j
    unfold rowCut rowCutInf
    split_ifs <;> rfl
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    have hmem : ∀ w, compGL w u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n) := by
      intro w
      refine (GlobalTheory.SmGL.mem_unipB ℂ).2 ⟨fun i j h => ?_, fun i => ?_⟩
      · rw [compGL_apply, hu0 i j h]; rfl
      · rw [compGL_apply, hu1 i]; rfl
    funext j w
    rw [← hc, ← hc, map_mul]
    exact congrFun ((truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).1 _ (hmem w)) j
  · intro w
    obtain ⟨j, hj, hne⟩ := (truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).2
    exact ⟨j, hj, by rwa [← hc]⟩

end GlobalTheory.JSW.MirCinf
