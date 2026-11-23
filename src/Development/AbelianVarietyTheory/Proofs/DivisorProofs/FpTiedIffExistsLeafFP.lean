module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledValuationFormula
public import Formalism.QuotientMetricDivisors.Statement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FinitePlacesCompare

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

variable {K : Type} [Field K] [NumberField K]

theorem lw_nonneg (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

omit [NumberField K] in
theorem localization_mono' {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (p : Ideal (𝓞 K)) [p.IsPrime]
    {L L' : Submodule (𝓞 K) W} (h : L ≤ L') : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem primePow_anti (w : HeightOneSpectrum (𝓞 K)) {n n' : ℤ} (h : n' ≤ n) : primePow w n ≤ primePow w n' := by
  have hP : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot
  obtain ⟨k, rfl⟩ := Int.le.dest h
  have h1 : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ k ≤ 1 := by
    rw [← FractionalIdeal.coeIdeal_pow]; exact FractionalIdeal.coeIdeal_le_one
  have h2 : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (n' + (k : ℤ)) ≤
      (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n' := by
    rw [zpow_add₀ hP, zpow_natCast]
    calc _ ≤ (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n' * 1 := by gcongr
      _ = _ := mul_one _
  exact FractionalIdeal.coe_le_coe.mpr h2

theorem scaledAt_anti {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) (Fin d → K)) {n n' : ℤ}
    (h : n' ≤ n) : scaledAt w n B ≤ scaledAt w n' B := by
  refine localization_mono' _ (Submodule.span_mono ?_)
  rintro z ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, primePow_anti w h ha, x, hx, rfl⟩

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

end GlobalTheory.FinitePlacesCompare
