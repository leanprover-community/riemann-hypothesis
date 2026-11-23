module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

theorem hasOrbInt_of_isCompact_cent_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsCompact (cent s : Set H) → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant], IsProperOrbit (cent s) s → ∀ (y : H) (f : H → ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ s dt f ((∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) / dt.real Set.univ) := by
  intro H _ _ _ _ _ _ _ _ μ _ _ s hT dt _ _ hP y f hf hc
  haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
  obtain ⟨C, hC, h0⟩ := hP _ hc
  have hcont : Continuous (conjFn s f) := hf.comp (by fun_prop)
  have hsupp : HasCompactSupport (conjFn s f) := by
    refine HasCompactSupport.intro' (hT.mul hC) (hT.mul hC).isClosed fun x hx => ?_
    by_contra hne
    obtain ⟨t, ht, htx⟩ := h0 x (subset_tsupport f hne)
    exact hx ⟨t⁻¹, (cent s).inv_mem ht, t * x, htx, by group⟩
  have hint : Integrable (conjFn s f) μ := hcont.integrable_of_hasCompactSupport hsupp
  have e : (∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) = ∫ x, f (x⁻¹ * s * x) ∂μ := by
    have := integral_mul_left_eq_self (μ := μ) (fun z => f (z⁻¹ * s * z)) y
    rw [← this]
    congr 1; ext x; congr 1; group
  rw [e]
  exact hasOrbInt_of_finite hint

end GlobalTheory
