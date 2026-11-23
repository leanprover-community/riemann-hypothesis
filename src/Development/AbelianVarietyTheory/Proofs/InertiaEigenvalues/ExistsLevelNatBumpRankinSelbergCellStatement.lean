module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCell
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_level_nat_bump_rankinSelbergCell : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  first | exact @GlobalTheory.RSParams.exists_level_nat_bump | exact GlobalTheory.RSParams.exists_level_nat_bump | (intros; apply GlobalTheory.RSParams.exists_level_nat_bump <;> assumption)
