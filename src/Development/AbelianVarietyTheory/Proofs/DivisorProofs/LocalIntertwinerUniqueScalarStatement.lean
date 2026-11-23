module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIntertwinerUniqueScalar
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal


theorem _root_.GlobalTheory.T.local_intertwiner_unique_scalar : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) [Invertible (2 : Fv F v)] (κ : Type) [Fintype κ]
    (ψv : AddChar (Fv F v) ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ (T : ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ) (A : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v)),
      (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
      (∀ w, ∀ φ ∈ SB (κ → Fv F v), T (schr ψv w φ) = schr ψv (A w) (T φ)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => T φ x * starRingEnd ℂ (T φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
  first | exact @GlobalTheory.CompactOpenLattice.inner_eq_const_mul | exact GlobalTheory.CompactOpenLattice.inner_eq_const_mul | (intros; apply GlobalTheory.CompactOpenLattice.inner_eq_const_mul <;> assumption)
