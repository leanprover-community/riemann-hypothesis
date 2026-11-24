module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicUnipotentRadicalCoveredByLeviConjugates
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.isotropicUnipotentRadical_covered_by_levi_conjugates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (V : Set (GAd σ J)) (B : ℝ), IsCompact V ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (GAd σ J), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) ∧ (∀ y ∈ Y, y ∈ unipRad σ J C) ∧ ∀ u ∈ unipRad σ J C, ∃ γ ∈ ratPts σ J, γ ∈ unipRad σ J C ∧ ∃ y ∈ Y, ∃ w ∈ V, w ∈ unipRad σ J C ∧ γ * u = y * lv (tor F E fun i => (μ i : ℤ)) * w * (lv (tor F E fun i => (μ i : ℤ)))⁻¹ := by
  first | exact @GlobalTheory.SphEis.cover_unipRad | exact GlobalTheory.SphEis.cover_unipRad | (intros; apply GlobalTheory.SphEis.cover_unipRad <;> assumption)
