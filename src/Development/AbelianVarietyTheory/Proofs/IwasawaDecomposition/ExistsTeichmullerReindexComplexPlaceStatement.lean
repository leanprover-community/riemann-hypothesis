module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerReindexComplexPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_teichmuller_reindex_complexPlace : ∀ (g : ℕ) [Fact g.Prime] (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ t₀ : Formalism.CyclotomicNorms.Fbar g →* ℂ, Formalism.L2.NT.IsTeich A κ t₀ ∧ ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t₀ x = t₀ y → x = y := by
  first | exact @GlobalTheory.TeichAt.exists_teich_reindex | exact GlobalTheory.TeichAt.exists_teich_reindex | (intros; apply GlobalTheory.TeichAt.exists_teich_reindex <;> assumption)
