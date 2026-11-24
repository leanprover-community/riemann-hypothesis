module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicAlgHomSubDvdOfXDvd
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_normal_subgroup_filtration_index_bounded : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (γ : GQ l) (k : ℕ), 2 ≤ k → ‖(η γ : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k → ∃ H : ℕ → Subgroup (GQ l), (∀ n g, g ∈ H n ↔ ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)) ∧ (∀ n, (H n).Normal) ∧ (∀ n, (H n).index ≠ 0) ∧ (∀ n, (H n).index ≤ l ^ (k + n)) ∧ (∀ n, γ ^ l ^ n ∈ H n) ∧ ∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1) := by
  first | exact @GlobalTheory.galois_congruence_chain | exact GlobalTheory.galois_congruence_chain | (intros; apply GlobalTheory.galois_congruence_chain <;> assumption)
