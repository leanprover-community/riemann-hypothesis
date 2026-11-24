module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), (∀ j : ℕ, 1 ≤ j → Module.finrank ℚ_[l] ↥(Ks K j) = Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1))) ∧ ∀ χ : GQ l →* ℚ_[l]ˣ, IsCyc χ → ∀ u : ℚ_[l], ‖u‖ = 1 → ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by
  first | exact @GlobalTheory.Cyc.finrank_Ks_and_chi_surjective | exact GlobalTheory.Cyc.finrank_Ks_and_chi_surjective | (intros; apply GlobalTheory.Cyc.finrank_Ks_and_chi_surjective <;> assumption)
