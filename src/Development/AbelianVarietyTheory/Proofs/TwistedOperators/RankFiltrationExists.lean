module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenSetOfLeRank
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

theorem comp_mem_SB_of_isInducing {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsInducing i) (Φ : SB X) {C : Set X} (hC : IsClosed C) (hiC : ∀ y, i y ∈ C)
    (hs : ∀ x ∈ C, Φ.1 x ≠ 0 → x ∈ Set.range i) : (fun y => Φ.1 (i y)) ∈ SB Y := by
  refine ⟨Φ.2.1.comp_continuous hi.continuous, ?_⟩
  have h0 : IsClosed (Function.support Φ.1) := (Φ.2.1.isOpen_fiber 0).isClosed_compl
  have h1 : IsCompact (Function.support Φ.1) := Φ.2.2.of_isClosed_subset h0 subset_closure
  have h2 : IsCompact (i ⁻¹' (Function.support Φ.1 ∩ C)) :=
    hi.isCompact_preimage' (h1.inter_right hC) fun x hx => hs x hx.2 hx.1
  refine HasCompactSupport.intro' h2 ((h0.inter hC).preimage hi.continuous) fun y hy => ?_
  by_contra h
  exact hy ⟨h, hiC y⟩

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]


omit [DecidableEq a] [DecidableEq b] in
theorem isOpen_le_rank (κ : ℕ) : IsOpen {x : Matrix b a k | κ ≤ x.rank} := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  exact GlobalTheory.isOpen_setOf_le_rank k b a κ



end

end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
