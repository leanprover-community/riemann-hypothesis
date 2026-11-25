module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnipotentInCompactSubgroup
import GroundTheory.AutomorphicForms.GLnLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

theorem exists_compact_subgroup_between {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {U : Subgroup (GL (Fin N) k)}
    (hU : U ≤ unipB k (Fin N)) (hcl : IsClosed (U : Set (GL (Fin N) k)))
    (Q : Set (GL (Fin N) k)) (hQ : IsCompact Q) (hQU : Q ⊆ (U : Set (GL (Fin N) k))) :
    ∃ L : {L : Subgroup (GL (Fin N) k) // IsCompact (L : Set (GL (Fin N) k)) ∧ L ≤ U},
      Q ⊆ (L.1 : Set (GL (Fin N) k)) := by
  obtain ⟨U₀, hc, hs⟩ := GlobalTheory.UnipCptSub.exists_compact_subgroup_of_isCompact Q hQ
    (fun g hg => hU (hQU hg))
  refine ⟨⟨U₀ ⊓ U, ?_, inf_le_right⟩, fun g hg => ⟨hs hg, hQU hg⟩⟩
  rw [Subgroup.coe_inf]
  exact hc.inter_right hcl

theorem exists_monotone_compact_exhaustion :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (U : Subgroup (GL (Fin N) k)), U ≤ unipB k (Fin N) → IsClosed (U : Set (GL (Fin N) k)) →
      ∃ L : ℕ → Subgroup (GL (Fin N) k), Monotone L ∧ (∀ j, IsCompact (L j : Set (GL (Fin N) k))) ∧
        (∀ j, L j ≤ U) ∧ ∀ n ∈ U, ∃ j, n ∈ L j := by
  intro k _ _ _ _ N U hU hcl
  haveI : SecondCountableTopology (GL (Fin N) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL (Fin N) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI : SigmaCompactSpace (GL (Fin N) k) := inferInstance
  let S := {L : Subgroup (GL (Fin N) k) // IsCompact (L : Set (GL (Fin N) k)) ∧ L ≤ U}
  let K : ℕ → Set (GL (Fin N) k) := compactCovering (GL (Fin N) k)
  have hstep : ∀ (j : ℕ) (A : S), ∃ B : S,
      (K j ∩ (U : Set (GL (Fin N) k))) ∪ (A.1 : Set (GL (Fin N) k)) ⊆ (B.1 : Set (GL (Fin N) k)) :=
    fun j A => exists_compact_subgroup_between hU hcl _
      (((isCompact_compactCovering _ j).inter_right hcl).union A.2.1)
      (Set.union_subset Set.inter_subset_right A.2.2)
  choose next hnext using hstep
  let b : S := ⟨⊥, by rw [Subgroup.coe_bot]; exact isCompact_singleton, bot_le⟩
  let f : ℕ → S := fun j => Nat.rec b (fun i A => next i A) j
  have hsucc : ∀ j, f (j + 1) = next j (f j) := fun _ => rfl
  refine ⟨fun j => (f j).1, monotone_nat_of_le_succ fun j g hg => ?_, fun j => (f j).2.1,
    fun j => (f j).2.2, fun n hn => ?_⟩
  · rw [hsucc]
    exact hnext j (f j) (Or.inr hg)
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1
      ((iUnion_compactCovering (GL (Fin N) k)).symm ▸ Set.mem_univ n : n ∈ ⋃ i, K i)
    refine ⟨j + 1, ?_⟩
    show n ∈ (f (j + 1)).1
    rw [hsucc]
    exact hnext j (f j) (Or.inl ⟨hj, hn⟩)

end GlobalTheory.CompanionTheory.UnipExhaust
