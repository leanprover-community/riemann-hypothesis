module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem fieldUnitBounded_of_packing (hP : NormOnePacking) (hT : TensorLattice) :
    FieldUnitBounded := by
  unfold FieldUnitBounded
  intro F B _ _ _ _ _ τ hB hτ

  obtain ⟨hTop, hLC, hT2, hSC, _hinj, hdisc, C, hC, hcov⟩ := hT F B
  let : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  have := hTop
  have := hLC
  have := hT2
  have := hSC

  have : Nontrivial B := ⟨hB.exists_pair_ne⟩
  have : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have : Infinite B := Infinite.of_injective (algebraMap F B) (algebraMap F B).injective
  have : NoncompactSpace (B ⊗[F] AdeleRing (𝓞 F) F) := by
    refine ⟨fun hU => ?_⟩
    have hfin := hdisc Set.univ hU
    simp only [Set.mem_univ, Set.ofPred_true] at hfin
    exact Set.infinite_univ hfin

  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable B := (Module.finBasis F B).equivFun.injective.countable

  let ι := inclE (F := F) (E := B) (AdeleRing (𝓞 F) F)
  let Λ : AddSubgroup (B ⊗[F] AdeleRing (𝓞 F) F) := ι.toAddMonoidHom.range
  have hΛ : Countable Λ := by
    refine Function.Surjective.countable (f := fun b : B => (⟨ι b, b, rfl⟩ : Λ)) ?_
    rintro ⟨y, b, rfl⟩
    exact ⟨b, rfl⟩
  have hcoc : ∃ C' : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact C' ∧
      ∀ x, ∃ l ∈ Λ, x - l ∈ C' := by
    refine ⟨C, hC, fun x => ?_⟩
    obtain ⟨β, hβ⟩ := hcov x
    exact ⟨ι β, ⟨β, rfl⟩, hβ⟩

  obtain ⟨D, hD, hDu⟩ := hP (B ⊗[F] AdeleRing (𝓞 F) F) (sigR τ (AdeleRing (𝓞 F) F))
    (continuous_sigR τ (AdeleRing (𝓞 F) F)) (sigR_sigR hτ (AdeleRing (𝓞 F) F)) Λ hΛ hcoc
  refine ⟨D, hD, fun u hu => ?_⟩
  obtain ⟨β, ⟨b, rfl⟩, hβ0, huβ⟩ := hDu u hu

  have hb : b ≠ 0 := by
    rintro rfl
    exact hβ0 (map_zero ι)
  obtain ⟨c, hc⟩ := hB.mul_inv_cancel hb
  exact ⟨b, ⟨⟨b, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩, huβ⟩

end GlobalTheory.RegSS
