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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.RegSS Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem normOne_bounded_of_unit_bounded {B X : Type} [CommRing B] [CommRing X]
    [TopologicalSpace X] [IsTopologicalRing X] (i : B →+* X) (τ : B →+* B) (s : X →+* X)
    (hs : Continuous s) (hi : ∀ b, i (τ b) = s (i b))
    (hfin : ∀ D : Set X, IsCompact D → {β : B | i β ∈ D}.Finite)
    (D : Set X) (hD : IsCompact D)
    (h : ∀ u : X, u * s u = 1 → ∃ β : B, IsUnit β ∧ u * i β ∈ D) :
    ∃ D' : Set X, IsCompact D' ∧
      ∀ u : X, u * s u = 1 → ∃ β : B, β * τ β = 1 ∧ u * i β ∈ D' := by
  classical

  set K : Set X := (fun x => x * s x) '' D with hK
  have hKc : IsCompact K := hD.image (continuous_id.mul hs : Continuous fun x : X => x * s x)

  set T : Set B := {γ : B | i γ ∈ K} with hT
  have hTf : T.Finite := hfin K hKc

  let c : B → B := fun γ =>
    if h : ∃ p : B × B, p.1 * p.2 = 1 ∧ p.1 * τ p.1 = γ then (Classical.choose h).2 else 0
  refine ⟨⋃ γ ∈ T, (fun x => x * i (c γ)) '' D,
    hTf.isCompact_biUnion fun γ _ => hD.image (continuous_mul_const _), ?_⟩
  intro u hu
  obtain ⟨β, hβ, hβD⟩ := h u hu
  obtain ⟨β', hβ'⟩ := hβ.exists_right_inv
  have hex : ∃ p : B × B, p.1 * p.2 = 1 ∧ p.1 * τ p.1 = β * τ β := ⟨(β, β'), hβ', rfl⟩
  set p := Classical.choose hex with hpdef
  have hp : p.1 * p.2 = 1 ∧ p.1 * τ p.1 = β * τ β := Classical.choose_spec hex
  have hc : c (β * τ β) = p.2 := by
    show (if h : ∃ q : B × B, q.1 * q.2 = 1 ∧ q.1 * τ q.1 = β * τ β
      then (Classical.choose h).2 else 0) = p.2
    rw [dite_eq_left hex]

  refine ⟨β * p.2, ?_, ?_⟩
  · calc β * p.2 * τ (β * p.2) = (β * τ β) * (p.2 * τ p.2) := by rw [map_mul]; ring
      _ = (p.1 * τ p.1) * (p.2 * τ p.2) := by rw [hp.2]
      _ = (p.1 * p.2) * τ (p.1 * p.2) := by rw [map_mul τ p.1 p.2]; ring
      _ = 1 := by rw [hp.1, map_one, one_mul]
  · have hmem : β * τ β ∈ T := by
      show i (β * τ β) ∈ K
      refine ⟨u * i β, hβD, ?_⟩
      show u * i β * s (u * i β) = i (β * τ β)
      rw [map_mul s, map_mul i, hi]
      calc u * i β * (s u * s (i β)) = (u * s u) * (i β * s (i β)) := by ring
        _ = i β * s (i β) := by rw [hu, one_mul]
    refine Set.mem_biUnion hmem ⟨u * i β, hβD, ?_⟩
    show u * i β * i (c (β * τ β)) = u * i (β * p.2)
    rw [hc, map_mul i, mul_assoc]

theorem normOfUnitBounded_of_tensorLattice :
    GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.NormOfUnitBounded := by
  intro hL F B _ _ _ _ _ τ hU
  let _ : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  obtain ⟨hTR, -, -, -, -, hfin, -⟩ := hL F B
  have := hTR
  obtain ⟨D, hD, hDu⟩ := hU
  exact normOne_bounded_of_unit_bounded (inclE (F := F) (AdeleRing (𝓞 F) F)) (τ : B →+* B)
    (sigR τ (AdeleRing (𝓞 F) F)) (continuous_sigR τ _) (fun b => inclE_conj τ _ b) hfin D hD hDu

end GlobalTheory.RegSS
