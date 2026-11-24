module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
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

@[expose] public section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.presQuot :
    ∀ (Λ R' R : Type) [CommRing Λ] [CommRing R'] [Algebra Λ R'] [CommRing R] [Algebra Λ R] (a b : ℕ) (τ : Type) [Finite τ] (g : R' →ₐ[Λ] R) (e : τ → R'), HasPres Λ R' a b → Function.Surjective g → RingHom.ker g = Ideal.span (Set.range e) → HasPres Λ R a (b + Nat.card τ) := by
  intro Λ R' R _ _ _ _ _ a b τ _ g e hP hg he
  obtain ⟨π, f, hπ, hk⟩ := hP
  obtain ⟨σ⟩ : Nonempty (τ ≃ Fin (Nat.card τ)) := ⟨Finite.equivFin τ⟩
  choose l hl using fun t => hπ (e t)
  refine ⟨g.comp π, Fin.append f (l ∘ σ.symm), hg.comp hπ, ?_⟩
  have hrange : Set.range (Fin.append f (l ∘ σ.symm)) = Set.range f ∪ Set.range l := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i => exact Or.inl ⟨i, by simp⟩
      | right i => exact Or.inr ⟨σ.symm i, by simp⟩
    · rintro (⟨i, rfl⟩ | ⟨t, rfl⟩)
      · exact ⟨Fin.castAdd _ i, by simp⟩
      · exact ⟨Fin.natAdd _ (σ t), by simp⟩
  have hker : RingHom.ker (g.comp π) = Ideal.comap π (RingHom.ker g) := by
    ext x
    simp [RingHom.mem_ker]
  have hmap : Ideal.span (Set.range e) = Ideal.map π (Ideal.span (Set.range l)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext t
    exact (hl t).symm
  rw [hker, he, hmap, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hk, hrange,
    Ideal.span_union, sup_comm]
