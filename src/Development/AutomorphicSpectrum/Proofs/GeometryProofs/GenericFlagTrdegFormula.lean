module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagTrdeg

open scoped IntermediateField.algebraAdjoinAdjoin

theorem card_below_diagonal (n : ℕ) :
    Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = n * (n - 1) / 2 := by
  rw [show Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = Fintype.card (Σ a : Fin n, {b : Fin n // b < a}) from
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b : Fin n => b < a), Fintype.card_sigma]
  have h : ∀ a : Fin n, Fintype.card {b : Fin n // b < a} = a := by
    intro a
    rw [Fintype.card_subtype]
    have e : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by
      ext b
      simp
    rw [e, Fin.card_Iio]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

theorem isTranscendenceBasis_of_adjoin {k K ι : Type} [Field k] [Field K] [Algebra k K] {x : ι → K}
    (hx : AlgebraicIndependent k x)
    (h : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K) :
    IsTranscendenceBasis k x := by
  rw [hx.isTranscendenceBasis_iff_isAlgebraic]
  exact (IsFractionRing.comap_isAlgebraic_iff (A := ↥(Algebra.adjoin k (Set.range x)))
    (K := ↥(IntermediateField.adjoin k (Set.range x))) (C := K)).2 h

theorem trdeg_of_isGenericFlag (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E : Type) [AddCommGroup E]
    [Module Ω₀ E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (S : Type) [Fintype S]
    (r : S → ℕ) (V : S → Submodule Ω₀ E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ)
    (hg : IsGenericFlag (Ω' := Ω) j V b₀ d) :
    Algebra.trdeg Ω₀ Ω = ((∑ σ, r σ * (r σ - 1) / 2 : ℕ) : Cardinal) := by
  obtain ⟨c, u, -, -, -, -, hdiag, hup, -, hind, hd, hfr⟩ := hg
  have heq : IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨σ, l, k⟩, rfl⟩
      rcases lt_trichotomy k l with hkl | hkl | hkl
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l, k), hkl⟩⟩, rfl⟩
      · subst hkl
        simp only [hdiag]
        exact one_mem _
      · simp only [hup σ l k hkl]
        exact zero_mem _
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨σ, ⟨⟨l, k⟩, hkl⟩⟩, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, (l, k)⟩, rfl⟩
  haveI : Module.Finite (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact hd)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω :=
    Algebra.IsAlgebraic.of_finite _ _
  rw [heq] at halg
  have hb := isTranscendenceBasis_of_adjoin hind halg
  rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype, Fintype.card_sigma]
  simp only [card_below_diagonal]

end GlobalTheory.CompanionTheory.Ar.FlagTrdeg
