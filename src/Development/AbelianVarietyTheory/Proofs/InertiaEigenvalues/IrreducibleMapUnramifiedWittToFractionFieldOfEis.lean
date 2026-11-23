module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
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
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.TameFrob

open Polynomial

attribute [local instance] algK isFractionRing

theorem irreducible_map_iota_of_eisenstein : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic → 0 < E.natDegree →
    (∀ i < E.natDegree, (l : Wq l a) ∣ E.coeff i) → (∃ w : (Wq l a)ˣ, E.coeff 0 = (l : Wq l a) * w) →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) := by
  intro l _ a _ E hmon hdeg hdiv ⟨w, hw⟩
  have hP : (Ideal.span {(l : Wq l a)}).IsPrime := by
    rw [← WittVector.ker_constantCoeff]; exact RingHom.ker_isPrime _
  have hl0 : (l : Wq l a) ≠ 0 := fun h => by
    have := congrArg (iotaO l a) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hW : Irreducible E := by
    refine Polynomial.IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hP hmon.isPrimitive hdeg
    · rw [hmon.leadingCoeff]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro n hn
      exact Ideal.mem_span_singleton.2 (hdiv n hn)
    · rw [hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      have h1 : (l : Wq l a) * ((w : Wq l a) - l * c) = 0 := by linear_combination hc
      have h2 : (w : Wq l a) = l * c := by
        have := (mul_eq_zero.1 h1).resolve_left hl0
        linear_combination this
      have h3 := congrArg WittVector.constantCoeff h2
      rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul] at h3
      exact (w.isUnit.map WittVector.constantCoeff).ne_zero h3
  have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ↥(Kunr l a))).1 hW
  exact h

end GlobalTheory.TameFrob
