module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory

theorem expand_map_dvd_of_frobS_dvd : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P Q : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → frobS l a (P : (Wq l a)⟦X⟧) ∣ (Q : (Wq l a)⟦X⟧) →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ Q := by
  intro l hl a _ P Q hP hdvd hQ
  have hl0 : 0 < l := hl.out.pos
  set σ : Wq l a →+* Wq l a := (sigma l a : Wq l a →+* Wq l a) with hσ
  have hσinj : Function.Injective σ := (sigma l a).injective
  have hcoe : frobS l a (P : (Wq l a)⟦X⟧) =
      ((Polynomial.expand (Wq l a) l (P.map σ) : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) := by
    refine PowerSeries.ext fun n => ?_
    change PowerSeries.coeff n (PowerSeries.map σ (PowerSeries.expand l hl.out.ne_zero (P : (Wq l a)⟦X⟧))) = _
    rw [PowerSeries.coeff_map, PowerSeries.coeff_expand, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_expand hl0]
    split_ifs <;> simp [Polynomial.coeff_map]
  rw [hcoe] at hQ
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have hmon : (Polynomial.expand (Wq l a) l (P.map σ)).Monic := (hP.map σ).expand hl0
  have hdeg : (Polynomial.expand (Wq l a) l (P.map σ)).natDegree = P.natDegree * l := by
    rw [Polynomial.natDegree_expand, Polynomial.natDegree_map_eq_of_injective hσinj]
  have H : (Polynomial.expand (Wq l a) l (P.map σ)).IsDistinguishedAt (Ideal.span {(l : Wq l a)}) :=
    { mem := fun {n} hn => by
        rw [Ideal.mem_span_singleton, Polynomial.coeff_expand hl0]
        rw [hdeg] at hn
        split_ifs with h
        · rw [Polynomial.coeff_map]
          have hlt : n / l < P.natDegree := by
            rw [Nat.div_lt_iff_lt_mul hl0]; exact hn
          obtain ⟨c, hc⟩ := hdvd _ hlt
          refine ⟨σ c, ?_⟩
          rw [hc, map_mul, map_natCast]
        · exact dvd_zero _
      monic := hmon }
  exact GlobalTheory.NB.LT.poly_dvd_of_dvd H hQ

end GlobalTheory
