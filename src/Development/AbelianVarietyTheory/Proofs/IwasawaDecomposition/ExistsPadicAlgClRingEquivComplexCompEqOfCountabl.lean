module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.SetTheory.Cardinal.Continuum
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Countable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
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
public import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory

open Cardinal

theorem cardinalMk_padic_eq_continuum (l : ℕ) [Fact l.Prime] : #ℚ_[l] = 𝔠 := by
  apply le_antisymm
  · have hd := Padic.denseRange_ratCast l
    have h : ∀ x : ℚ_[l], ∃ u : ℕ → ℚ,
        Filter.Tendsto (fun n => (u n : ℚ_[l])) Filter.atTop (nhds x) := by
      intro x
      obtain ⟨v, hv, hx⟩ := mem_closure_iff_seq_limit.1 (hd x)
      choose u hu using hv
      exact ⟨u, by simpa only [hu] using hx⟩
    choose u hu using h
    have hi : Function.Injective u := fun x y hxy =>
      tendsto_nhds_unique (hu x) (hxy ▸ hu y)
    refine (Cardinal.mk_le_of_injective hi).trans ?_
    simp
  · exact continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]

theorem cardinalMk_padicAlgCl_eq_continuum (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 := by
  apply le_antisymm
  · exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans
      (max_le (cardinalMk_padic_eq_continuum l).le Cardinal.aleph0_le_continuum)
  · rw [← cardinalMk_padic_eq_continuum l]
    exact Cardinal.mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective

theorem nonempty_padicAlgCl_ringEquiv_complex (l : ℕ) [Fact l.Prime] :
    Nonempty (PadicAlgCl l ≃+* ℂ) :=
  IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [cardinalMk_padicAlgCl_eq_continuum]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [cardinalMk_padicAlgCl_eq_continuum, Cardinal.mk_complex]))

theorem exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable (l : ℕ) [Fact l.Prime]
    (K : Type) [Field K] [Countable K] (a : K →+* PadicAlgCl l) (b : K →+* ℂ) :
    ∃ e : PadicAlgCl l ≃+* ℂ, ∀ x, e (a x) = b x := by
  obtain ⟨e₀⟩ := nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨σ, hσ⟩ := GaloisDescent.exists_complex_ringEquiv_comp_eq (e₀.toRingHom.comp a) b
  exact ⟨e₀.trans σ, fun x => hσ x⟩

theorem exists_padicAlgCl_ringEquiv_complex_comp_eq (l : ℕ) [Fact l.Prime]
    (K : Type) [Field K] [NumberField K] (a : K →+* PadicAlgCl l) (b : K →+* ℂ) :
    ∃ e : PadicAlgCl l ≃+* ℂ, (e : PadicAlgCl l →+* ℂ).comp a = b := by
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨e, he⟩ := exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable l K a b
  exact ⟨e, RingHom.ext he⟩

end GlobalTheory
