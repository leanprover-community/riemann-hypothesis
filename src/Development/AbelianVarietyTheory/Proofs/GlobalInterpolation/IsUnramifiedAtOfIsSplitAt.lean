module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitUnram



theorem isUnramifiedAt_of_isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (w : HeightOneSpectrum (𝓞 L)), IsSplitAt w →
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  intro L _ _ _ w hw
  obtain ⟨u, hne, hu⟩ := hw
  set K := maximalRealSubfield L
  set p : Ideal (𝓞 K) := w.asIdeal.under (𝓞 K) with hpdef
  have hup : u.asIdeal.under (𝓞 K) = p := by
    have := congrArg HeightOneSpectrum.asIdeal hu
    exact this
  haveI : w.asIdeal.LiesOver p := ⟨rfl⟩
  haveI : u.asIdeal.LiesOver p := ⟨hup.symm⟩
  have hp0 : p ≠ ⊥ := (w.under (𝓞 K)).ne_bot
  haveI hpm : p.IsMaximal := (w.under (𝓞 K)).isMaximal
  have hwmem : w.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨w.isPrime, inferInstance⟩
  have humem : u.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨u.isPrime, inferInstance⟩
  have hneI : u.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) K L (p := p) hp0
  rw [Algebra.IsQuadraticExtension.finrank_eq_two K L] at hsum
  have hterm : ∀ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 L), 1 ≤ p.ramificationIdx' P * p.inertiaDeg' P := by
    intro P hP
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).1 hP
    haveI := hPp; haveI := hPl
    have h1 : 0 < p.ramificationIdx' P := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
      exact Ideal.ramificationIdx_pos (R := 𝓞 K) P
    have h2 : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1.ne' h2.ne')
  have hpair : ({w.asIdeal, u.asIdeal} : Finset (Ideal (𝓞 L))) ⊆ IsDedekindDomain.primesOverFinset p (𝓞 L) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hwmem
    · exact humem
  have hle := Finset.sum_le_sum_of_subset (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hpair
  rw [Finset.sum_pair hneI.symm, hsum] at hle
  have hu1 := hterm _ humem
  have hw1 : p.ramificationIdx' w.asIdeal * p.inertiaDeg' w.asIdeal = 1 := by
    have := hterm _ hwmem
    omega
  have he : p.ramificationIdx' w.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_right hw1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p w.asIdeal hp0] at he
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain).2 he

end GlobalTheory.SplitUnram
