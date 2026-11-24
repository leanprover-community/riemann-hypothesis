module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
theorem _root_.GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧ P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by
  intro K M _ _ _ _ _ S hS h
  choose P P' hne hP hP' hNP hNP' using h
  have key : ∀ {Q : HeightOneSpectrum (𝓞 M)} {v w : HeightOneSpectrum (𝓞 K)},
      Q.asIdeal.LiesOver v.asIdeal → Q.asIdeal.LiesOver w.asIdeal → v = w :=
    fun h₁ h₂ => HeightOneSpectrum.ext (h₁.over.trans h₂.over.symm)
  let f : {v // v ∉ S} × Bool → HeightOneSpectrum (𝓞 M) :=
    fun x => if x.2 then P x.1 x.1.2 else P' x.1 x.1.2
  have lies : ∀ x, (f x).asIdeal.LiesOver x.1.1.asIdeal := by
    rintro ⟨⟨v, hv⟩, b⟩
    cases b
    exacts [hP' v hv, hP v hv]
  refine _root_.GlobalTheory.Mem.ZetaPole.not_injective_double_primes K M S hS f ?_ ?_
  · rintro ⟨⟨v, hv⟩, b⟩ ⟨⟨w, hw⟩, c⟩ hfe
    have hvw : v = w := key (lies (⟨v, hv⟩, b)) (by rw [hfe]; exact lies _)
    subst hvw
    cases b <;> cases c
    · rfl
    · exact absurd hfe.symm (hne v hv)
    · exact absurd hfe (hne v hv)
    · rfl
  · rintro ⟨⟨v, hv⟩, b⟩
    cases b
    exacts [hNP' v hv, hNP v hv]

end GlobalTheory
