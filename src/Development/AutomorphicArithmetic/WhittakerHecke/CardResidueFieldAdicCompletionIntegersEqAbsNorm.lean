module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.DiscreteGroups.GlobalIrreducibility.DzApprox
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

theorem UpperTheory.card_residueField_adicCompletionIntegers_eq_absNorm :
    ∀ {L : Type} [Field L] [NumberField L] (u : HeightOneSpectrum (𝓞 L)),
        Nat.card (IsLocalRing.ResidueField (u.adicCompletionIntegers L)) = normV u := by
  intro L _ _ u
  have hmax : ∀ a : u.adicCompletionIntegers L, a ∈ IsLocalRing.maximalIdeal (u.adicCompletionIntegers L) ↔ Valued.v (a : u.adicCompletion L) < 1 := by
    intro a
    unfold HeightOneSpectrum.adicCompletionIntegers at a ⊢
    exact Valuation.mem_maximalIdeal_iff _ _
  have hval : ∀ x : 𝓞 L, Valued.v ((algebraMap (𝓞 L) (u.adicCompletionIntegers L) x : u.adicCompletionIntegers L) : u.adicCompletion L) < 1 ↔ x ∈ u.asIdeal := by
    intro x
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
    rfl
  let ψ : 𝓞 L →+* IsLocalRing.ResidueField (u.adicCompletionIntegers L) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 L) (u.adicCompletionIntegers L))
  have hker : RingHom.ker ψ = u.asIdeal := by
    ext x
    rw [RingHom.mem_ker]
    show IsLocalRing.residue _ _ = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, hmax, hval]
  have hsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    have ha : Valued.v (a : u.adicCompletion L) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp a.2
    obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl u _ ha
    refine ⟨x, ?_⟩
    show IsLocalRing.residue _ _ = _
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmax]
    exact hx
  show Nat.card _ = Nat.card (𝓞 L ⧸ u.asIdeal)
  exact (Nat.card_congr ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)).toEquiv).symm
