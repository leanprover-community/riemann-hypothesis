module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Topology Filter TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Automorphic

variable (K : Type*) [Field K] [NumberField K]

instance secondCountableTopology_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletion K) := by
  have : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  let O : Set (v.adicCompletion K) := v.adicCompletionIntegers K
  let U : K → Set (v.adicCompletion K) := fun a => {x | x - algebraMap K _ a ∈ O}
  have hO : IsOpen O := GroundTheory.Global.isOpen_adicCompletionIntegers v
  have hU : ∀ a, IsOpen (U a) := fun a => hO.preimage (continuous_id.sub continuous_const)
  have hSC : ∀ a, SecondCountableTopology (U a) := fun a => by
    have : SecondCountableTopology O :=
      inferInstanceAs (SecondCountableTopology (v.adicCompletionIntegers K))
    let φ : U a → O := fun x => ⟨x.1 - algebraMap K _ a, x.2⟩
    have he : IsEmbedding ((Subtype.val : O → v.adicCompletion K) ∘ φ) :=
      (Homeomorph.subRight (algebraMap K (v.adicCompletion K) a)).isEmbedding.comp
        IsEmbedding.subtypeVal
    exact ((IsEmbedding.subtypeVal.of_comp_iff).1 he).secondCountableTopology
  refine secondCountableTopology_of_countable_cover hU ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hV : IsOpen {y : v.adicCompletion K | x - y ∈ O} :=
    hO.preimage (continuous_const.sub continuous_id)
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap K v).exists_mem_open hV
    ⟨x, by simp [O, (v.adicCompletionIntegers K).zero_mem]⟩
  exact ⟨a, ha⟩

instance secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  let R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K
  let A := fun v : HeightOneSpectrum (𝓞 K) =>
    (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  have hAo : ∀ v, IsOpen (A v) := fun v => GroundTheory.Global.isOpen_adicCompletionIntegers v
  have hS : ∀ S : Finset (HeightOneSpectrum (𝓞 K)),
      cofinite ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) := fun S => by
    rw [le_principal_iff]
    exact S.finite_toSet.compl_mem_cofinite
  let U : Finset (HeightOneSpectrum (𝓞 K)) → Set (Πʳ v, [R v, A v]) :=
    fun S => Set.range (RestrictedProduct.inclusion R A (hS S))
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hAo (hS S)).isOpen_range
  have hSC : ∀ S, SecondCountableTopology (U S) := fun S => by
    have h1 :
        SecondCountableTopology (Πʳ v, [R v, A v]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (RestrictedProduct.isOpenEmbedding_inclusion_principal hAo
      (hS S)).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hcov : ⋃ S, U S = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    have hfin : {v | x.1 v ∉ A v}.Finite := x.2
    refine ⟨hfin.toFinset, ⟨x.1, ?_⟩, rfl⟩
    show ∀ᶠ v in 𝓟 ((hfin.toFinset : Set (HeightOneSpectrum (𝓞 K)))ᶜ), x.1 v ∈ A v
    rw [eventually_principal]
    intro v hv
    by_contra h
    exact hv (by simpa using h)
  show SecondCountableTopology (Πʳ v, [R v, A v])
  exact @secondCountableTopology_of_countable_cover _ _ _ _ _ hSC hUo hcov

instance secondCountableTopology_adeleRing : SecondCountableTopology 𝔸[K] :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

end GroundTheory.Automorphic
