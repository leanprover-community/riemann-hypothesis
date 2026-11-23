module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTop
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem normGroup_adjoin_eq_norm_range_completion : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (j : K → Kbar w) (f : w.adicCompletion E →+* W.adicCompletion K) (b : Kbar w ≃+* Kbar W), Continuous f → (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) → (∀ x : K, b (j x) = algebraMap (W.adicCompletion K) _ (algebraMap K (W.adicCompletion K) x)) → (∀ x : E, f (algebraMap E _ x) = algebraMap K _ (algebraMap E K x)) → letI := f.toAlgebra; Neutral.B1.normGroup (w.adicCompletion E) (IntermediateField.adjoin (w.adicCompletion E) (Set.range j)) = (Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)).range := by
  intro E K _ _ _ _ _ w W j f b hfc hb hj hf
  letI := f.toAlgebra

  let c : W.adicCompletion K →ₐ[w.adicCompletion E] Kbar w :=
    { toRingHom := b.symm.toRingHom.comp (algebraMap (W.adicCompletion K) (Kbar W))
      commutes' := fun x => by
        change b.symm (algebraMap _ _ (f x)) = _
        rw [← hb x]; exact b.symm_apply_apply _ }
  have hcj : ∀ x : K, c (algebraMap K (W.adicCompletion K) x) = j x := by
    intro x
    change b.symm (algebraMap _ _ _) = _
    rw [← hj x]; exact b.symm_apply_apply _
  have hrange : c.fieldRange = IntermediateField.adjoin (w.adicCompletion E) (Set.range j) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      have hspan := span_basis_image_adicCompletion_eq_top E K w W f hfc hf _ (Module.finBasis E K)
      have hy : y ∈ Submodule.span (w.adicCompletion E)
          (Set.range fun i => algebraMap K (W.adicCompletion K) (Module.finBasis E K i)) := by
        rw [hspan]; trivial
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        change c _ ∈ _
        rw [hcj]
        exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _)] at hx hy ⊢
        exact add_mem hx hy
      | smul a x _ hx =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul] at hx ⊢
        exact IntermediateField.smul_mem _ hx
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      exact ⟨algebraMap K _ x, hcj x⟩
  let e : W.adicCompletion K ≃ₐ[w.adicCompletion E]
      IntermediateField.adjoin (w.adicCompletion E) (Set.range j) :=
    (AlgEquiv.ofInjectiveField c).trans (IntermediateField.equivOfEq hrange)
  ext u
  simp only [Neutral.B1.normGroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map e.symm.toRingEquiv.toMonoidHom v, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map e.toRingEquiv.toMonoidHom v, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]

end GlobalTheory
