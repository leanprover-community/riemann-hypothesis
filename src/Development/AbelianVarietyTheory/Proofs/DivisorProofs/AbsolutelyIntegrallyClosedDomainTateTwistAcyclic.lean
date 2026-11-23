module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRooStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHenseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictlyHenselianOfIsFieldMonicRootsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShEqvTwStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.AicAcyc

theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : AIC K := by
  intro p hp hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem isIso_spMap {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) : IsIso (spMap (e : A →+* B)) := by
  haveI : IsIso (CommRingCat.ofHom (e : A →+* B)) := (RingEquiv.toCommRingCatIso e).isIso_hom
  unfold spMap
  infer_instance

end GlobalTheory.EtC.AicAcyc

namespace GlobalTheory.EtC


open GlobalTheory.EtC.AicAcyc in
theorem b5 : B5 := by
  intro q A _ _ hA hq n i hn
  haveI := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  have hK : SH (FractionRing A) :=
    GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots (FractionRing A) (Field.toIsField _) (aic_of_isAlgClosed _)
  have hE := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have heqv : Eqv (ZMod q) (spMap (algebraMap A (FractionRing A))) (tw q i) := by
    refine GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) A A (FractionRing A)
      (Algebra.ofId A (FractionRing A)) ?_
    intro O _ _ hO hOind
    obtain ⟨hfield, haic⟩ := GlobalTheory.T.isField_monicRoots_tensor_fractionRing_strictlyHenselian A O hA hO hOind
    have hSH : SH (O ⊗[A] FractionRing A) := GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots _ hfield haic
    have hqO : IsUnit (q : O) := by
      simpa using hq.map (algebraMap A O)
    let e := Algebra.TensorProduct.rid A A O
    let j : O →ₐ[A] O ⊗[A] FractionRing A := Algebra.TensorProduct.includeLeft
    have hψ : (Algebra.TensorProduct.map (AlgHom.id A O) (Algebra.ofId A (FractionRing A))) =
        j.comp e.toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro o a
      simp [j, e, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [hψ]
    have h1 : Eqv (ZMod q) (spMap (j : O →+* O ⊗[A] FractionRing A)) (tw q i) :=
      GlobalTheory.T.eqv_spMap_tw_of_isUnit q i O _ (j : O →+* O ⊗[A] FractionRing A) hO hSH hqO
    have h2 : Eqv (ZMod q) (spMap ((e : O ⊗[A] A ≃+* O) : O ⊗[A] A →+* O)) (tw q i) := by
      haveI := isIso_spMap (e : O ⊗[A] A ≃+* O)
      exact hE.1 _ _ _ inferInstance
    have h3 := (hE.2.1 _ _ _ _ _).1 h1 h2
    rw [← spMap_comp] at h3
    exact h3
  have hacK : AcycF (ZMod q) (sp (FractionRing A)) (tw q i) :=
    fun m hm => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) (FractionRing A) hK (tw q i) m hm
  exact (hE.2.2.2 _ _ _ heqv).1 hacK n hn

end GlobalTheory.EtC

end
