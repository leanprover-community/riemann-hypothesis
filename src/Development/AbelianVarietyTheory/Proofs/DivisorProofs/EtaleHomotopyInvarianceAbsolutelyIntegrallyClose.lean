module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsIntClosedLocalDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingAtPrimeOfEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainMonicRootsOfIsIndEtaleLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgCStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.HInvAic

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]
  exact (hf n).comp (hg n)

theorem eqv_spMap_equiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) :
    Eqv R (spMap (e : A →+* B)) F := by
  intro n
  have h1 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id B; ext x; simp
  have h2 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id A; ext x; simp
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h2, pull_id]
  · rw [← pull_comp, h1, pull_id]

end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

theorem alg (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O] :
    AIC T → SH O → IndEt T O → IsDomain O ∧ AIC O := by
  intro hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  obtain ⟨-, hac⟩ := (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT
  haveI : IsIntegrallyClosed T := ((GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT).1
  refine GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local T O hInd ?_
  intro E _ _ _ P _
  obtain ⟨hd, hc⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale T P (Localization.AtPrime P)
  exact ⟨hd, (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed _).2 ⟨hc, GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' T E P hac⟩⟩
end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

theorem tensor_map_eq (T O : Type) [CommRing T] [CommRing O] [Algebra T O] :
    (Algebra.TensorProduct.map (AlgHom.id T O) (Algebra.ofId T (Polynomial T))).toRingHom =
      (((polyEquivTensor T O).toRingEquiv : Polynomial O →+* O ⊗[T] Polynomial T).comp Polynomial.C).comp
        ((Algebra.TensorProduct.rid T T O).toRingEquiv : O ⊗[T] T →+* O) := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o t =>
    simp only [RingHom.comp_apply, AlgEquiv.coe_toRingEquiv, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      Algebra.TensorProduct.rid_tmul, polyEquivTensor_apply, Polynomial.eval₂_C]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.ofId_apply, Polynomial.algebraMap_eq]
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Polynomial.algebraMap_eq]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  intro q _ T _ _ hT hq i
  have hφ : ((Algebra.ofId T (Polynomial T)).toRingHom : T →+* Polynomial T) = Polynomial.C := by
    ext x <;> simp [Algebra.ofId_apply]
  rw [← hφ]
  apply GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) T T (Polynomial T) (Algebra.ofId T (Polynomial T))

  intro O _ _ hSH hInd
  obtain ⟨hdom, haic⟩ := alg T O hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  have hqO : IsUnit (q : O) := by simpa using hq.map (algebraMap T O)
  have hC := GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain q O haic hqO i
  rw [tensor_map_eq, spMap_comp, spMap_comp]
  exact eqv_comp _ _ _ (eqv_comp _ _ _ (eqv_spMap_equiv _ _) hC) (eqv_spMap_equiv _ _)

end GlobalTheory.HInvAic
