import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem eqv_of_isIso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) :
    Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, ?_, ?_⟩
  · intro x
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · intro x
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem hInv_of_subsingleton : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], Subsingleton A → HInv q A := by
  intro q _ A _ hA i
  have hb : Function.Bijective (Polynomial.C : A →+* Polynomial A) :=
    ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  let e : A ≃+* Polynomial A := RingEquiv.ofBijective _ hb
  haveI : IsIso (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) :=
    (RingEquiv.toCommRingCatIso e).isIso_hom
  haveI : IsIso (spMap (Polynomial.C : A →+* Polynomial A)) := by
    unfold spMap; infer_instance
  exact eqv_of_isIso _ _

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], Subsingleton A → HInv q A := by
  first | exact @GlobalTheory.EtC.hInv_of_subsingleton | exact GlobalTheory.EtC.hInv_of_subsingleton | (intros; apply GlobalTheory.EtC.hInv_of_subsingleton; all_goals assumption)
end
