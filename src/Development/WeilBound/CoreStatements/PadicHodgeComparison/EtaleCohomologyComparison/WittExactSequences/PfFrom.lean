import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem isRt_rt : IsRt l (rt l) ∧ rt l 0 = pFlat l := by
  refine ⟨fun k => ?_, ?_⟩
  · apply (iterateFrobeniusEquiv (Ob l) l k).injective
    have h1 : iterateFrobeniusEquiv (Ob l) l (k + 1) (rt l (k + 1)) = pFlat l := RingEquiv.apply_symm_apply _ _
    have h2 : iterateFrobeniusEquiv (Ob l) l k (rt l k) = pFlat l := RingEquiv.apply_symm_apply _ _
    rw [h2, ← h1, iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, ← pow_mul, pow_succ']
  · change (iterateFrobeniusEquiv (Ob l) l 0).symm (pFlat l) = pFlat l
    rw [iterateFrobeniusEquiv_zero]; rfl

theorem toPf_full : (toPf l).Full ∧ (toPf l).Faithful := by
  refine ⟨⟨fun {A B} φ => ⟨⟨φ.hom.hom.toRingHom, RingHom.ext fun c => φ.hom.hom.commutes c⟩, ?_⟩⟩,
    ⟨fun {A B} f g h => ?_⟩⟩
  · exact InducedCategory.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun x => rfl))
  · have h' := congrArg (fun φ => φ.hom.hom.toRingHom) h
    exact PAlg.Hom.ext h'

end CrystallineSemistableComparison.D
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

abbrev pfOb {R : Type} [CommRing R] {p : ℕ} (X : Type) [CommRing X] [Algebra R X] (h : Pf p X) : PfC p R :=
  ⟨CommAlgCat.of R X, h⟩

abbrev pfHom {R : Type} [CommRing R] {p : ℕ} {X Y : Type} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y]
    {hX : Pf p X} {hY : Pf p Y} (φ : X →ₐ[R] Y) : pfOb (R := R) X hX ⟶ pfOb (R := R) Y hY :=
  ObjectProperty.homMk (CommAlgCat.ofHom φ)

abbrev pfFrom {R : Type} [CommRing R] {p : ℕ} (A : PfC p R) (B : Type) [CommRing B] [Algebra R B] [Algebra A.obj B]
    [IsScalarTower R A.obj B] (hB : Pf p B) : A ⟶ pfOb (R := R) B hB :=
  ObjectProperty.homMk (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A.obj B))

end CrystallineSemistableComparison.D
end
end
