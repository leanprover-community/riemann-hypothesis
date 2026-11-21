import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Mathlib

section
namespace Formalism.L2.Pj.TranscendenceDegreeLemmas

open Algebra

theorem trdeg_residueField_of_minimal {K A : Type} [Field K] [CommRing A] [Algebra K A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A) :
    Algebra.trdeg K p.ResidueField = n := by
  classical
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K A
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin n) K) A :=
    IsScalarTower.of_algebraMap_eq' (g.comp_algebraMap).symm
  have : Algebra.Etale (MvPolynomial (Fin n) K) A := hg
  have hq : p.under (MvPolynomial (Fin n) K) = ⊥ := by
    by_contra hne
    have : p.LiesOver (p.under (MvPolynomial (Fin n) K)) := ⟨rfl⟩
    obtain ⟨P, hPlt, hP, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥)
      (q := p.under (MvPolynomial (Fin n) K)) p (bot_lt_iff_ne_bot.mpr hne)
    exact (not_le_of_gt hPlt) (hp.2 ⟨hP, bot_le⟩ hPlt.le)
  have : p.LiesOver (⊥ : Ideal (MvPolynomial (Fin n) K)) := ⟨hq.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal (MvPolynomial (Fin n) K)) p
  have : Localization.AtPrime.IsLiesOverAlgebra (⊥ : Ideal (MvPolynomial (Fin n) K)) p := ⟨rfl⟩
  have : Algebra.FormallyUnramified A (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.of_isLocalization p.primeCompl
  have : Algebra.IsUnramifiedAt (MvPolynomial (Fin n) K) p :=
    Algebra.FormallyUnramified.comp (MvPolynomial (Fin n) K) A (Localization.AtPrime p)
  have : Module.Finite (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField := inferInstance
  have : Algebra.IsAlgebraic (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField :=
    inferInstance
  have : Algebra.IsAlgebraic (MvPolynomial (Fin n) K) (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have : FaithfulSMul (MvPolynomial (Fin n) K) (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  have : IsScalarTower K (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField p.ResidueField := inferInstance
  have h1 := trdeg_add_eq K (MvPolynomial (Fin n) K) (A := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField)
  have h2 := trdeg_add_eq K (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField (A := p.ResidueField)
  rw [trdeg_eq_zero (R := MvPolynomial (Fin n) K) (A := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField), add_zero] at h1
  rw [trdeg_eq_zero (R := (⊥ : Ideal (MvPolynomial (Fin n) K)).ResidueField) (A := p.ResidueField), add_zero] at h2
  rw [← h2, ← h1, MvPolynomial.trdeg_of_isDomain]
  simp

end Formalism.L2.Pj.TranscendenceDegreeLemmas
end

section
namespace Formalism.L2.Pj.TranscendenceDegreeLemmas

open AlgebraicGeometry CategoryTheory

theorem primeIdealOf_mem_minimalPrimes {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hx : hZ.1.genericPoint ∈ V) :
    (hV.primeIdealOf ⟨_, hx⟩).asIdeal ∈ minimalPrimes Γ(X, V) := by
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen : IsGenericPoint hZ.1.genericPoint Z := by
    have := hZ.1.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  refine ⟨⟨(hV.primeIdealOf ⟨_, hx⟩).isPrime, bot_le⟩, fun q hq hle => ?_⟩
  let y : PrimeSpectrum Γ(X, V) := ⟨q, hq.1⟩
  have hsp : y ⤳ hV.primeIdealOf ⟨_, hx⟩ := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  have hsp' : hV.fromSpec y ⤳ hZ.1.genericPoint := by
    have := hsp.map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  have hirr : IsIrreducible (closure {hV.fromSpec y}) := isIrreducible_singleton.closure
  have hZle : Z ⊆ closure {hV.fromSpec y} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp')) isClosed_closure
  have heq : closure {hV.fromSpec y} = Z := (hZ.2 hirr hZle).antisymm hZle
  have hmem : hV.fromSpec y ∈ Z := heq ▸ subset_closure rfl
  have hxy : hV.fromSpec y = hZ.1.genericPoint := (hsp'.antisymm (hgen.specializes hmem)).eq
  have hy : y = hV.primeIdealOf ⟨_, hx⟩ :=
    hV.fromSpec.isOpenEmbedding.injective (hxy.trans (hV.fromSpec_primeIdealOf ⟨_, hx⟩).symm)
  have := congrArg PrimeSpectrum.asIdeal hy
  exact le_of_eq this.symm

theorem trdeg_residueField_genericPoint {K : Type} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    Algebra.trdeg K (X.residueField hZ.1.genericPoint) = n := by
  classical
  obtain ⟨U, hU, V, hV, hxV, e, hP⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) hZ.1.genericPoint
  have hUtop : U = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hfx : f hZ.1.genericPoint ∈ U := e hxV
    rwa [Subsingleton.elim y (f hZ.1.genericPoint)]
  subst hUtop
  let e0 : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(X, V) := (f.appLE ⊤ V e).hom.comp (e0 : K →+* _)
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) :=
    hP.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e0)
  have hmin := primeIdealOf_mem_minimalPrimes hV hZ hxV
  have hcore := trdeg_residueField_of_minimal (K := K) n (hV.primeIdealOf ⟨_, hxV⟩).asIdeal hmin
  let _ : Algebra Γ(X, V) (X.presheaf.stalk hZ.1.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hZ.1.genericPoint, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨hZ.1.genericPoint, hxV⟩
  let eL := IsLocalization.algEquiv (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal) (X.presheaf.stalk hZ.1.genericPoint)
  let eR : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField ≃+* X.residueField hZ.1.genericPoint :=
    IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv
  have hc1 : CharZero (X.residueField hZ.1.genericPoint) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have hc2 : CharZero (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have t1 : IsScalarTower ℚ K (X.residueField hZ.1.genericPoint) :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have t2 : IsScalarTower ℚ K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have a1 := trdeg_add_eq ℚ K (A := X.residueField hZ.1.genericPoint)
  have a2 := trdeg_add_eq ℚ K (A := (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField)
  have a3 := (eR.toRatAlgEquiv).trdeg_eq
  rw [trdeg_eq_zero (R := ℚ) (A := K), zero_add] at a1 a2
  rw [a1, ← a3, ← a2, hcore]

theorem fg_residueField_genericPoint {K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    (⊤ : IntermediateField K (X.residueField hZ.1.genericPoint)).FG := by
  classical
  obtain ⟨U, hU, V, hV, hxV, e, hP⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) hZ.1.genericPoint
  have hUtop : U = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hfx : f hZ.1.genericPoint ∈ U := e hxV
    rwa [Subsingleton.elim y (f hZ.1.genericPoint)]
  subst hUtop
  let e0 : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(X, V) := (f.appLE ⊤ V e).hom.comp (e0 : K →+* _)
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) :=
    hP.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e0)
  have hmin := primeIdealOf_mem_minimalPrimes hV hZ hxV
  let _ : Algebra Γ(X, V) (X.presheaf.stalk hZ.1.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hZ.1.genericPoint, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨hZ.1.genericPoint, hxV⟩
  let eL := IsLocalization.algEquiv (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal) (X.presheaf.stalk hZ.1.genericPoint)
  let eR : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField ≃+* X.residueField hZ.1.genericPoint :=
    IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv
  have hc1 : CharZero (X.residueField hZ.1.genericPoint) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have hc2 : CharZero (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have t1 : IsScalarTower ℚ K (X.residueField hZ.1.genericPoint) :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have t2 : IsScalarTower ℚ K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have f00 : Algebra.IsStandardSmooth K Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have f01 : Algebra.FinitePresentation K Γ(X, V) := inferInstance
  have f0 : Algebra.EssFiniteType K Γ(X, V) := inferInstance
  have f1 : Algebra.EssFiniteType K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp K Γ(X, V) _
  have f2 : Algebra.EssFiniteType ℚ K := inferInstance
  have f3 : Algebra.EssFiniteType ℚ (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp ℚ K _
  have f4 : Algebra.EssFiniteType ℚ (X.residueField hZ.1.genericPoint) :=
    (Algebra.EssFiniteType.iff_of_algEquiv eR.toRatAlgEquiv).1 f3
  have f5 : Algebra.EssFiniteType K (X.residueField hZ.1.genericPoint) := Algebra.EssFiniteType.of_comp ℚ K _
  exact IntermediateField.fg_top K _

end Formalism.L2.Pj.TranscendenceDegreeLemmas
end

section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

set_option backward.isDefEq.respectTransparency.types false in
instance smoothOfRelativeDimension_strK (Xo : Moduli Dw l) (c : Coeff l) :
    SmoothOfRelativeDimension Dw.dim (strK (Xo := Xo) (c := c)) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} Dw.dim
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension Dw.dim) _ _ Xo.smooth

theorem kapTrdeg_pf (Xo : Moduli Dw l) (c : Coeff l) : KapTrdeg Xo c Dw.dim := by
  intro Z
  have h := @TranscendenceDegreeLemmas.trdeg_residueField_genericPoint c.F _ _ _ _
    (strK (Xo := Xo) (c := c)) Dw.dim _ _ Z.2 (algKap Z)
  exact h

theorem kapFG_pf (Xo : Moduli Dw l) (c : Coeff l) : KapFG Xo c := by
  intro Z
  have h := @TranscendenceDegreeLemmas.fg_residueField_genericPoint c.F _ _ _ _
    (strK (Xo := Xo) (c := c)) Dw.dim _ _ Z.2 (algKap Z)
  exact h

end Formalism.L2.Pj

end
end
