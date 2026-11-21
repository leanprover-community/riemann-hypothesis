import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbelianPartExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalBaseChangeIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieSignature
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieSignatureNumberFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalHermitianFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHeightBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelValueLift
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactSphere
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianFiniteCoverTorus
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelPrimeQuotient
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverSquareZeroLift
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverOfAdicCompletion
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVRScheme
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModelStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CoordinateMapFiniteType
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationCompact
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationContinuous
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FiniteSurjectivePointLift
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsIntegralClosedSubscheme
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationCompare
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HermitianNormSquareFormula
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianBundleQuotientDegreeBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelRankEqGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianPullbackTorusExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpanStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChangeStatement

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.StratLie

open GlobalTheory.CompanionTheory.Ar.TorusModel

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem killed_of_eq {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {B : Type} [CommRing B] {b : Sp B ⟶ S}
    (h : KillsOver u Y b) {A : Type} [CommRing A] (g : B →+* A) {a : Sp A ⟶ S} (ha : a = spMap g ≫ b)
    (t : Over.mk a ⟶ splitTorus S X) (ht : ∀ y ∈ Y, charVal t y = 1) : t ≫ u = 1 := by
  subst ha
  exact h A g t ht

theorem killsOver_comp {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {B C : Type} [CommRing B] [CommRing C]
    (c : B →+* C) {b : Sp B ⟶ S} (h : KillsOver u Y b) : KillsOver u Y (spMap c ≫ b) := by
  intro A _ g t ht
  refine killed_of_eq h (g.comp c) ?_ t ht
  rw [← Category.assoc, spMap_comp_spMap]

theorem killsOver_descent [IsSeparated G.hom] {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {κ k : Type}
    [Field κ] [Field k] (c : κ →+* k) {b : Sp κ ⟶ S} (h : KillsOver u Y (spMap c ≫ b)) : KillsOver u Y b := by
  intro A _ g t ht
  letI := g.toAlgebra
  letI := c.toAlgebra
  let i : A →+* (A ⊗[κ] k) := Algebra.TensorProduct.includeLeftRingHom
  let j : k →+* (A ⊗[κ] k) := (Algebra.TensorProduct.includeRight : k →ₐ[κ] (A ⊗[κ] k)).toRingHom
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeLeft_injective (R := κ) (S := κ) (A := A) (B := k) c.injective
  have hij : i.comp g = j.comp c := by
    ext a
    change (algebraMap κ A a) ⊗ₜ[κ] (1 : k) = (1 : A) ⊗ₜ[κ] (algebraMap κ k a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hw : spMap i ≫ spMap g ≫ b = spMap j ≫ spMap c ≫ b := by
    simp only [← Category.assoc, spMap_comp_spMap, hij]
  let φ : Over.mk (spMap j ≫ spMap c ≫ b) ⟶ Over.mk (spMap g ≫ b) := Over.homMk (spMap i) hw
  have h1 := h _ j (φ ≫ t) (fun y hy => by rw [charVal_comp i t (φ ≫ t) rfl, ht y hy, map_one])
  have h2 : φ ≫ (t ≫ u) = φ ≫ 1 :=
    (Category.assoc _ _ _).symm.trans (h1.trans (MonObj.comp_one φ).symm)
  have := GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom i) hi
  refine Over.OverMorphism.ext (GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap i) ?_)
  · rw [Over.w, Over.w]
  · exact congr($(h2).left)

theorem false_of_killsOver {u : splitTorus S X ⟶ G} {K : Type} [Field K] (b : Sp K ⟶ S) {l : ℕ} (hl : l.Prime)
    (ψ : X →+ ZMod l) (hψ : Function.Surjective ψ) (hk : KillsOver u ψ.ker b)
    (hinj : ∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X),
      t ≫ u = 1 → t = 1) : False := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨t, ht⟩ := exists_charVal (X := X) (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ b)
    (MonoidHom.toHomUnits ((AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)))
  have ht' : ∀ χ, charVal t χ = AddMonoidAlgebra.single (ψ χ) 1 := ht
  have h1 := hk _ _ t fun y hy => by
    rw [ht', (AddMonoidHom.mem_ker).1 hy]; rfl
  have h2 := hinj _ _ t h1
  obtain ⟨χ, hχ⟩ := hψ 1
  have h3 := ht' χ
  rw [h2, charVal_one, AddMonoidAlgebra.one_def, hχ] at h3
  exact one_ne_zero (AddMonoidAlgebra.single_left_injective one_ne_zero h3).symm

theorem killsOver_of_residue [IsSeparated G.hom] {u : splitTorus S X ⟶ G} [IsMonHom u] {Y : AddSubgroup X}
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S)
    (h : KillsOver u Y (spMap (IsLocalRing.residue R) ≫ b)) : KillsOver u Y b := by
  refine GlobalTheory.T.killsOver_of_adic_completion S G X u Y R b fun n => ?_
  induction n with
  | zero =>
    let e : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.lift _ (Ideal.Quotient.mk _) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)
    have he : e.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _ := by
      ext a; rfl
    have := killsOver_comp e h
    rwa [← Category.assoc, spMap_comp_spMap, he] at this
  | succ n ih =>
    set m := IsLocalRing.maximalIdeal R with hm
    have hne : m ^ (n + 1 + 1) ≠ ⊤ := fun htop =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_eq_top_iff.1 htop |>.elim id (by simp))
    let q := Ideal.Quotient.mk (m ^ (n + 1 + 1))
    haveI : Nontrivial (R ⧸ m ^ (n + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (R ⧸ m ^ (n + 1 + 1)) :=
      IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
    let I : Ideal (R ⧸ m ^ (n + 1 + 1)) := (m ^ (n + 1)).map q
    have hI : I ^ 2 = ⊥ := by
      rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, ← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    refine GlobalTheory.T.killsOver_square_zero_lift S G X u Y _ (spMap q ≫ b) I hI ?_
    let e : R ⧸ m ^ (n + 1) →+* (R ⧸ m ^ (n + 1 + 1)) ⧸ I :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp q) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
    have he : e.comp (Ideal.Quotient.mk (m ^ (n + 1))) = (Ideal.Quotient.mk I).comp q := by
      ext a; rfl
    have := killsOver_comp e ih
    rw [← Category.assoc, spMap_comp_spMap, he, ← spMap_comp_spMap, Category.assoc] at this
    exact this

theorem lie_injective : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (G : Over Z) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus Z X ⟶ G) [IsMonHom u] (U : Z.Opens), (U : Set Z).Nonempty → (∀ (k : Type) [Field k] (x : Sp k ⟶ Z), ⊤ ≤ x ⁻¹ᵁ U → ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z X), t ≫ u = 1 → t = 1) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z) (M : LieModel (splitTorus Z X) x (X →+ k)), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  intro Z _ _ G _ _ X _ _ u _ U hU hinj k _ x M hM δ hδ
  by_contra hne
  obtain ⟨l, hl, ψ, hψ, hk⟩ := GlobalTheory.T.torus_kernel_prime_quotient Z G X u k x M hM δ hne hδ
  obtain ⟨z, f, hx⟩ : ∃ (z : Z) (f : Z.residueField z ⟶ CommRingCat.of k),
      x = Spec.map f ≫ Z.fromSpecResidueField z :=
    ⟨_, _, ((Scheme.SpecToEquivOfField k Z).symm_apply_apply x).symm⟩
  by_cases hz : z ∈ U
  · have hU' : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
      subst hx
      change (Z.fromSpecResidueField z) _ ∈ U
      rwa [Scheme.fromSpecResidueField_apply]
    exact false_of_killsOver x hl ψ hψ hk (hinj k x hU')
  have hgen : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  have hzg : z ≠ genericPoint Z := fun h => hz (h ▸ hgen)
  have hkκ : KillsOver u ψ.ker (Z.fromSpecResidueField z) :=
    killsOver_descent f.hom (hx ▸ hk)
  obtain ⟨V, hV, hA, hdom⟩ := GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.proof Z z hzg
  let jv : Z.presheaf.stalk z →+* V := (algebraMap (Z.presheaf.stalk z) Z.functionField).codRestrict V hA
  haveI : IsLocalHom jv := ⟨fun a ha => by
    by_contra hna
    exact ((hdom a).2 ((IsLocalRing.mem_maximalIdeal a).2 hna)) ha⟩
  let b : Sp V ⟶ Z := spMap jv ≫ Z.fromSpecStalk z
  let rm : IsLocalRing.ResidueField (Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V :=
    IsLocalRing.ResidueField.map jv
  have e1 : spMap rm ≫ Z.fromSpecResidueField z = spMap (IsLocalRing.residue V) ≫ b := by
    have e0 : spMap rm ≫ Spec.map (Z.residue z) = spMap (IsLocalRing.residue V) ≫ spMap jv := by
      rw [spMap_comp_spMap, ← IsLocalRing.ResidueField.map_comp_residue jv, ← spMap_comp_spMap]
      rfl
    simp only [b, Scheme.fromSpecResidueField]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Z.fromSpecStalk z) e0).trans (Category.assoc _ _ _))
  have kres : KillsOver u ψ.ker (spMap (IsLocalRing.residue V) ≫ b) := e1 ▸ killsOver_comp rm hkκ
  have kV := killsOver_of_residue b kres
  have kK := killsOver_comp V.subtype kV
  have hU'' : ⊤ ≤ (spMap V.subtype ≫ b) ⁻¹ᵁ U := by
    have e2 : spMap V.subtype ≫ b = Z.fromSpecStalk (genericPoint Z) := by
      simp only [b]
      rw [← Category.assoc, spMap_comp_spMap]
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Z).specializes trivial)
    intro p _
    change (spMap V.subtype ≫ b) p ∈ U
    rw [e2]
    have hp : (Z.fromSpecStalk (genericPoint Z)) p ∈ Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hp
    exact Specializes.mem_open hp U.isOpen hgen
  exact false_of_killsOver _ hl ψ hψ kK (hinj _ _ hU'')

end GlobalTheory.CompanionTheory.Ar.StratLie
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_injective_on_open : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (G : Over Z) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus Z X ⟶ G) [IsMonHom u] (U : Z.Opens), (U : Set Z).Nonempty → (∀ (k : Type) [Field k] (x : Sp k ⟶ Z), ⊤ ≤ x ⁻¹ᵁ U → ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z X), t ≫ u = 1 → t = 1) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z) (M : LieModel (splitTorus Z X) x (X →+ k)), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.StratLie.lie_injective
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem closure_finiteType_over_int : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) :=
  @PositivityTheory.Xgn.coordinate_map_finite_type

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_finite_type_over_integers : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem compact_of_finite_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (Z' : Scheme.{0}) (f : Z' ⟶ XQ X), IsFinite f →
    @CompactSpace (Sp ℂ ⟶ Z') (anTop Z') :=
  @PositivityTheory.Xgn.torus_uniformization_compact

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_points_finite_compact : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (Z' : Scheme.{0}) (f : Z' ⟶ XQ X), IsFinite f →
    @CompactSpace (Sp ℂ ⟶ Z') (anTop Z') := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TorusUnif.compact_of_finite_generic
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem gramAt_continuous_anTop : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Fin r → (Xc →+ ℤ)) (H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ),
    (∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v) →
    @Continuous _ _ (anTop Z') _ H :=
  @PositivityTheory.Xgn.torus_uniformization_continuous

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_continuous : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Fin r → (Xc →+ ℤ)) (H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ),
    (∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v) →
    @Continuous _ _ (anTop Z') _ H := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TorusUnif.gramAt_continuous_anTop
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos

theorem core_gram_posDef {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent ℂ v) :
    (Matrix.of fun a b => core.inner (v a) (v b)).PosDef := by
  let _ : NormedAddCommGroup V := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hp := Matrix.posDef_gram_of_linearIndependent (𝕜 := ℂ) hv
  have hG : (Matrix.gram ℂ v) = Matrix.of fun a b => core.inner (v a) (v b) := by
    ext i j
    rfl
  rw [hG] at hp
  exact hp

theorem cochar_indep {Xc : Type} [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] {r : ℕ}
    (β : Fin r → (Xc →+ ℤ)) (hβ : LinearIndependent ℤ β) :
    LinearIndependent ℂ (fun a => (Int.castAddHom ℂ).comp (β a)) := by
  let b := Module.Free.chooseBasis ℤ Xc
  let ev : (Xc →+ ℤ) →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ Xc → ℤ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    have : f.toIntLinearMap = 0 := b.ext fun i => congrFun hf i
    ext x
    exact LinearMap.congr_fun this x
  have h1 : LinearIndependent ℤ (ev ∘ β) := hβ.map' ev hev
  have h2 : LinearIndependent ℂ (fun a => algebraMap ℤ ℂ ∘ (ev ∘ β) a) :=
    linearIndependent_algebraMap_comp_iff.2 h1
  let evC : (Xc →+ ℂ) →ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ Xc → ℂ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp evC h2

theorem exists_diff {S : Scheme.{0}} {T G : Over S} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u]
    {R : Type} [CommRing R] {x : Sp R ⟶ S} {E F : Type} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (M : LieModel T x E) (N : LieModel G x F) : ∃ A : E →ₗ[R] F, ∀ e, N.pt (A e) = M.pt e ≫ u := by
  have ht : ∀ e, IsTanAt G x (M.pt e ≫ u) := by
    intro e
    have h1 := (LieEx.isTanAt_iff x T _).1 (M.tan e)
    refine (LieEx.isTanAt_iff x G _).2 ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (h1 =≫ u).trans ?_
    exact MonObj.one_comp u
  choose A hA using fun e => N.onto _ (ht e)
  refine ⟨{ toFun := A, map_add' := fun e e' => N.inj ?_, map_smul' := fun c e => N.inj ?_ }, hA⟩
  · rw [N.add, hA, hA, hA, M.add, MonObj.mul_comp]
  · apply Over.OverMorphism.ext
    rw [N.smul, hA, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc]

theorem gramAt_posDef_of_diff_injective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
    (∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) → ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → (RootHt.gramAt h (zc ≫ ρ) v).PosDef := by
  intro X Ω _ K J y ξ G _ _ Li _ _ M h Z' ρ G' _ Φ hΦ Xc _ _ _ u _ r β zc Mz _ hker v hv
  obtain ⟨V, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ (zc ≫ ρ)
  obtain ⟨A, hA⟩ := exists_diff u Mz (LiePull.modelPull hΦ zc MR)
  have hA' : ∀ δ, (MR.pt (A δ)).left = (Mz.pt δ ≫ u).left ≫ Φ := by
    intro δ
    rw [← hA, ← LiePull.pts_left hΦ (LiePull.eps_assoc zc)]
    exact congrArg (fun k => k.left) ((LiePull.tanPts hΦ zc).apply_symm_apply (MR.pt (A δ))).symm
  have hk : LinearMap.ker A = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro δ hδ
    apply hker
    rw [← hA, hδ]
    have := (LiePull.modelPull hΦ zc MR).add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hli := (cochar_indep β β.linearIndependent).map' A hk
  obtain ⟨core, hcore⟩ := h.herm (zc ≫ ρ) V MR
  have key := core_gram_posDef core _ hli
  have hv' : ∀ a, v a = MR.pt (A ((Int.castAddHom ℂ).comp (β a))) := fun a =>
    Over.OverMorphism.ext ((hv a).trans (hA' _).symm)
  have hm : RootHt.gramAt h (zc ≫ ρ) v = Matrix.of fun a b =>
      core.inner ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) a) ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) b) := by
    ext a c
    simp only [RootHt.gramAt, Matrix.of_apply, hcore, hv', Function.comp_apply]
  rw [hm]
  exact key

end GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_metric_torus_pullback : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
    (∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) → ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → (RootHt.gramAt h (zc ≫ ρ) v).PosDef := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos.gramAt_posDef_of_diff_injective
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem exists_lift_algClosure : ∀ (Z' Z : Scheme.{0}) (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ (L : Type) [Field L] (zZ : Sp L ⟶ Z),
    ∃ x : Sp (AlgebraicClosure L) ⟶ Z', x ≫ π = spMap (algebraMap L (AlgebraicClosure L)) ≫ zZ :=
  PositivityTheory.Xgn.finite_surjective_point_lift

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_surjective_lifts_points : ∀ (Z' Z : Scheme.{0}) (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ (L : Type) [Field L] (zZ : Sp L ⟶ Z),
    ∃ x : Sp (AlgebraicClosure L) ⟶ Z', x ≫ π = spMap (algebraMap L (AlgebraicClosure L)) ≫ zZ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_lift_algClosure
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem exists_integral_closed_subscheme : ∀ (S : Scheme.{0}) (F : Set S), IsClosed F → IsIrreducible F →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ S), IsClosedImmersion i ∧ Set.range i = F ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S), x (IsLocalRing.closedPoint k) ∈ F → ∃ x' : Sp k ⟶ Z, x' ≫ i = x :=
  PositivityTheory.Xgn.exists_integral_closed_subscheme_of_irreducible

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_closed_integral_subscheme : ∀ (S : Scheme.{0}) (F : Set S), IsClosed F → IsIrreducible F →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ S), IsClosedImmersion i ∧ Set.range i = F ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S), x (IsLocalRing.closedPoint k) ∈ F → ∃ x' : Sp k ⟶ Z, x' ≫ i = x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_integral_closed_subscheme
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem torus_stratum_cocharacters_compare : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  exact @PositivityTheory.Xgn.torus_uniformization_compare

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_split_pullback_generic : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem sqAt_sum_eq_gram : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (ε : Fin n → B.carrier) (Γ : Matrix (Fin n) (Fin n) ℂ),
    (∀ a b, Γ a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)) → ∀ w : Fin n → ℂ,
    sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) = (star w ⬝ᵥ (Γ *ᵥ w)).re :=
  @PositivityTheory.Xgn.hermitian_norm_square_formula

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_square_norm_gram : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (ε : Fin n → B.carrier) (Γ : Matrix (Fin n) (Fin n) ℂ),
    (∀ a b, Γ a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)) → ∀ w : Fin n → ℂ,
    sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) = (star w ⬝ᵥ (Γ *ᵥ w)).re := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TorusUnif.sqAt_sum_eq_gram
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem noeth_good {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] (Good : ℝ → T → Prop)
    (mono : ∀ C C' t, C ≤ C' → Good C t → Good C' t)
    (step : ∀ F : Set T, IsClosed F → IsIrreducible F → ∃ F' : Set T, IsClosed F' ∧ F' ⊂ F ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ F, t ∉ F' → Good C t) : ∃ C : ℝ, 1 ≤ C ∧ ∀ t, Good C t := by
  have key : ∀ F : TopologicalSpace.Closeds T, ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ F, Good C t := by
    intro F
    induction F using WellFoundedLT.induction with
    | ind F ih =>
      by_cases hF : IsIrreducible (F : Set T)
      · obtain ⟨F', hc, hlt, C, hC, hg⟩ := step F F.isClosed hF
        obtain ⟨C', hC', hg'⟩ := ih ⟨F', hc⟩ (by
          exact lt_of_le_of_ne (fun x hx => hlt.1 hx) (fun e => hlt.2 (by rw [← e]; exact fun x hx => hx)))
        refine ⟨max C C', le_max_of_le_left hC, fun t ht => ?_⟩
        by_cases h' : t ∈ F'
        · exact mono _ _ _ (le_max_right _ _) (hg' t h')
        · exact mono _ _ _ (le_max_left _ _) (hg t ht h')
      · obtain ⟨S, hS, hirr, hsup⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible F
        have hlt : ∀ s ∈ S, s < F := fun s hs => by
          refine lt_of_le_of_ne (hsup ▸ le_sSup hs) (fun e => hF ?_)
          rw [← e]; exact hirr s hs
        choose! c hc hg using fun s (hs : s ∈ S) => ih s (hlt s hs)
        refine ⟨∑ s ∈ hS.toFinset, c s + 1, ?_, fun t ht => ?_⟩
        · have : 0 ≤ ∑ s ∈ hS.toFinset, c s :=
            Finset.sum_nonneg fun s hs => by linarith [hc s (hS.mem_toFinset.1 hs)]
          linarith
        · have ht' : t ∈ (sSup S : TopologicalSpace.Closeds T) := hsup ▸ ht
          have hsS : ∃ s ∈ S, t ∈ s := by
            have aux : ∀ A : Finset (TopologicalSpace.Closeds T), t ∈ A.sup id → ∃ s ∈ A, t ∈ s := by
              classical
              intro A
              induction A using Finset.induction_on with
              | empty =>
                intro h
                have h' : t ∈ ((⊥ : TopologicalSpace.Closeds T) : Set T) := h
                simp at h'
              | insert a A _ ih' =>
                intro h
                rw [Finset.sup_insert] at h
                have h' : t ∈ ((id a ⊔ A.sup id : TopologicalSpace.Closeds T) : Set T) := h
                rw [TopologicalSpace.Closeds.coe_sup] at h'
                rcases h' with h' | h'
                · exact ⟨a, Finset.mem_insert_self _ _, h'⟩
                · obtain ⟨s, hs, hts⟩ := ih' h'
                  exact ⟨s, Finset.mem_insert_of_mem hs, hts⟩
            have hfin : (sSup S : TopologicalSpace.Closeds T) = hS.toFinset.sup id := by
              rw [Finset.sup_id_eq_sSup, hS.coe_toFinset]
            rw [hfin] at ht'
            obtain ⟨s, hs, hts⟩ := aux _ ht'
            exact ⟨s, hS.mem_toFinset.1 hs, hts⟩
          obtain ⟨s, hs, hts⟩ := hsS
          refine mono _ _ _ ?_ (hg s hs t hts)
          have : c s ≤ ∑ s ∈ hS.toFinset, c s :=
            Finset.single_le_sum (f := c) (fun s hs => by linarith [hc s (hS.mem_toFinset.1 hs)]) (hS.mem_toFinset.2 hs)
          linarith
  obtain ⟨C, hC, h⟩ := key ⊤
  exact ⟨C, hC, fun t => h t trivial⟩

theorem isGrpPullback_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
    {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : G''.left ⟶ G'.left} (h : IsGrpPullback G' G f φ)
    (h' : IsGrpPullback G'' G' g ψ) : IsGrpPullback G'' G (g ≫ f) (ψ ≫ φ) := by
  refine ⟨h'.1.paste_horiz h.1, fun T x y x₀ y₀ hx hy => ?_⟩
  have key : ∀ (c : T.left ⟶ S) (_ : (T.hom ≫ g) ≫ f = c) (x₀ y₀ : Over.mk c ⟶ G), x₀.left = x.left ≫ ψ ≫ φ →
      y₀.left = y.left ≫ ψ ≫ φ → (x₀ * y₀).left = (x * y).left ≫ ψ ≫ φ := by
    rintro _ rfl x₀ y₀ hx hy
    let x₁ : Over.mk (T.hom ≫ g) ⟶ G' := Over.homMk (x.left ≫ ψ) (by
      have := h'.1.w
      simp only [Over.mk_hom, Category.assoc, this, Over.w_assoc, Over.w])
    let y₁ : Over.mk (T.hom ≫ g) ⟶ G' := Over.homMk (y.left ≫ ψ) (by
      have := h'.1.w
      simp only [Over.mk_hom, Category.assoc, this, Over.w_assoc, Over.w])
    have e₁ := h'.2 T x y x₁ y₁ rfl rfl
    have e₂ := h.2 (Over.mk (T.hom ≫ g)) x₁ y₁ x₀ y₀ (by simpa [x₁] using hx) (by simpa [y₁] using hy)
    rw [e₂, e₁]
    exact CategoryTheory.Category.assoc _ _ _
  exact key _ (Category.assoc _ _ _) x₀ y₀ hx hy

theorem dual_inl {A B : Type} [CommRing A] [CommRing B] (σ : A →+* B) (a : A) :
    dualMap σ (algebraMap A (DualNumber A) a) = algebraMap B (DualNumber B) (σ a) := by
  show dualMap σ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (σ a)
  apply TrivSqZeroExt.ext <;> simp [dualMap]

def dualEquiv {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) : (B →+ ℤ) ≃ₗ[ℤ] (A →+ ℤ) :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun g => g.comp e.toAddMonoidHom
      invFun := fun g => g.comp e.symm.toAddMonoidHom
      left_inv := fun g => by ext x; simp
      right_inv := fun g => by ext x; simp
      map_add' := fun g g' => by ext x; simp }

theorem exists_dual_basis (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r) ℤ (Xc →+ ℤ)) :=
  ⟨_, ⟨(Module.finBasis ℤ Xc).dualBasis.map (addMonoidHomLequivInt ℤ).symm⟩⟩

end GlobalTheory.CompanionTheory.Ar.TorusUnif

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

open scoped ComplexOrder in

theorem gram_bound (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (hall : ∀ q : X, genPt ξ ⤳ q)
    (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (f : Z' ⟶ XQ X) (hf : IsFinite f) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left)
    (hP : IsGrpPullback G' G (f ≫ XQ.fst X) Φ)
    (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u]
    (hinj : ∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) (r : ℕ) (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (zc : Sp ℂ ⟶ Z') (zX : Sp ℂ ⟶ X) (_ : zc ≫ f ≫ XQ.fst X = zX)
      (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz → ∀ v : Fin r → (epsAt zX ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → ∀ w : Fin r → ℂ,
        C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ (star w ⬝ᵥ (RootHt.gramAt h zX v *ᵥ w)).re ∧
        (star w ⬝ᵥ (RootHt.gramAt h zX v *ᵥ w)).re ≤ C * ∑ a, ‖w a‖ ^ 2 := by
  set ρ : Z' ⟶ X := f ≫ XQ.fst X with hρ
  have hM : ∀ zc : Sp ℂ ⟶ Z', ∃ Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ), IsCocharLie Mz :=
    fun zc => GlobalTheory.T.exists_cocharacter_lie_model Z' Xc ℂ zc
  choose Mz hMz using hM
  have hv : ∀ (zc : Sp ℂ ⟶ Z') (Mz' : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)) (a : Fin r),
      ∃ v : epsAt (zc ≫ ρ) ⟶ G, v.left = (Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ := by
    intro zc Mz' a
    refine ⟨Over.homMk ((Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) ?_, rfl⟩
    have w1 : Φ ≫ G.hom = G'.hom ≫ ρ := hP.1.w
    have w2 := Over.w (Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u)
    rw [CategoryTheory.Category.assoc, w1, reassoc_of% w2]
    simp [epsAt]
  choose vv hvv using fun zc => hv zc (Mz zc)
  let H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ := fun zc => RootHt.gramAt h (zc ≫ ρ) (vv zc)
  have hH : ∀ (zc : Sp ℂ ⟶ Z') (Mz' : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz' →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v := by
    intro zc Mz' hMz' v hv'
    have e : ∀ d, Mz'.pt d = (Mz zc).pt d := fun d =>
      (GlobalTheory.T.charVal_multiplicative Z' Xc (DualNumber ℂ) _).1 _ _ (fun χ => by rw [hMz', hMz])
    have : vv zc = v := by
      funext a
      apply Over.OverMorphism.ext
      rw [hvv, hv', e]
    simp only [H, this]
  have hcont := GlobalTheory.T.gram_matrix_continuous X Ω K J y ξ hall hT G Li M h Z' ρ G' Φ hP Xc u r (fun a => β a) H hH
  letI := anTop Z'
  haveI := GlobalTheory.T.analytic_points_finite_compact X Ω K J y ξ hall hT Z' f hf
  obtain ⟨C, hC, hb⟩ := GlobalTheory.CompanionTheory.GramCompact.exists_bounds (Sp ℂ ⟶ Z') Set.univ (Fin r) H isCompact_univ
    hcont.continuousOn (fun zc _ => GlobalTheory.T.lie_metric_torus_pullback X Ω K J y ξ G Li M h Z' ρ G' Φ hP Xc u r β zc (Mz zc) (hMz zc)
      (hinj zc _ (hMz zc)) (vv zc) (hvv zc))
  refine ⟨C, hC, fun zc zX hz Mz' hMz' v hv' w => ?_⟩
  subst hz
  rw [← hH zc Mz' hMz' v hv']
  exact hb zc trivial w

theorem xq_facts (X : Scheme.{0}) (h : LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X)) :
    LocallyOfFiniteType (XQ.snd X) ∧ QuasiCompact (XQ.snd X) ∧ IsLocallyNoetherian (XQ X) ∧
      TopologicalSpace.NoetherianSpace (XQ X) := by
  obtain ⟨h1, h2⟩ := h
  have a1 : LocallyOfFiniteType (XQ.snd X) := inferInstance
  have a2 : QuasiCompact (XQ.snd X) := inferInstance
  have a3 : IsLocallyNoetherian (XQ X) := LocallyOfFiniteType.isLocallyNoetherian (XQ.snd X)
  have a4 : CompactSpace (XQ X) := QuasiCompact.compactSpace_of_compactSpace (XQ.snd X)
  have a5 : IsNoetherian (XQ X) := {}
  exact ⟨a1, a2, a3, inferInstance⟩

end GlobalTheory.CompanionTheory.Ar.TorusUnif

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

open scoped CategoryTheory.Obj

theorem stratum_good : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ XQ X), IsClosedImmersion i →
    ∃ (U : Z.Opens) (C : ℝ), (U : Set Z).Nonempty ∧ 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X)
      (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK),
      IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → ∀ zZ : Sp L ⟶ Z,
      zZ ≫ i = toXQ (spMap (algebraMap (𝓞 L) L) ≫ z) → ⊤ ≤ zZ ⁻¹ᵁ U → GoodAt h C z φ τ := by
  intro hFC X Ω _ K _ J _ y ξ hall hT G _ _ hG Li _ _ M h Z _ i hi
  have hfin := GlobalTheory.T.coords_finite_type_over_integers X Ω K J y ξ hall hT
  obtain ⟨hq1, hq2, hq3, hq4⟩ := xq_facts X hfin
  haveI := hG.smooth
  haveI := hG.separated
  let s : Z ⟶ Sp ℚ := i ≫ XQ.snd X
  haveI : LocallyOfFiniteType s := inferInstance
  haveI : QuasiCompact s := inferInstance
  let io : Z ⟶ X := i ≫ XQ.fst X
  have hGZ : IsSemiAbelian ((Over.pullback io).obj G) := IsSemiAbelian.pullback io G hG
  obtain ⟨Z', hZ', π, G', hG', φ', Xc, _, _, _, u, U, hπf, hπs, hnorm, hpb, hu, hU, hpt⟩ :=
    GlobalTheory.T.semiabelian_finite_cover_torus hFC Z s ((Over.pullback io).obj G) hGZ
  let f : Z' ⟶ XQ X := π ≫ i
  haveI hff : IsFinite f := inferInstance
  have hP : IsGrpPullback G' G (f ≫ XQ.fst X) (φ' ≫ pullback.fst G.hom io) := by
    have := isGrpPullback_comp (isGrpPullback_pullback G io) hpb
    simpa [f, io, CategoryTheory.Category.assoc] using this
  haveI : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsSeparated G'.hom := by
    have h1 : IsSeparated ((Over.pullback io).obj G).hom := (IsSemiAbelian.separated (G := (Over.pullback io).obj G))
    exact MorphismProperty.of_isPullback (P := @IsSeparated) hpb.1 h1
  obtain ⟨r, ⟨β⟩⟩ := exists_dual_basis Xc
  have hU' : ((π ⁻¹ᵁ U : Z'.Opens) : Set Z').Nonempty := by
    obtain ⟨p, hp⟩ := hU
    obtain ⟨q, rfl⟩ := hπs.surj p
    exact ⟨q, hp⟩
  have hinj0 := GlobalTheory.T.torus_injective_on_open Z' G' Xc u (π ⁻¹ᵁ U) hU' (fun k _ x hx A _ g t ht => (hpt k x hx).1 A g t ht)
  obtain ⟨C, hC, hb⟩ := gram_bound X Ω K J y ξ hall hT G Li M h Z' f hff G' _ hP Xc u
    (fun zc Mz hMz δ hδ => hinj0 ℂ zc Mz hMz δ hδ) r β
  refine ⟨U, C, hU, hC, ?_⟩
  intro L _ _ z GK _ φ τ hGK zZ hzZ hzU
  letI := τ.addCommGroup
  let Lb := AlgebraicClosure L
  obtain ⟨x, hx⟩ := GlobalTheory.T.finite_surjective_lifts_points Z' Z π hπf hπs L zZ
  have hxρ : x ≫ f ≫ XQ.fst X = spMap (algebraMap L Lb) ≫ (spMap (algebraMap (𝓞 L) L) ≫ z) := by
    have e : zZ ≫ i ≫ XQ.fst X = spMap (algebraMap (𝓞 L) L) ≫ z := by
      rw [← CategoryTheory.Category.assoc, hzZ, toXQ_fst]
    simp only [f, CategoryTheory.Category.assoc]
    rw [reassoc_of% hx, e]
  have hxU : ⊤ ≤ (x ≫ π) ⁻¹ᵁ U := by
    rw [hx]
    intro p _
    have h1 : spMap (algebraMap L (AlgebraicClosure L)) p ∈ zZ ⁻¹ᵁ U := hzU (TopologicalSpace.Opens.mem_top _)
    simpa using h1
  obtain ⟨hi1, hi2⟩ := hpt Lb x hxU
  obtain ⟨e, he⟩ := GlobalTheory.T.torus_split_pullback_generic X Z' G G' (f ≫ XQ.fst X) _ hP Xc u L Lb x _ hxρ GK φ hGK τ hi1 hi2
  refine ⟨r, β.map (dualEquiv e), fun MT hMT B MB hF ε hε σ w => ?_⟩
  letI : Algebra L ℂ := σ.toAlgebra
  let σ' : Lb →+* ℂ := (IsAlgClosed.lift : Lb →ₐ[L] ℂ).toRingHom
  have hσ' : σ'.comp (algebraMap L Lb) = σ := by
    ext a
    exact (IsAlgClosed.lift : Lb →ₐ[L] ℂ).commutes a
  let zc : Sp ℂ ⟶ Z' := spMap σ' ≫ x
  let c : 𝓞 L →+* ℂ := σ.comp (algebraMap (𝓞 L) L)
  let zX : Sp ℂ ⟶ X := spMap c ≫ z
  have hzX : zc ≫ f ≫ XQ.fst X = zX := by
    have e1 : spMap σ' ≫ spMap (algebraMap L Lb) ≫ spMap (algebraMap (𝓞 L) L) = spMap c := by
      rw [LieTangent.spec_comp, LieTangent.spec_comp]
      simp only [c, ← RingHom.comp_assoc, hσ']
    show (spMap σ' ≫ x) ≫ f ≫ XQ.fst X = spMap c ≫ z
    rw [CategoryTheory.Category.assoc, hxρ, ← e1]
    simp only [CategoryTheory.Category.assoc]
  obtain ⟨Mz, hMz⟩ := GlobalTheory.T.exists_cocharacter_lie_model Z' Xc ℂ zc
  let v : Fin r → (epsAt zX ⟶ G) := fun a => LieTangent.epsBase c rfl ≫ MB.pt (ε a)
  have hv : ∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ (φ' ≫ pullback.fst G.hom io) := by
    intro a
    set δ' : τ.X →+ L := (Int.castAddHom L).comp ((β.map (dualEquiv e)) a) with hδ'
    let a0 : Sp (DualNumber L) ⟶ Sp L := (epsAt (𝟙 (Sp L))).hom
    let g1 : DualNumber L →+* DualNumber ℂ := dualMap σ
    let t' : Over.mk (spMap g1 ≫ a0) ⟶ splitTorus (Sp L) τ.X :=
      Over.homMk (spMap g1 ≫ (MT.pt δ').left) (by
        have := Over.w (MT.pt δ')
        simp only [Over.mk_hom, CategoryTheory.Category.assoc] at this ⊢
        rw [this]
        rfl)
    have hchar : ∀ χ, charVal t' χ = charVal (Mz.pt ((Int.castAddHom ℂ).comp (β a))) (e χ) := by
      intro χ
      have e1 := (GlobalTheory.T.charVal_multiplicative (Sp L) τ.X (DualNumber L) a0).2.2.2.2.2 (DualNumber ℂ) g1 (MT.pt δ') t' rfl χ
      rw [e1, hMT, hMz]
      simp only [g1, hδ']
      ext <;> simp [dualMap, dualEquiv]
    have e2 := he (DualNumber ℂ) ((algebraMap ℂ (DualNumber ℂ)).comp σ') (epsAt zc).hom (by
        show _ = Spec.map _ ≫ spMap σ' ≫ x
        rw [← CategoryTheory.Category.assoc, LieTangent.spec_comp]) (spMap g1 ≫ a0) (by
        show _ = spMap g1 ≫ Spec.map (CommRingCat.ofHom (algebraMap L (DualNumber L))) ≫ 𝟙 _
        rw [CategoryTheory.Category.comp_id, LieTangent.spec_comp]
        have e0 : ((algebraMap ℂ (DualNumber ℂ)).comp σ').comp (algebraMap L Lb) = g1.comp (algebraMap L (DualNumber L)) := by
          refine RingHom.ext fun a => ?_
          show algebraMap ℂ (DualNumber ℂ) (σ' (algebraMap L Lb a)) = dualMap σ (algebraMap L (DualNumber L) a)
          rw [dual_inl]
          exact congrArg (algebraMap ℂ (DualNumber ℂ)) (congrArg (fun q => q a) hσ')
        rw [e0]) (Mz.pt ((Int.castAddHom ℂ).comp (β a))) t' hchar
    refine Eq.trans ?_ e2.symm
    have e3 := hε a
    unfold LieModel.Lifts at e3
    have e4 : (v a).left = spMap (dualMap c) ≫ (MB.pt (ε a)).left :=
      (LieTangent.left_eq_iff _ _ _ _).2 rfl
    rw [e4]
    have e5 : spMap (dualMap c) = spMap g1 ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := by
      rw [LieTangent.spec_comp, ← RootHt.dualMap_comp]
    rw [e5, CategoryTheory.Category.assoc, ← e3, Over.comp_left]
    show _ = ((spMap g1 ≫ (MT.pt δ').left) ≫ τ.i.left) ≫ φ
    simp only [CategoryTheory.Category.assoc, Over.comp_left]
    rfl
  obtain ⟨hlo, hhi⟩ := hb zc zX hzX Mz hMz v hv w
  have hΓ : ∀ a b, RootHt.gramAt h zX v a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b) := by
    intro a b
    exact (hF σ (ε a) (ε b) (v a) (v b) rfl rfl).symm
  rw [GlobalTheory.T.hermitian_square_norm_gram L B σ r ε _ hΓ w]
  exact ⟨hlo, hhi⟩

end GlobalTheory.CompanionTheory.Ar.TorusUnif

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

open scoped CategoryTheory.Obj

theorem goodAt_mono {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel G ξ Li} (h : LieMetric M y) {C C' : ℝ} (hC : 1 ≤ C) (hCC : C ≤ C') {L : Type} [Field L] [NumberField L]
    {z : Sp (𝓞 L) ⟶ X} {GK : Over (Sp L)} [GrpObj GK] {φ : GK.left ⟶ G.left} {τ : TorusExtension GK}
    (hg : GoodAt h C z φ τ) : GoodAt h C' z φ τ := by
  letI := τ.addCommGroup
  obtain ⟨r, bs, hb⟩ := hg
  refine ⟨r, bs, fun MT hMT B MB hF ε hε σ w => ?_⟩
  obtain ⟨h1, h2⟩ := hb MT hMT B MB hF ε hε σ w
  have hS : 0 ≤ ∑ a, ‖w a‖ ^ 2 := by positivity
  have hC0 : 0 < C := by linarith
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hC0 hCC) hS) h1, le_trans h2 (mul_le_mul_of_nonneg_right hCC hS)⟩

theorem torus_unif : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y), ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK), letI := τ.addCommGroup; IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier, (∀ a, MB.Lifts (algebraMap (𝓞 L) L) φ (ε a) (MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i)) → ∀ (σ : L →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2 := by
  intro hFC X Ω _ K _ J _ y ξ hc hall hT G _ _ hG Li _ _ M h
  obtain ⟨hq1, hq2, hq3, hq4⟩ := xq_facts X (GlobalTheory.T.coords_finite_type_over_integers X Ω K J y ξ hall hT)
  let Good : ℝ → XQ X → Prop := fun C t => 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X)
      (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK),
      IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ →
      toXQ (spMap (algebraMap (𝓞 L) L) ≫ z) (IsLocalRing.closedPoint L) = t → GoodAt h C z φ τ
  have key := noeth_good (T := XQ X) Good (fun C C' t hCC hg => ⟨hg.1.trans hCC, fun L _ _ z GK _ φ τ hP ht =>
    goodAt_mono h hg.1 hCC (hg.2 L z GK φ τ hP ht)⟩) ?_
  · obtain ⟨C, hC, hg⟩ := key
    exact ⟨C, hC, fun L _ _ z GK _ φ τ hP => (hg _).2 L z GK φ τ hP rfl⟩
  · intro F hF hFi
    obtain ⟨Z, hZ, i, hi, hr, hlift⟩ := GlobalTheory.T.irreducible_closed_integral_subscheme (XQ X) F hF hFi
    obtain ⟨U, C, hU, hC, hgood⟩ := stratum_good hFC X Ω K J y ξ hall hT G hG Li M h Z i hi
    refine ⟨i '' (U : Set Z)ᶜ, hi.base_closed.isClosedMap _ U.isOpen.isClosed_compl, ?_, C, hC, fun t ht hnt => ?_⟩
    · have hsub : i '' (U : Set Z)ᶜ ⊆ F := by
        rintro _ ⟨p, -, rfl⟩
        exact hr ▸ Set.mem_range_self p
      refine ⟨hsub, fun hne => ?_⟩
      obtain ⟨p, hp⟩ := hU
      have hpF : i p ∈ F := hr ▸ Set.mem_range_self p
      obtain ⟨q, hq, hqp⟩ := hne hpF
      exact hq (hi.base_closed.injective hqp ▸ hp)
    · refine ⟨hC, fun L _ _ z GK _ φ τ hP ht' => ?_⟩
      obtain ⟨x', hx'⟩ := hlift L (toXQ (spMap (algebraMap (𝓞 L) L) ≫ z)) (ht' ▸ ht)
      refine hgood L z GK φ τ hP x' hx' ?_
      intro p _
      have hpc : p = IsLocalRing.closedPoint L := Subsingleton.elim _ _
      subst hpc
      by_contra hn
      refine hnt ⟨x' (IsLocalRing.closedPoint L), hn, ?_⟩
      rw [← ht', ← hx']
      rfl

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_lie_metric_height : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y), ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK), letI := τ.addCommGroup; IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier, (∀ a, MB.Lifts (algebraMap (𝓞 L) L) φ (ε a) (MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i)) → ∀ (σ : L →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_unif
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_rank_eq_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V), Module.finrank (𝓞 L) V = Module.finrank Ω Li := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq | exact GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanCompare

theorem grp_mul {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (a : T ⟶ S') (b : T ⟶ S) (hb : b = a ≫ f)
    (x y : Over.mk a ⟶ G') (x₀ y₀ : Over.mk b ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hb
  exact h.2 (Over.mk a) x y x₀ y₀ hx hy

theorem exists_lift {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} (a : T ⟶ S') (w : T ⟶ G.left) (hw : w ≫ G.hom = a ≫ f) :
    ∃ v : Over.mk a ⟶ G', v.left ≫ φ = w :=
  ⟨Over.homMk (h.lift w a hw) (by simp), by simp⟩

theorem lift_unique {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {a : T ⟶ S'} (v v' : Over.mk a ⟶ G')
    (e : v.left ≫ φ = v'.left ≫ φ) : v = v' :=
  Over.OverMorphism.ext (h.hom_ext e (by rw [Over.w, Over.w]))

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun a => ?_
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [LieTangent.dualMap_fst, LieTangent.dualMap_snd]

def scale {S : Scheme.{0}} {Y : Over S} (a : Sp ℂ ⟶ S) (c : ℂ) (v : epsAt a ⟶ Y) : epsAt a ⟶ Y :=
  Over.homMk (spMap (epsMul c) ≫ v.left) (by
    have h := Over.w v
    simp only [Over.mk_left, Over.mk_hom, Category.assoc] at h ⊢
    rw [h, ← Category.assoc, LieTangent.spec_eps_alg])

@[simp] theorem scale_left {S : Scheme.{0}} {Y : Over S} (a : Sp ℂ ⟶ S) (c : ℂ) (v : epsAt a ⟶ Y) :
    (scale a c v).left = spMap (epsMul c) ≫ v.left := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem abPart_mul {S : Scheme.{0}} {t : SAB H S} {K : Type} [Field K] {z : Sp K ⟶ S} (P : AbPart t z) {T : Over (Sp K)}
    (x y : T ⟶ P.tK.G) :
    (x * y) ≫ P.τ.q ≫ P.e.hom = (x ≫ P.τ.q ≫ P.e.hom) * (y ≫ P.τ.q ≫ P.e.hom) := by
  letI := P.τ.grpB
  haveI := P.τ.q_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  rw [← Category.assoc, mul_comp, mul_comp, Category.assoc, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.TanCompare

namespace GlobalTheory.CompanionTheory.Ar.TanCompare

theorem tan_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (V₁ V₂ : Type) [AddCommGroup V₁] [Module (𝓞 L) V₁] [AddCommGroup V₂] [Module (𝓞 L) V₂] (MB : LieModel t.G z V₁) (MB' : LieModel t'.G (𝟙 _) V₂) (f : V₁ →ₗ[𝓞 L] V₂) (hf : ∀ (e : V₁) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), MB.Lifts (algebraMap (𝓞 L) L) P₂.m.φ e v → MB'.Lifts (algebraMap (𝓞 L) L) (P₂.e.hom.left ≫ w ≫ m'.φ) (f e) (v ≫ P₂.τ.q)) (σ : L →+* ℂ) (Pσ : AbPart t (spMap (σ.comp e₂) ≫ z₁)) (mKσ : SABMap Pσ.tK P₁.tK (spMap (σ.comp e₂))) (mBσ : SABMap Pσ.tB P₁.tB (spMap (σ.comp e₂))) (d1 : mKσ.φ ≫ P₁.m.φ = Pσ.m.φ) (d2 : mKσ.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ) (Mσ : LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V₁)) (hMσ : ∀ e : V₁, MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 t.G.left) e (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))) (Mσ' : LieModel t'.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (GroundTheory.Heights₂.Heights.Fibre σ V₂)) (hMσ' : ∀ e : V₂, MB'.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 t'.G.left) e (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))) (x : GroundTheory.Heights₂.Heights.Fibre σ V₁) (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G), v.left ≫ Pσ.m.φ = (Mσ.pt x).left → u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left → u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
  intro E _ _ _ H X t L₁ L _ _ _ e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' V₁ V₂ _ _ _ _ MB MB' f hf σ Pσ mKσ mBσ
    d1 d2 Mσ hMσ Mσ' hMσ' x v u hv hu
  have hbase : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap (σ.comp e₂) ≫ z₁ := by
    rw [spMap_comp (algebraMap (𝓞 L) L) σ, spMap_comp e₂ σ, Category.assoc, Category.assoc, hz]
  have hb1 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _) ≫ spMap (σ.comp e₂) ≫ z₁ := by
    rw [hbase, Category.comp_id]
  have hb2 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [spMap_comp (algebraMap (𝓞 L) L) σ, Category.comp_id, Category.assoc]
  have hb3 : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _) ≫ spMap (σ.comp e₂) =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂ := by
    rw [spMap_comp e₂ σ, Category.comp_id, Category.assoc]
  have base : ∀ e : V₁, ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ∧
      u.left ≫ m'.φ = (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro e
    obtain ⟨vL, hvL⟩ := exists_lift P₂.m.cart.1 (spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _)
      (spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt e).left) (by
        have hMe : (MB.pt e).left ≫ t.G.hom = spMap (algebraMap (𝓞 L) (DualNumber (𝓞 L))) ≫ z := Over.w (MB.pt e)
        rw [Category.assoc, hMe, ← Category.assoc, LieTangent.spec_dual_alg, Category.assoc, hz, Category.comp_id])
    have hfe : (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ w ≫ m'.φ =
        spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB'.pt (f e)).left := hf e vL hvL
    obtain ⟨v, hv⟩ := exists_lift Pσ.m.cart.1 (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _)
      (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left
      ((Over.w (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))).trans hb1)
    obtain ⟨u, hu⟩ := exists_lift m'.cart.1 (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ)
      (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left
      ((Over.w (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e))).trans hb2)
    refine ⟨v, u, hv, hu, ?_⟩
    have hde : spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) =
        spMap (dualMap σ) ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := spMap_dual_comp _ _
    have hd : spMap (dualMap σ) ≫ spMap (algebraMap L (DualNumber L)) =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := LieTangent.spec_dual_alg σ
    have h1 : (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left =
        spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left :=
      (Category.comp_id _).symm.trans (hMσ e)
    have h1' : (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] f e)).left =
        spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB'.pt (f e)).left :=
      (Category.comp_id _).symm.trans (hMσ' (f e))
    have hvd : v.left ≫ Pσ.m.φ = spMap (dualMap σ) ≫ vL.left ≫ P₂.m.φ := by
      rw [hv, h1, hde, Category.assoc, hvL]
    have wv : v.left ≫ Pσ.tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ 𝟙 _ := Over.w v
    have wvL : vL.left ≫ P₂.tK.G.hom = spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _ := Over.w vL
    have star : v.left ≫ mKσ.φ = spMap (dualMap σ) ≫ vL.left ≫ mK2.φ := by
      refine P₁.m.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, d1, hvd, Category.assoc, Category.assoc, c1]
      · rw [Category.assoc, mKσ.cart.1.w, ← Category.assoc, wv, hb3]
        simp only [Category.assoc]
        rw [mK2.cart.1.w, ← Category.assoc vL.left, wvL, Category.comp_id]
        have hd2 : spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ ≫ spMap e₂ =
            spMap (dualMap σ) ≫ spMap (algebraMap L (DualNumber L)) ≫ spMap e₂ := by
          rw [← Category.assoc, ← hd, Category.assoc]
        exact hd2
    have wu : u.left ≫ tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := Over.w u
    have wq : (vL ≫ P₂.τ.q).left ≫ P₂.τ.B.hom = spMap (algebraMap L (DualNumber L)) ≫ 𝟙 _ := Over.w (vL ≫ P₂.τ.q)
    have we : P₂.e.hom.left ≫ P₂.tB.G.hom = P₂.τ.B.hom := Over.w P₂.e.hom
    have hu2 : u.left = spMap (dualMap σ) ≫ (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ w := by
      refine m'.cart.1.hom_ext ?_ ?_
      · rw [hu, h1', hde]
        simp only [Category.assoc]
        rw [hfe]
      · rw [wu]
        simp only [Category.assoc]
        rw [hw', we, wq, Category.comp_id, hd]
    have e1 : (vL ≫ P₂.τ.q).left ≫ P₂.e.hom.left ≫ mB2.φ = vL.left ≫ (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ := by
      simp only [Over.comp_left, Category.assoc]
    have e2 : (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ = v.left ≫ (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
      rw [Over.comp_left, Category.assoc]
    rw [hu2, e2, ← d2, ← Category.assoc v.left, star]
    simp only [Category.assoc]
    rw [hw, e1, ← c2]
  have tm : ∀ (c : GroundTheory.Heights₂.Heights.ComplexAt σ) (e : V₁), ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt (c ⊗ₜ[𝓞 L] e)).left ∧
      u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) (c ⊗ₜ[𝓞 L] e))).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro c e
    obtain ⟨v, u, h, k, l⟩ := base e
    let c' : ℂ := c
    have hs : c' • (1 : GroundTheory.Heights₂.Heights.ComplexAt σ) = c := by
      rw [GroundTheory.Heights₂.Heights.ComplexAt.complex_smul_def, _root_.mul_one]
      rfl
    have hc : ∀ (W : Type) [AddCommGroup W] [Module (𝓞 L) W] (a : W),
        c ⊗ₜ[𝓞 L] a = c' • ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] a) := by
      intro W _ _ a
      rw [TensorProduct.smul_tmul', hs]
    refine ⟨scale _ c' v, scale _ c' u, ?_, ?_, ?_⟩
    · rw [hc, Mσ.smul, scale_left, Category.assoc, h]
    · rw [LinearMap.lTensor_tmul, hc, Mσ'.smul, scale_left, Category.assoc, k]
    · rw [scale_left, Category.assoc, l]
      simp only [Over.comp_left, scale_left, Category.assoc]
  have hx0 : ∀ u : epsAt (spMap σ) ⟶ tK.G, (u.left ≫ mP.φ) ≫ P₁.tB.G.hom =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂ := by
    intro u
    have wu : u.left ≫ tK.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := Over.w u
    rw [Category.assoc, mP.cart.1.w, ← Category.assoc, wu]
  have key : ∀ x : GroundTheory.Heights₂.Heights.Fibre σ V₁, ∃ (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G),
      v.left ≫ Pσ.m.φ = (Mσ.pt x).left ∧
      u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left ∧
      u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      have h0 := tm 0 0
      rwa [TensorProduct.zero_tmul] at h0
    | tmul c e => exact tm c e
    | add x y hx hy =>
      obtain ⟨v₁, u₁, h₁, k₁, l₁⟩ := hx
      obtain ⟨v₂, u₂, h₂, k₂, l₂⟩ := hy
      refine ⟨v₁ * v₂, u₁ * u₂, ?_, ?_, ?_⟩
      · rw [Mσ.add]
        exact (grp_mul Pσ.m.cart _ _ hb1 v₁ v₂ (Mσ.pt x) (Mσ.pt y) h₁.symm h₂.symm).symm
      · rw [map_add, Mσ'.add]
        exact (grp_mul m'.cart _ _ hb2 u₁ u₂ _ _ k₁.symm k₂.symm).symm
      · rw [abPart_mul]
        let x₀ : Over.mk ((spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂) ⟶ P₁.tB.G :=
          Over.homMk (u₁.left ≫ mP.φ) (hx0 u₁)
        let y₀ : Over.mk ((spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ) ≫ spMap e₂) ⟶ P₁.tB.G :=
          Over.homMk (u₂.left ≫ mP.φ) (hx0 u₂)
        rw [← grp_mul mP.cart _ _ rfl u₁ u₂ x₀ y₀ rfl rfl]
        exact grp_mul mBσ.cart _ _ hb3.symm _ _ x₀ y₀ l₁ l₂
  obtain ⟨v₀, u₀, h₀, k₀, l₀⟩ := key x
  have hv' : v = v₀ := lift_unique Pσ.m.cart.1 _ _ (hv.trans h₀.symm)
  have hu' : u = u₀ := lift_unique m'.cart.1 _ _ (hu.trans k₀.symm)
  rw [hv', hu']
  exact l₀

end GlobalTheory.CompanionTheory.Ar.TanCompare
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_maps_compatible_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (V₁ V₂ : Type) [AddCommGroup V₁] [Module (𝓞 L) V₁] [AddCommGroup V₂] [Module (𝓞 L) V₂] (MB : LieModel t.G z V₁) (MB' : LieModel t'.G (𝟙 _) V₂) (f : V₁ →ₗ[𝓞 L] V₂) (hf : ∀ (e : V₁) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), MB.Lifts (algebraMap (𝓞 L) L) P₂.m.φ e v → MB'.Lifts (algebraMap (𝓞 L) L) (P₂.e.hom.left ≫ w ≫ m'.φ) (f e) (v ≫ P₂.τ.q)) (σ : L →+* ℂ) (Pσ : AbPart t (spMap (σ.comp e₂) ≫ z₁)) (mKσ : SABMap Pσ.tK P₁.tK (spMap (σ.comp e₂))) (mBσ : SABMap Pσ.tB P₁.tB (spMap (σ.comp e₂))) (d1 : mKσ.φ ≫ P₁.m.φ = Pσ.m.φ) (d2 : mKσ.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ) (Mσ : LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V₁)) (hMσ : ∀ e : V₁, MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 t.G.left) e (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))) (Mσ' : LieModel t'.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (GroundTheory.Heights₂.Heights.Fibre σ V₂)) (hMσ' : ∀ e : V₂, MB'.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 t'.G.left) e (Mσ'.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))) (x : GroundTheory.Heights₂.Heights.Fibre σ V₁) (v : epsAt (𝟙 (Sp ℂ)) ⟶ Pσ.tK.G) (u : epsAt (spMap σ) ⟶ tK.G), v.left ≫ Pσ.m.φ = (Mσ.pt x).left → u.left ≫ m'.φ = (Mσ'.pt (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x)).left → u.left ≫ mP.φ = (v ≫ Pσ.τ.q ≫ Pσ.e.hom).left ≫ mBσ.φ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TanCompare.tan_compare
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SlopeNorm

open GroundTheory.Heights₂.Heights

theorem core_left {V : Type} [AddCommGroup V] [Module ℂ V] (c₁ c₂ : InnerProductSpace.Core ℂ V) (W : Set V)
    (hW : Submodule.span ℂ W = ⊤) (a : V) (h : ∀ b ∈ W, c₁.inner b a = c₂.inner b a) (b : V) :
    c₁.inner b a = c₂.inner b a := by
  have hb : b ∈ Submodule.span ℂ W := hW ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have e₁ := c₁.smul_left 0 a 0
    have e₂ := c₂.smul_left 0 a 0
    simp only [smul_zero, map_zero, zero_mul] at e₁ e₂
    rw [e₁, e₂]
  | add x y _ _ hx hy => rw [c₁.add_left, c₂.add_left, hx, hy]
  | smul r x _ hx => rw [c₁.smul_left, c₂.smul_left, hx]

theorem core_eq {V : Type} [AddCommGroup V] [Module ℂ V] (c₁ c₂ : InnerProductSpace.Core ℂ V) (W : Set V)
    (hW : Submodule.span ℂ W = ⊤) (h : ∀ a ∈ W, ∀ b ∈ W, c₁.inner a b = c₂.inner a b) (a b : V) :
    c₁.inner a b = c₂.inner a b := by
  refine core_left c₁ c₂ W hW b (fun x hx => ?_) a
  have e := core_left c₁ c₂ W hW x (fun y hy => h y hy x hx) b
  rw [← c₁.conj_inner_symm, ← c₂.conj_inner_symm, e]

variable {L : Type} [Field L]

theorem span_tmul (σ : L →+* ℂ) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] :
    Submodule.span ℂ (Set.range fun e : V => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = ⊤ := by
  refine (Submodule.eq_top_iff'.2 fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c e =>
    have hc : c ⊗ₜ[𝓞 L] e = ((ComplexAt.ofComplex σ).symm c : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) := by
      rw [TensorProduct.smul_tmul', ComplexAt.complex_smul_def]
      simp
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

theorem spComp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    spMap c ≫ spMap d = spMap (c.comp d) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

def lf {S : Scheme.{0}} {G : Over S} {R : Type} [CommRing R] {x : Sp R ⟶ S} (v : epsAt x ⟶ G) :
    Sp (DualNumber R) ⟶ G.left :=
  v.left

theorem exists_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x x' : Sp R ⟶ S}
    (h : x = x') {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∃ M' : LieModel G x' V, ∀ e, lf (M'.pt e) = lf (M.pt e) := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem exists_lift {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S') {b : Sp R ⟶ S}
    (hb : x' ≫ f = b) {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G b V) :
    ∃ M' : LieModel G' x' V, ∀ e, lf (M'.pt e) ≫ φ = lf (M.pt e) := by
  subst hb
  exact (LiePull.lieModel_pullback S S' G G' f φ h R x' V).1 M

theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S')
    (v : epsAt x' ⟶ G') : ∃ u : epsAt (x' ≫ f) ⟶ G, lf v ≫ φ = lf u :=
  ⟨LiePull.tanPts h x' v, rfl⟩

theorem hodge_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] (Lb : LB G.left) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') {c : ℂ}
    (hc : HodgeIP G Lb z v w c) : HodgeIP G Lb z' v' w' c := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  exact hc

theorem ip_congr {S : Scheme.{0}} {G : Over S}
    (ip : ∀ z : Sp ℂ ⟶ S, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') :
    ip z v w = ip z' v' w' := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  rfl

end GlobalTheory.CompanionTheory.Ar.SlopeNorm

open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.SlopeNorm GlobalTheory.CompanionTheory.Ar.LiePull in

theorem GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M₀ y) (K₀ : ℝ) (hQ : ∀ (zc : Sp ℂ ⟶ X) (P : AbPart t zc) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt zc ⟶ t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K₀ * (h.ip zc v₀ v₀).re) (B B' : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G z B.carrier) (MB' : LieModel t'.G (𝟙 _) B'.carrier) (hB : IsFibre (fun z v w c => c = h.ip z v w) z B MB) (hB' : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B' MB') (f : B.carrier →ₗ[𝓞 L] B'.carrier) (hf : ∀ (e : B.carrier) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), MB.Lifts (algebraMap (𝓞 L) L) P₂.m.φ e v → MB'.Lifts (algebraMap (𝓞 L) L) (P₂.e.hom.left ≫ w ≫ m'.φ) (f e) (v ≫ P₂.τ.q)) (σ : L →+* ℂ) (x : GroundTheory.Heights₂.Heights.Fibre σ B.carrier), sqAt B' σ (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x) ≤ K₀ * sqAt B σ x := by
  intro E _ _ _ H X t L₁ L _ _ _ e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' Ω _ ξ Li _ _ M₀ K J y h K₀ hQ
    B B' MB MB' hB hB' f hf σ x
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : Smooth t'.G.hom := t'.semi.smooth
  obtain ⟨Pσ, mKσ, mBσ, d1, d2⟩ := GlobalTheory.T.abelian_part_base_change E H X t L₁ ℂ z₁ P₁ (σ.comp e₂)
  obtain ⟨Mσ, hMσ⟩ := GlobalTheory.T.lie_model_complex_base_change X t.G L z B.carrier MB σ
  obtain ⟨Mσ', hMσ'⟩ := GlobalTheory.T.lie_model_complex_base_change (Sp (𝓞 L)) t'.G L (𝟙 _) B'.carrier MB' σ
  have hb : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap (σ.comp e₂) ≫ z₁ := by
    rw [← spComp (algebraMap (𝓞 L) L) σ, ← spComp e₂ σ, Category.assoc, Category.assoc, hz]
  have hb' : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ = spMap σ ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [Category.comp_id, spComp]
  have hb2 : spMap σ ≫ spMap e₂ = 𝟙 _ ≫ spMap (σ.comp e₂) := by
    rw [Category.id_comp, spComp]

  obtain ⟨core₁, hcore₁⟩ := h.herm _ (Fibre σ B.carrier) Mσ
  have h1 : ∀ a b, (B.metric.form σ).inner a b = h.ip _ (Mσ.pt a) (Mσ.pt b) := by
    intro a b
    rw [← hcore₁]
    refine core_eq _ _ _ (span_tmul σ _) ?_ a b
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    rw [hcore₁]
    exact hB σ e e' _ _ (hMσ e) (hMσ e')

  obtain ⟨Mz, hMz⟩ := exists_transport hb' Mσ'
  have h2 : ∀ a b, HodgeIP t'.G t'.PP.L (spMap σ ≫ spMap (algebraMap (𝓞 L) L)) (Mz.pt a) (Mz.pt b)
      ((B'.metric.form σ).inner a b) := by
    refine GlobalTheory.T.hodge_inner_product_on_span E H (Sp L) (Sp (𝓞 L)) tK t' (spMap (algebraMap (𝓞 L) L)) m' (spMap σ)
      (Fibre σ B'.carrier) Mz (B'.metric.form σ) (Set.range fun e => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e)
      ⟨0, TensorProduct.tmul_zero _ _⟩ (span_tmul σ _) ?_
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    exact hodge_congr t'.PP.L hb' (hMz _).symm (hMz _).symm (hB' σ e e' _ _ (hMσ' e) (hMσ' e'))

  obtain ⟨Mc, hMc⟩ := exists_transport hb Mσ
  obtain ⟨Mv, hMv⟩ := exists_lift Pσ.m.cart (𝟙 _) (by rw [Category.id_comp]; exact hb.symm) Mσ
  obtain ⟨Mu, hMu⟩ := exists_lift m'.cart (spMap σ) hb'.symm Mσ'
  have hv₀ : lf (Mv.pt x) ≫ Pσ.m.φ = lf (Mc.pt x) := (hMv x).trans (hMc x).symm
  have h3 := GlobalTheory.T.abelian_part_maps_compatible_left E H X t L₁ L e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' B.carrier B'.carrier
    MB MB' f hf σ Pσ mKσ mBσ d1 d2 Mσ hMσ Mσ' hMσ' x (Mv.pt x) (Mu.pt (f.lTensor (ComplexAt σ) x)) (hMv x) (hMu _)

  have hUz : lf (Mu.pt (f.lTensor (ComplexAt σ) x)) ≫ m'.φ = lf (Mz.pt (f.lTensor (ComplexAt σ) x)) :=
    (hMu _).trans (hMz _).symm
  have a1 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp L) (Sp (𝓞 L)) tK t' (spMap (algebraMap (𝓞 L) L)) m' (spMap σ)
    (Mu.pt (f.lTensor (ComplexAt σ) x)) (Mu.pt (f.lTensor (ComplexAt σ) x))
    (Mz.pt (f.lTensor (ComplexAt σ) x)) (Mz.pt (f.lTensor (ComplexAt σ) x)) hUz hUz).1 _).2
    (h2 (f.lTensor (ComplexAt σ) x) (f.lTensor (ComplexAt σ) x))
  obtain ⟨U, hU⟩ := exists_push mP.cart (spMap σ) (Mu.pt (f.lTensor (ComplexAt σ) x))
  obtain ⟨Vv, hV⟩ := exists_push mBσ.cart (𝟙 _) (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom)
  have a2 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp L) (Sp L₁) tK P₁.tB (spMap e₂) mP (spMap σ)
    (Mu.pt (f.lTensor (ComplexAt σ) x)) (Mu.pt (f.lTensor (ComplexAt σ) x)) U U hU hU).1 _).1 a1
  have hUV : lf U = lf Vv := hU.symm.trans (Eq.trans h3 hV)
  have a3 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp ℂ) (Sp L₁) Pσ.tB P₁.tB (spMap (σ.comp e₂)) mBσ (𝟙 _)
    (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom) (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom) Vv Vv hV hV).1 _).2
    (hodge_congr P₁.tB.PP.L hb2 hUV hUV a2)
  have h5 := hQ (spMap (σ.comp e₂) ≫ z₁) Pσ (Mv.pt x) (Mc.pt x) _ (Mv.tan x) hv₀ a3
  have h6 : h.ip _ (Mc.pt x) (Mc.pt x) = (B.metric.form σ).inner x x := by
    rw [h1]
    exact ip_congr h.ip hb.symm (hMc x) (hMc x)
  rw [h6] at h5
  exact h5
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_maps_compatible_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M₀ y) (K₀ : ℝ) (hQ : ∀ (zc : Sp ℂ ⟶ X) (P : AbPart t zc) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt zc ⟶ t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K₀ * (h.ip zc v₀ v₀).re) (B B' : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G z B.carrier) (MB' : LieModel t'.G (𝟙 _) B'.carrier) (hB : IsFibre (fun z v w c => c = h.ip z v w) z B MB) (hB' : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B' MB') (f : B.carrier →ₗ[𝓞 L] B'.carrier) (hf : ∀ (e : B.carrier) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), MB.Lifts (algebraMap (𝓞 L) L) P₂.m.φ e v → MB'.Lifts (algebraMap (𝓞 L) L) (P₂.e.hom.left ≫ w ≫ m'.φ) (f e) (v ≫ P₂.τ.q)) (σ : L →+* ℂ) (x : GroundTheory.Heights₂.Heights.Fibre σ B.carrier), sqAt B' σ (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x) ≤ K₀ * sqAt B σ x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SlopeUnif

theorem isGrpPullback_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · haveI : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · have e₁ : (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      first | exact Hom.mul_comp _ _ _ | exact MonObj.mul_comp _ _ _ | exact CategoryTheory.Hom.mul_comp _ _ _
    have : (x * y).left ≫ e.hom.left = ((x ≫ e.hom) * (y ≫ e.hom)).left := by
      rw [← e₁]; rfl
    rw [this]
    exact mul_left_congr (Category.comp_id _) _ _ _ _ hx hy

theorem exists_compare {S S₁ : Scheme.{0}} {f : S₁ ⟶ S} {A A' : Over S₁} {C : Over S} [GrpObj A] [GrpObj A'] [GrpObj C]
    {a : A.left ⟶ C.left} {a' : A'.left ⟶ C.left} (hA : IsGrpPullback A C f a) (hA' : IsGrpPullback A' C f a') :
    ∃ w : A.left ⟶ A'.left, w ≫ a' = a ∧ w ≫ A'.hom = A.hom ∧ IsGrpPullback A A' (𝟙 S₁) w := by
  refine ⟨hA'.1.lift a A.hom hA.1.w, hA'.1.lift_fst _ _ _, hA'.1.lift_snd _ _ _, ?_⟩
  refine IsGrpPullback.cancel hA' ?_ ?_
  · rw [hA'.1.lift_fst, Category.id_comp]; exact hA
  · rw [hA'.1.lift_snd, Category.comp_id]

theorem slope_unif : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L₀ : Type) [Field L₀] [NumberField L₀] (z₀ : Sp (𝓞 L₀) ⟶ 𝔐.X), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L), ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G (spMap (RingOfIntegers.mapRingHom e) ≫ z₀) B.carrier), IsFibre (fun z v w c => c = h.ip z v w) _ B MB → B.slopeMax ≤ ((C * Real.log (2 + C + max (-B.normDegree ⊤) 0) + C : ℝ) : EReal) := by
  intro hN hP hR hH hS E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 h hpq
  obtain ⟨K₀, hK₀, hQ⟩ := GlobalTheory.T.lie_metric_height_bound hR E H D l Xo c Y S Ω K J y 𝔐 h hpq
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨C₁, hC₁, hT⟩ := GlobalTheory.T.semiabelian_lie_metric_height hH 𝔐.X Ω K J y 𝔐.ξ inferInstance 𝔐.all 𝔐.tie 𝔐.t.G 𝔐.t.semi 𝔐.Li 𝔐.M h
  obtain ⟨C₀, hC₀, hSl⟩ := hS
  obtain ⟨Cc, hCc1, hCcK, hCc₁, hCc₀⟩ : ∃ Cc : ℝ, 1 ≤ Cc ∧ K₀ ≤ Cc ∧ C₁ ≤ Cc ∧ C₀ ≤ Cc :=
    ⟨max (max K₀ C₁) (max C₀ 1), by simp, by simp, by simp, by simp⟩
  obtain ⟨C', hC', hPB⟩ := GlobalTheory.T.hermitian_bundle_quotient_degree_bound (Module.finrank Ω 𝔐.Li) Cc hCc1
  refine ⟨C', hC', fun L₀ _ _ z₀ => ?_⟩
  obtain ⟨L₁, _, _, e₁, ⟨P₁⟩⟩ := GlobalTheory.T.exists_abelian_part_extension E H 𝔐.X 𝔐.t L₀ (spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀)
  obtain ⟨σ₁⟩ : Nonempty (L₁ →+* ℂ) := inferInstance
  obtain ⟨P₁c, _, mBc, _, _⟩ := GlobalTheory.T.abelian_part_base_change E H 𝔐.X 𝔐.t L₁ ℂ _ P₁ σ₁
  have hpr : IsPrincipal P₁.tB := (GlobalTheory.T.isPrincipal_base_change_iff E H L₁ ℂ σ₁ P₁.tB P₁c.tB mBc).1 (hQ _ P₁c).1
  obtain ⟨L, _, _, e₂, t', tK, ⟨m'⟩, ⟨mP⟩⟩ := GlobalTheory.T.lie_signature_number_field hN hP E H L₁ P₁.tB hpr
    (GlobalTheory.T.abelian_part_lie_signature E H D l Xo c Y S Ω K J y 𝔐 L₁ _ P₁)
  have hprK : IsPrincipal tK := (GlobalTheory.T.isPrincipal_base_change_iff E H L₁ L e₂ P₁.tB tK mP).2 hpr
  refine ⟨L, inferInstance, inferInstance, e₂.comp e₁, fun B MB hB => ?_⟩
  have hz : spMap (algebraMap (𝓞 L) L) ≫ (spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀) =
      spMap e₂ ≫ (spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀) := by
    have e : spMap (algebraMap (𝓞 L) L) ≫ spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) =
        spMap e₂ ≫ spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    rw [← Category.assoc, e]
    simp only [Category.assoc]
  obtain ⟨B', MB', hB'⟩ := GlobalTheory.T.principal_hermitian_fibre E H L t' tK m' hprK
  have hslope := hSl E H L t' tK m' hprK B' MB' hB'
  obtain ⟨P₂, mK2, mB2, c1, c2⟩ := GlobalTheory.T.abelian_part_base_change E H 𝔐.X 𝔐.t L₁ L _ P₁ e₂
  obtain ⟨w, hw, hw', hwp⟩ := exists_compare mB2.cart mP.cart
  letI := P₂.τ.addCommGroup
  letI := P₂.τ.grpB
  haveI := P₂.e_hom
  have hφ' : IsGrpPullback P₂.τ.B t'.G (spMap (algebraMap (𝓞 L) L)) (P₂.e.hom.left ≫ w ≫ m'.φ) := by
    have := (isGrpPullback_iso P₂.e).comp (hwp.comp m'.cart)
    simpa using this
  obtain ⟨MT, hMT⟩ := GlobalTheory.T.exists_cocharacter_lie_model (Sp L) P₂.τ.X L (𝟙 _)
  have hcart : IsGrpPullback P₂.tK.G 𝔐.t.G (spMap (algebraMap (𝓞 L) L) ≫ (spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀)) P₂.m.φ := by
    rw [hz]; exact P₂.m.cart
  obtain ⟨r, bs, hbs⟩ := hT L _ P₂.tK.G P₂.m.φ P₂.τ hcart
  obtain ⟨ε, f, hε, hf, hli, hker, hsur⟩ := GlobalTheory.T.semi_abelian_pullback_torus_extension 𝔐.X 𝔐.t.G 𝔐.t.semi L _ P₂.tK.G P₂.m.φ P₂.τ t'.G _ t'.semi hcart hφ'
    MT hMT B.carrier B'.carrier MB MB' r bs
  have hbd := hbs MT hMT B MB hB ε hε
  have hnb := GlobalTheory.T.abelian_part_maps_compatible_right E H 𝔐.X 𝔐.t L₁ L e₂ _ _ hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' Ω 𝔐.ξ 𝔐.Li 𝔐.M K J y h K₀
    (fun zc P v v₀ c => (hQ zc P).2 v v₀ c) B B' MB MB' hB hB' f hf
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hrk := GlobalTheory.T.lie_model_rank_eq_generic 𝔐.X Ω 𝔐.ξ 𝔐.all 𝔐.t.G 𝔐.Li 𝔐.M L _ B.carrier MB
  have hC₁0 : (0 : ℝ) < C₁ := by linarith
  have hCc0 : (0 : ℝ) < Cc := by linarith
  refine hPB L B B' r ε f hrk hli hker hsur ?_ ?_ ?_
  · intro σ u
    have hs : 0 ≤ ∑ a, ‖u a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
    obtain ⟨h₁, h₂⟩ := hbd σ u
    refine ⟨le_trans (mul_le_mul_of_nonneg_right ?_ hs) h₁, h₂.trans (mul_le_mul_of_nonneg_right hCc₁ hs)⟩
    exact inv_anti₀ hC₁0 hCc₁
  · intro σ x
    have h0 : 0 ≤ sqAt B σ x := by
      have := (B.metric.form σ).re_inner_nonneg x
      simpa [sqAt] using this
    exact (hnb σ x).trans (mul_le_mul_of_nonneg_right hCcK h0)
  · refine hslope.trans (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_right hCc₀ (Real.log_nonneg ?_)))
    have : (0 : ℝ) ≤ max (-B'.normDegree ⊤) 0 := le_max_right _ _
    have h' : (0 : ℝ) ≤ Module.finrank (𝓞 L) B'.carrier := Nat.cast_nonneg _
    linarith

end GlobalTheory.CompanionTheory.Ar.SlopeUnif
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_lie_metric_bound : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L₀ : Type) [Field L₀] [NumberField L₀] (z₀ : Sp (𝓞 L₀) ⟶ 𝔐.X), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L), ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G (spMap (RingOfIntegers.mapRingHom e) ≫ z₀) B.carrier), IsFibre (fun z v w c => c = h.ip z v w) _ B MB → B.slopeMax ≤ ((C * Real.log (2 + C + max (-B.normDegree ⊤) 0) + C : ℝ) : EReal) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.SlopeUnif.slope_unif
end
