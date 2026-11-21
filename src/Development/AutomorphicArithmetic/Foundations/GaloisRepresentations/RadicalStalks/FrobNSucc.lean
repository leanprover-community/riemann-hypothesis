import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OneLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCorrFormPullTensorForm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NonvanishingPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZeroSmoothAffineOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobEpi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.EpsMulSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamRingAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFinrankDeRhamQuotientCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusEquivariantDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelPrimitiveDeRhamHodge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRelativeFrobeniusPrimitiveDeRhamEqConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeFrobeniusGrpSchemeCharP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundle

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.transl :
    ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (σ : k →+* k) (ψ : A.left ⟶ A.left), SMor A σ ψ →
      (∀ v : epsR k ⟶ A, IsTangent v → IsConst (v.left ≫ ψ)) → ∀ v : epsR k ⟶ A, IsConst (v.left ≫ ψ) := by
  intro k _ A _ σ ψ m hT v
  let z : Sp k ⟶ Sp (DualNumber k) := spMap (TrivSqZeroExt.fstHom k k k).toRingHom
  let r : Sp (DualNumber k) ⟶ Sp k := spMap (algebraMap k (DualNumber k))
  have hq : spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) = r ≫ z := by
    simp only [r, z, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hzr : z ≫ r = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
      ext x; simp
    simp only [r, z, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have hqq : (r ≫ z) ≫ r ≫ z = r ≫ z := by
    rw [Category.assoc, reassoc_of% hzr]
  let c : epsR k ⟶ epsR k := Over.homMk (r ≫ z) (by
    show (r ≫ z) ≫ r = r
    rw [Category.assoc, hzr, Category.comp_id])
  let zz : 𝟙_ (Over (Sp k)) ⟶ epsR k := Over.homMk z hzr
  have hzc : zz ≫ c = zz := Over.OverMorphism.ext (by
    show z ≫ r ≫ z = z
    rw [reassoc_of% hzr])
  let v0 : epsR k ⟶ A := c ≫ v
  let t : epsR k ⟶ A := v0⁻¹ * v
  have hvt : v = v0 * t := by simp [t]
  have hzt : zz ≫ t = 1 := by
    have a : zz ≫ v0 = zz ≫ v := by simp only [v0, ← Category.assoc, hzc]
    calc zz ≫ t = (zz ≫ v0⁻¹) * (zz ≫ v) := MonObj.comp_mul _ _ _
      _ = (zz ≫ v0⁻¹) * (zz ≫ v0) := by rw [a]
      _ = zz ≫ (v0⁻¹ * v0) := (MonObj.comp_mul _ _ _).symm
      _ = 1 := by rw [inv_mul_cancel, MonObj.comp_one]
  have htan : IsTangent t := by
    have e1 : (1 : 𝟙_ (Over (Sp k)) ⟶ A) = η[A] := by
      show toUnit _ ≫ η[A] = _
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    show z ≫ t.left = η[A].left
    rw [← e1, ← hzt]
    rfl
  let Y : Over (Sp k) := Over.mk ((epsR k).hom ≫ spMap σ)
  let Q : Y ⟶ Y := Over.homMk (r ≫ z) (by
    show (r ≫ z) ≫ r ≫ spMap σ = r ≫ spMap σ
    rw [Category.assoc, reassoc_of% hzr])
  have h0 : Q ≫ GlobalTheory.FrobAdjoint.down m v0 = GlobalTheory.FrobAdjoint.down m v0 := Over.OverMorphism.ext (by
    show (r ≫ z) ≫ ((r ≫ z) ≫ v.left) ≫ ψ = ((r ≫ z) ≫ v.left) ≫ ψ
    simp only [← Category.assoc]
    rw [show ((r ≫ z) ≫ r) ≫ z = r ≫ z by simpa using hqq])
  have h1 : Q ≫ GlobalTheory.FrobAdjoint.down m t = GlobalTheory.FrobAdjoint.down m t := Over.OverMorphism.ext (by
    have := hT t htan
    unfold IsConst at this
    rw [hq] at this
    exact this)
  have key : Q ≫ GlobalTheory.FrobAdjoint.down m v = GlobalTheory.FrobAdjoint.down m v := by
    rw [hvt, GlobalTheory.FrobAdjoint.down_mul, MonObj.comp_mul, h0, h1]
  unfold IsConst
  rw [hq]
  exact congrArg (fun u => u.left) key
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem exists_functional_ne_zero_projective {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    [Module.Projective B M] {m : M} (hm : m ≠ 0) : ∃ l : M →ₗ[B] B, l m ≠ 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective B M)
  by_contra hall
  push_neg at hall
  apply hm
  have h0 : s m = 0 := by
    ext a
    simpa using hall (Finsupp.lapply a ∘ₗ s)
  have := LinearMap.congr_fun hs m
  simpa [h0] using this.symm

private theorem exists_point_nonvanishing_reduced (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [IsReduced B] {c : B} (hc : c ≠ 0) :
    ∃ x : B →ₐ[k] k, x c ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.NonvanishingPoint.exists_point_nonvanishing_reduced k B hc

theorem UpperTheory.Gal.Ord.dz1 :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B] [Module.Projective B Ω[B⁄k]] (r : B),
      (∀ v : B →ₐ[k] DualNumber k, TrivSqZeroExt.snd (v r) = 0) → KaehlerDifferential.D k B r = 0 := by
  intro k _ _ B _ _ _ _ _ r hv
  by_contra hne
  obtain ⟨l, hl⟩ := exists_functional_ne_zero_projective (B := B) hne
  obtain ⟨x, hx⟩ := exists_point_nonvanishing_reduced k B hl
  let d : B →ₗ[k] k := x.toLinearMap ∘ₗ (l.restrictScalars k) ∘ₗ (KaehlerDifferential.D k B).toLinearMap
  have hd : ∀ b, d b = x (l (KaehlerDifferential.D k B b)) := fun _ => rfl
  let f : B →ₗ[k] DualNumber k :=
    Algebra.linearMap k (DualNumber k) ∘ₗ x.toLinearMap + TrivSqZeroExt.inrHom k k ∘ₗ d
  have hal : ∀ c : k, algebraMap k (DualNumber k) c = TrivSqZeroExt.inl c := fun _ => rfl
  have hfst : ∀ b, TrivSqZeroExt.fst (f b) = x b := fun b => by simp [f, hal]
  have hsnd : ∀ b, TrivSqZeroExt.snd (f b) = d b := fun b => by simp [f, hal]
  let v : B →ₐ[k] DualNumber k := AlgHom.ofLinearMap f
    (by
      apply TrivSqZeroExt.ext
      · simp [hfst]
      · simp [hsnd, hd])
    (by
      intro a b
      apply TrivSqZeroExt.ext
      · simp [hfst]
      · simp [hfst, hsnd, hd, Derivation.leibniz, mul_comm, add_comm])
  apply hx
  have := hv v
  simpa [v, hsnd, hd] using this
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private lemma rootGlue_uniq {R : Type*} [CommRing R] [IsReduced R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) {a b : R} (hab : a ^ p = b ^ p) : a = b := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim a b
  · haveI : CharP R p := (CharP.charP_iff_prime_eq_zero hp).mpr h
    haveI : Fact p.Prime := ⟨hp⟩
    apply frobenius_inj R p
    simpa [frobenius_def] using hab

theorem UpperTheory.Gal.Ord.rootGlue :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X], (p : Γ(X, ⊤)) = 0 → ∀ (U : X.Opens) (s : Γ(X, U)),
      (∀ (V : X.Opens) (hV : V ≤ U), IsAffineOpen V → ∃ r : Γ(X, V), r ^ p = X.presheaf.map (homOfLE hV).op s) → ∃ r : Γ(X, U), r ^ p = s := by
  intro p _ X _ hp U s hloc
  have hpr : p.Prime := Fact.out
  have hpV : ∀ V : X.Opens, (p : Γ(X, V)) = 0 := by
    intro V
    have h0 := congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) hp
    rwa [map_natCast, map_zero] at h0
  let Idx := {V : X.Opens // V ≤ U ∧ IsAffineOpen V}
  choose r hr using fun i : Idx => hloc i.1 i.2.1 i.2.2
  have hcover : U ≤ ⨆ i : Idx, i.1 := by
    intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVU, hV⟩, hxV⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.obj (fun i : Idx => i.1) r := by
    intro i j
    apply rootGlue_uniq hpr (hpV _)
    change (X.presheaf.map _ (r i)) ^ p = (X.presheaf.map _ (r j)) ^ p
    rw [← map_pow, ← map_pow, hr i, hr j, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨t, ht, -⟩ : ∃! t : Γ(X, U), ∀ i : Idx, X.presheaf.map (homOfLE i.2.1).op t = r i :=
    X.sheaf.existsUnique_gluing' (fun i : Idx => i.1) U (fun i => homOfLE i.2.1) hcover r hcomp
  refine ⟨t, ?_⟩
  have key : ∀ i : Idx,
      X.presheaf.map (homOfLE i.2.1).op (t ^ p) = X.presheaf.map (homOfLE i.2.1).op s := by
    intro i
    rw [map_pow, ht i, hr i]
  exact X.sheaf.eq_of_locally_eq' (fun i : Idx => i.1) U (fun i => homOfLE i.2.1) hcover _ _ key
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private lemma ev_comp {T T' : Type} [CommRing T] [CommRing T'] (g : T →+* T') {Y : Scheme.{0}} (U : Y.Opens)
    (f : Sp T ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap g ≫ f) ⁻¹ᵁ U) :
    (spMap g ≫ f).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of T')).hom =
      (f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) ≫ CommRingCat.ofHom g := by
  rw [← Scheme.Hom.appLE_comp_appLE (spMap g) f U ⊤ ⊤ h (by simp), Category.assoc, Category.assoc]
  congr 1
  have hh : (spMap g).appLE ⊤ ⊤ (by simp) = (spMap g).appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [hh]
  exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)

private lemma fromSpec_ev {X : Scheme.{0}} {V W : X.Opens} (hV : IsAffineOpen V) (hVW : V ≤ W)
    (e : ⊤ ≤ hV.fromSpec ⁻¹ᵁ W) :
    hV.fromSpec.appLE W ⊤ e ≫ (Scheme.ΓSpecIso Γ(X, V)).hom = X.presheaf.map (homOfLE hVW).op := by
  have e' : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  rw [← Scheme.Hom.map_appLE hV.fromSpec e' (homOfLE hVW).op, Category.assoc]
  have key : hV.fromSpec.appLE V ⊤ e' ≫ (Scheme.ΓSpecIso Γ(X, V)).hom = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc]
    rw [← Functor.map_comp_assoc]
    have hid : ∀ i : Opposite.op (⊤ : (Spec Γ(X, V)).Opens) ⟶ Opposite.op ⊤, i = 𝟙 _ :=
      fun i => Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [hid (_ ≫ _), CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  rw [key, Category.comp_id]

private lemma snd_zero {k : Type} [Field k] {X Y : Scheme.{0}} (ψ : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (hV : V ≤ ψ ⁻¹ᵁ U) (hA : IsAffineOpen V) (φ : Γ(X, V) →+* DualNumber k)
    (hc : IsConst (spMap φ ≫ hA.fromSpec ≫ ψ)) (t : Γ(Y, U)) :
    TrivSqZeroExt.snd (φ (X.presheaf.map (homOfLE hV).op (ψ.app U t))) = 0 := by
  have h0 : ⊤ ≤ hA.fromSpec ⁻¹ᵁ (ψ ⁻¹ᵁ U) :=
    hA.fromSpec_preimage_self.ge.trans
      ((TopologicalSpace.Opens.map hA.fromSpec.base).map (homOfLE hV)).le
  have h1 : ⊤ ≤ (hA.fromSpec ≫ ψ) ⁻¹ᵁ U := h0
  have h2 : ⊤ ≤ (spMap φ ≫ hA.fromSpec ≫ ψ) ⁻¹ᵁ U := fun x _ => h1 (Set.mem_univ _)
  have hc' : spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
      spMap φ ≫ hA.fromSpec ≫ ψ = spMap φ ≫ hA.fromSpec ≫ ψ := hc
  have hcongr : ∀ (w₁ w₂ : Sp (DualNumber k) ⟶ Y), w₁ = w₂ → ∀ (e₁ : ⊤ ≤ w₁ ⁻¹ᵁ U)
      (e₂ : ⊤ ≤ w₂ ⁻¹ᵁ U), w₁.appLE U ⊤ e₁ = w₂.appLE U ⊤ e₂ := by
    rintro _ _ rfl _ _
    rfl
  have A := ev_comp ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)
    U (spMap φ ≫ hA.fromSpec ≫ ψ) h2 (hc'.symm ▸ h2)
  rw [hcongr _ _ hc' _ h2] at A
  have B := ev_comp φ U (hA.fromSpec ≫ ψ) h1 h2
  have C := fromSpec_ev hA hV h0
  have B' : (spMap φ ≫ hA.fromSpec ≫ ψ).appLE U ⊤ h2 ≫
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom =
      ψ.app U ≫ X.presheaf.map (homOfLE hV).op ≫ CommRingCat.ofHom φ := by
    rw [B, Scheme.Hom.comp_appLE, Category.assoc, Category.assoc]
    erw [← Category.assoc (hA.fromSpec.appLE _ _ _), C]
  have A' := ConcreteCategory.congr_hom A t
  rw [B'] at A'
  have hxx : φ (X.presheaf.map (homOfLE hV).op (ψ.app U t)) =
      ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)
        (φ (X.presheaf.map (homOfLE hV).op (ψ.app U t))) := by
    simpa using A'
  rw [hxx, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]

theorem UpperTheory.Gal.Ord.dzero :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X Y : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (ψ : X ⟶ Y),
      (∀ v : Sp (DualNumber k) ⟶ X, v ≫ s = spMap (algebraMap k (DualNumber k)) → IsConst (v ≫ ψ)) →
      ∀ (U : Y.Opens) (t : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U t := by
  intro p _ k _ _ hk X Y _ s _ ψ hψ U t
  have hp : (p : Γ(X, ⊤)) = 0 := by
    have h := congrArg (GlobalTheory.CechDR.secMap s ⊤).hom hk
    rwa [map_natCast, map_zero] at h
  refine rootGlue p X hp (ψ ⁻¹ᵁ U) (ψ.app U t) ?_
  intro V hV hA
  let V' : X.affineOpens := ⟨V, hA⟩
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s V) := by
    have hi : Smooth hA.fromSpec := inferInstance
    have h0 : Smooth (hA.fromSpec ≫ s) := MorphismProperty.comp_mem _ _ _ hi ‹Smooth s›
    have h1 : Smooth (GlobalTheory.CechDR.affPt s V' ≫ s) := h0
    rw [GlobalTheory.CechDR.affPt_w] at h1
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h1)
  haveI : _root_.IsReduced (GlobalTheory.CechDR.Sec s V) := IsReduced.component_reduced V
  have hD := dz1 k (GlobalTheory.CechDR.Sec s V) (X.presheaf.map (homOfLE hV).op (ψ.app U t)) ?_
  · exact GlobalTheory.T.exists_pow_eq_of_kaehlerD_eq_zero_smooth_affineOpen p k hk X s V' _ hD
  intro v
  have hw : (spMap v.toRingHom ≫ hA.fromSpec) ≫ s = spMap (algebraMap k (DualNumber k)) := by
    change spMap v.toRingHom ≫ GlobalTheory.CechDR.affPt s V' ≫ s = _
    rw [GlobalTheory.CechDR.affPt_w, ← Geo.Tor.spMap_comp]
    exact congrArg spMap v.comp_algebraMap
  have hc : IsConst (spMap v.toRingHom ≫ hA.fromSpec ≫ ψ) := by
    convert hψ _ hw using 1
    exact (Category.assoc _ _ _).symm
  exact snd_zero ψ hV hA v.toRingHom hc t
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.Ord.RootBuild

variable {p : ℕ} [hp : Fact p.Prime] {X Y : Scheme.{0}} [IsReduced X]

private theorem pow_inj (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens) {a b : Γ(X, U)} (e : a ^ p = b ^ p) :
    a = b := by
  have hU := GlobalTheory.SS.FrobField.cast_zero h U
  have hs := map_sub (GlobalTheory.SS.FrobField.powHom Γ(X, U) p 1 hp.out hU) a b
  have e2 : (a - b) ^ p = 0 := by
    simpa [GlobalTheory.SS.FrobField.powHom, e] using hs
  exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨p, e2⟩)

variable (ψ : X ⟶ Y)
  (H : ∀ (U : Y.Opens) (s : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U s)

private def rt (U : Y.Opens) (s : Γ(Y, U)) : Γ(X, ψ ⁻¹ᵁ U) := (H U s).choose

private theorem rt_pow (U : Y.Opens) (s : Γ(Y, U)) : rt ψ H U s ^ p = ψ.app U s := (H U s).choose_spec

private def rtHom (h : (p : Γ(X, ⊤)) = 0) (U : Y.Opens) : Γ(Y, U) →+* Γ(X, ψ ⁻¹ᵁ U) where
  toFun := rt ψ H U
  map_one' := pow_inj h _ (by rw [rt_pow, map_one, one_pow])
  map_mul' a b := pow_inj h _ (by rw [mul_pow, rt_pow, rt_pow, rt_pow, map_mul])
  map_zero' := pow_inj h _ (by rw [rt_pow, map_zero, zero_pow hp.out.ne_zero])
  map_add' a b := pow_inj h _ (by
    have hU := GlobalTheory.SS.FrobField.cast_zero h (ψ ⁻¹ᵁ U)
    have := map_add (GlobalTheory.SS.FrobField.powHom Γ(X, ψ ⁻¹ᵁ U) p 1 hp.out hU) (rt ψ H U a) (rt ψ H U b)
    have e : (rt ψ H U a + rt ψ H U b) ^ p = rt ψ H U a ^ p + rt ψ H U b ^ p := by
      simpa [GlobalTheory.SS.FrobField.powHom] using this
    rw [e, rt_pow, rt_pow, rt_pow, map_add])

private def rootPre (h : (p : Γ(X, ⊤)) = 0) : X.toPresheafedSpace.Hom Y.toPresheafedSpace where
  base := ψ.base
  c := { app := fun U => CommRingCat.ofHom (rtHom ψ H h U.unop)
         naturality := fun U V i => by
           ext s
           refine pow_inj h _ ?_
           have e := congrArg (fun φ => φ.hom s) (ψ.naturality i)
           show (rt ψ H V.unop ((Y.presheaf.map i).hom s)) ^ p =
             ((X.presheaf.map ((TopologicalSpace.Opens.map ψ.base).map i.unop).op).hom (rt ψ H U.unop s)) ^ p
           rw [rt_pow, ← map_pow, rt_pow]
           exact e }

private def rootMor (h : (p : Γ(X, ⊤)) = 0) : X ⟶ Y :=
  ⟨⟨rootPre ψ H h, fun x => ⟨fun a ha => by
    obtain ⟨U, hU, s, rfl⟩ := Y.presheaf.exists_germ_eq (x := ψ.base x) a
    have e := PresheafedSpace.stalkMap_germ_apply (rootPre ψ H h) U x hU s
    erw [e] at ha
    have ha' : IsUnit ((X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (rt ψ H U s)) := ha
    have e2 : (X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (ψ.app U s) =
        (X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (rt ψ H U s) ^ p := by
      rw [← rt_pow ψ H U s, map_pow]
    have hu : IsUnit ((X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (ψ.app U s)) := e2 ▸ ha'.pow p
    have e3 := Scheme.Hom.germ_stalkMap_apply ψ U x hU s
    rw [← e3] at hu
    exact isUnit_of_map_unit (ψ.stalkMap x).hom _ hu⟩⟩⟩

private theorem frob_rootMor (h : (p : Γ(X, ⊤)) = 0) : GlobalTheory.VB.frob X p h ≫ rootMor ψ H h = ψ := by
  refine Scheme.Hom.ext rfl ?_
  intro U
  erw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  ext s
  have e := GlobalTheory.VB.frob_app p h (rootMor ψ H h ⁻¹ᵁ U) (rt ψ H U s)
  refine Eq.trans ?_ (rt_pow ψ H U s)
  exact e

end UpperTheory.Gal.Ord.RootBuild

theorem UpperTheory.Gal.Ord.root0 :
    ∀ (p : ℕ) [Fact p.Prime] (X Y : Scheme.{0}) [IsReduced X] (h : (p : Γ(X, ⊤)) = 0) (ψ : X ⟶ Y),
      (∀ (U : Y.Opens) (s : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U s) → ∃ ψ' : X ⟶ Y, GlobalTheory.VB.frob X p h ≫ ψ' = ψ :=
  fun _ _ _ _ _ h ψ H => ⟨UpperTheory.Gal.Ord.RootBuild.rootMor ψ H h, UpperTheory.Gal.Ord.RootBuild.frob_rootMor ψ H h⟩

end
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.rootMor :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ σ' : k →+* k) (ψ ψ' : A.left ⟶ A.left), SMor A σ ψ → (∀ x, σ' x ^ p = σ x) →
      GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ ψ' = ψ → SMor A σ' ψ' := by
  intro p _ k _ _ hk A _ _ hAb σ σ' ψ ψ' hS hpow hfr
  haveI := hAb
  haveI : Smooth A.hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  haveI hP : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hAb hAb
  haveI : Smooth (A ⊗ A).hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced (A ⊗ A).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (A ⊗ A).hom
  haveI : Epi (GlobalTheory.VB.frob A.left p (cast_left p k hk A)) := (epi p A.left (cast_left p k hk A)).1
  haveI : Epi (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A))) :=
    (epi p (A ⊗ A).left (cast_left p k hk (A ⊗ A))).1
  have hσ : spMap (frobR p k hk) ≫ spMap σ' = spMap σ := by
    rw [← Geo.Tor.spMap_comp]
    congr 1
    ext x
    rw [RingHom.comp_apply, GlobalTheory.ConjSeq.frobR_apply, hpow]
  have hw' : ψ' ≫ A.hom = A.hom ≫ spMap σ' := by
    apply (cancel_epi (GlobalTheory.VB.frob A.left p (cast_left p k hk A))).mp
    rw [← Category.assoc, hfr, hS.w, ← Category.assoc,
      GlobalTheory.ConjSeq.frob_comp_hom p k hk A.hom (cast_left p k hk A), Category.assoc, hσ]
  have hnat : ∀ f : (A ⊗ A).left ⟶ A.left,
      GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A)) ≫ f ≫ ψ' = f ≫ ψ := by
    intro f
    rw [← Category.assoc, GlobalTheory.VB.frob_naturality p (cast_left p k hk A) f (cast_left p k hk (A ⊗ A)),
      Category.assoc, hfr]
  let F : Over.mk ((A ⊗ A).hom ≫ spMap σ) ⟶ Over.mk ((A ⊗ A).hom ≫ spMap σ') :=
    Over.homMk (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A))) (by
      simp only [Over.mk_hom]
      rw [← Category.assoc,
        GlobalTheory.ConjSeq.frob_comp_hom p k hk (A ⊗ A).hom (cast_left p k hk (A ⊗ A)), Category.assoc, hσ])
  let u : ∀ g : A ⊗ A ⟶ A, Over.mk ((A ⊗ A).hom ≫ spMap σ') ⟶ A := fun g =>
    Over.homMk (g.left ≫ ψ') (by
      simp only [Over.mk_hom]
      rw [Category.assoc, hw', ← Category.assoc, Over.w g])
  let v : ∀ g : A ⊗ A ⟶ A, Over.mk ((A ⊗ A).hom ≫ spMap σ) ⟶ A := fun g =>
    Over.homMk (g.left ≫ ψ) (by
      simp only [Over.mk_hom]
      rw [Category.assoc, hS.w, ← Category.assoc, Over.w g])
  have hFu : ∀ g : A ⊗ A ⟶ A, F ≫ u g = v g := by
    intro g
    apply Over.OverMorphism.ext
    simp only [F, u, v, Over.comp_left, Over.homMk_left]
    exact hnat g.left
  have huniv : (u (fst A A) * u (snd A A)).left = (fst A A * snd A A).left ≫ ψ' := by
    apply (cancel_epi (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A)))).mp
    rw [hnat]
    have e1 : (F ≫ (u (fst A A) * u (snd A A))).left = (v (fst A A) * v (snd A A)).left := by
      rw [MonObj.comp_mul, hFu, hFu]
    rw [Over.comp_left] at e1
    exact e1.trans (hS.mul (A ⊗ A) (fst A A) (snd A A) (v (fst A A)) (v (snd A A)) rfl rfl)
  refine GlobalTheory.DeRham.GrpMor.mk (isDPMorphism_of_eq_bot (dp0 k) rfl (dp0 k) σ') (by simp) hw' ?_
  intro T x y x₀ y₀ hx0 hy0
  let h : T ⟶ A ⊗ A := lift x y
  let hh : Over.mk (T.hom ≫ spMap σ') ⟶ Over.mk ((A ⊗ A).hom ≫ spMap σ') :=
    Over.homMk h.left (by
      simp only [Over.mk_hom]
      rw [← Category.assoc, Over.w h])
  have ex : x₀ = hh ≫ u (fst A A) := by
    apply Over.OverMorphism.ext
    simp only [hh, u, Over.comp_left, Over.homMk_left]
    rw [hx0, ← Category.assoc, ← Over.comp_left, lift_fst]
  have ey : y₀ = hh ≫ u (snd A A) := by
    apply Over.OverMorphism.ext
    simp only [hh, u, Over.comp_left, Over.homMk_left]
    rw [hy0, ← Category.assoc, ← Over.comp_left, lift_snd]
  rw [ex, ey, ← MonObj.comp_mul, Over.comp_left, huniv]
  simp only [hh, Over.homMk_left]
  rw [← Category.assoc, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.root :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ : k →+* k), Function.Bijective σ → ∀ (ψ : A.left ⟶ A.left) (m : SMor A σ ψ), (∀ x ∈ PrimitiveSubmodule A, m.pull x = 0) →
      ∃ (σ' : k →+* k) (ψ' : A.left ⟶ A.left), Function.Bijective σ' ∧ SMor A σ' ψ' ∧ (∀ x, σ' x ^ p = σ x) ∧ GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ ψ' = ψ := by
  intro p _ k _ _ hk A _ _ hab σ hσ ψ m hm
  haveI : IsAbelianScheme A := hab
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hk
  haveI : AlgebraicGeometry.IsIntegral A.left := GlobalTheory.isIntegral_left_of_isAbelianScheme_field A hab
  haveI : Smooth A.hom := IsAbelianScheme.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k A hab
  have hLie : LieExact A := (GlobalTheory.abelianDeRham.2.1 k A g hab hg).1
  have hT : ∀ v : epsR k ⟶ A, IsTangent v → IsConst (v.left ≫ ψ) := by
    intro v hv
    refine (tan k A hab σ ψ m hσ.2 v hv).mp ?_
    intro f hf
    obtain ⟨h, hh⟩ := hLie.2 v hv
    have hcl : Form.cl _ ((GrpMor.isMor m).pullForm f) = 0 := by
      rw [IsMor.cl_pullForm]
      have hF : (⟨Form.cl _ f, hf⟩ : primDR A) ∈ PrimitiveSubmodule A := by
        show Form.cl _ f ∈ F1 _
        rw [hodgeFiltration_eq_range]
        exact ⟨f, rfl⟩
      exact congrArg Subtype.val (hm _ hF)
    have hmem : Form.cl _ ((GrpMor.isMor m).pullForm f) ∈ primDR A := hcl ▸ (primDR A).zero_mem
    rw [← hh.2 _ hmem]
    have he : (⟨Form.cl _ ((GrpMor.isMor m).pullForm f), hmem⟩ : primDR A) = 0 := Subtype.ext hcl
    rw [he]
    exact map_zero h
  have hall := transl k A σ ψ m hT
  have hroot := dzero p k hk A.left A.left A.hom ψ (fun v hv => hall (Over.homMk v hv))
  obtain ⟨ψ', hψ'⟩ := root0 p A.left A.left (cast_left p k hk A) ψ hroot
  refine ⟨((frobeniusEquiv k p).symm : k →+* k).comp σ, ψ', ?_, ?_, ?_, hψ'⟩
  · exact (frobeniusEquiv k p).symm.bijective.comp hσ
  · exact rootMor p k hk A hab σ _ ψ ψ' m (fun x => frobeniusEquiv_symm_pow_p k p (σ x)) hψ'
  · exact fun x => frobeniusEquiv_symm_pow_p k p (σ x)
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private lemma tmul_p_mul (p : ℕ) (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] (l : k) (t : C) :
    l ⊗ₜ[ℤ] ((p : C) * t) = 0 := by
  have h1 : (p : C) * t = p • t := (nsmul_eq_mul p t).symm
  have h2 : (p • l : k) = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [h1, ← TensorProduct.smul_tmul, h2, TensorProduct.zero_tmul]

private lemma core (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] :
    ∃ (I : Type) (β : I → k),
      (∀ x : k ⊗[ℤ] C, ∃ c : I →₀ C, x = c.sum fun j d => β j ⊗ₜ[ℤ] d) ∧
      (∀ (s : Finset I) (c : I → C), ∑ j ∈ s, β j ⊗ₜ[ℤ] c j = 0 → ∀ j ∈ s, (p : C) ∣ c j) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let B := Module.Basis.ofVectorSpace (ZMod p) k
  let J : Ideal C := Ideal.span {(p : C)}
  have hpJ : (Int.castAddHom (C ⧸ J)) (p : ℤ) = 0 := by
    show ((p : ℤ) : C ⧸ J) = 0
    rw [Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  let φ : ZMod p →+ C ⧸ J := ZMod.lift p ⟨Int.castAddHom (C ⧸ J), hpJ⟩
  have hφ1 : φ 1 = 1 := by
    have h1 := ZMod.lift_coe p ⟨Int.castAddHom (C ⧸ J), hpJ⟩ (1 : ℤ)
    simpa using h1
  refine ⟨_, B, ?_, ?_⟩
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l t =>
      refine ⟨(B.repr l).mapRange (fun r => ((r.val : ℕ) : C) * t) (by simp), ?_⟩
      rw [Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _)]
      have hl := B.linearCombination_repr l
      rw [Finsupp.linearCombination_apply] at hl
      conv_lhs => rw [← hl]
      rw [Finsupp.sum, Finsupp.sum, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hs : (B.repr l j) • B j = (B.repr l j).val • B j := by
        conv_lhs => rw [← ZMod.natCast_zmod_val (B.repr l j)]
        rw [Nat.cast_smul_eq_nsmul]
      rw [hs, TensorProduct.smul_tmul, nsmul_eq_mul]
    | add x y hx hy =>
      obtain ⟨c1, rfl⟩ := hx
      obtain ⟨c2, rfl⟩ := hy
      exact ⟨c1 + c2, by rw [Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) (fun _ _ _ => TensorProduct.tmul_add _ _ _)]⟩
  · intro s c hs j hj
    let L : k →ₗ[ℤ] C →ₗ[ℤ] C ⧸ J := LinearMap.mk₂ ℤ (fun l t => φ (B.repr l j) * Ideal.Quotient.mk J t)
      (by intros; simp [add_mul])
      (by intro n m t; rw [map_zsmul, Finsupp.smul_apply, map_zsmul, smul_mul_assoc])
      (by intros; simp [mul_add])
      (by intro n m t; rw [map_zsmul, mul_smul_comm])
    have h0 := congrArg (TensorProduct.lift L) hs
    rw [map_sum, map_zero] at h0
    have step : ∀ i ∈ s, TensorProduct.lift L (B i ⊗ₜ[ℤ] c i) = if i = j then Ideal.Quotient.mk J (c i) else 0 := by
      intro i _
      rw [TensorProduct.lift.tmul]
      by_cases h : i = j
      · subst h; simp [L, hφ1]
      · simp [L, h, Finsupp.single_apply]
    rw [Finset.sum_congr rfl step, Finset.sum_ite_eq' s j, if_pos hj, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact Ideal.mem_span_singleton.mp h0

private lemma exact1 {R : Type} [CommRing R] (g a b : R) (h : ∀ x : R, g * x = 0 → ∃ u v, x = a * u + b * v)
    {M : Type 1} [AddCommGroup M] [Module R M] [Module.Projective R M] (x : M) (hx : g • x = 0) :
    ∃ u v : M, x = a • u + b • v := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  have hy : ∀ m, g * s x m = 0 := by
    intro m
    have h0 : s (g • x) = 0 := by rw [hx, map_zero]
    rw [map_smul] at h0
    have h1 := congrArg (fun y => y m) h0
    simpa using h1
  choose u v huv using fun m => h _ (hy m)
  refine ⟨∑ m ∈ (s x).support, u m • m, ∑ m ∈ (s x).support, v m • m, ?_⟩
  have hx' := hs x
  rw [Finsupp.linearCombination_apply] at hx'
  conv_lhs => rw [← hx']
  rw [Finsupp.sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [huv m, add_smul, mul_smul, mul_smul]
  rfl

private lemma exact2 {R : Type} [CommRing R] (e g a : R) (h : ∀ x : R, a * x = 0 → ∃ u, e * x = g * u)
    {M : Type 1} [AddCommGroup M] [Module R M] [Module.Projective R M] (x : M) (hx : a • x = 0) :
    ∃ u : M, e • x = g • u := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  have hy : ∀ m, a * s x m = 0 := by
    intro m
    have h0 : s (a • x) = 0 := by rw [hx, map_zero]
    rw [map_smul] at h0
    have h1 := congrArg (fun y => y m) h0
    simpa using h1
  choose u hu using fun m => h _ (hy m)
  refine ⟨∑ m ∈ (s x).support, u m • m, ?_⟩
  have hx' := hs x
  rw [Finsupp.linearCombination_apply] at hx'
  conv_lhs => rw [← hx']
  rw [Finsupp.sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_smul, hu m, mul_smul]
  rfl

theorem UpperTheory.Gal.Ord.proj :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] (w : Ideal C) (f : ℕ) (π : Par p w f)
      (M : Type 1) [AddCommGroup M] [Module (k ⊗[ℤ] C) M] [Module.Projective (k ⊗[ℤ] C) M],
      (∀ x : M, ((1 : k) ⊗ₜ[ℤ] π.g) • x = 0 → ∃ u v : M, x = ((1 : k) ⊗ₜ[ℤ] π.a) • u + ((1 : k) ⊗ₜ[ℤ] (1 - π.ε)) • v) ∧
      ∀ x : M, ((1 : k) ⊗ₜ[ℤ] π.a) • x = 0 → ∃ u : M, ((1 : k) ⊗ₜ[ℤ] π.ε) • x = ((1 : k) ⊗ₜ[ℤ] π.g) • u := by
  intro p _ k _ _ C _ w f π M _ _ _
  obtain ⟨I, β, hspan, hind⟩ := core p k C
  constructor
  · intro x hx
    refine exact1 _ _ _ ?_ x hx
    intro y hy
    obtain ⟨c, rfl⟩ := hspan y
    rw [Finsupp.sum, Finset.mul_sum] at hy
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul] at hy
    have key : ∀ j ∈ c.support, (p : C) ∣ π.g * c j := hind c.support (fun j => π.g * c j) hy
    choose! u v hd using fun j (hj : j ∈ c.support) => π.annG (c j) (key j hj)
    refine ⟨∑ j ∈ c.support, β j ⊗ₜ[ℤ] u j, ∑ j ∈ c.support, β j ⊗ₜ[ℤ] v j, ?_⟩
    rw [Finsupp.sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨t, ht⟩ := hd j hj
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← TensorProduct.tmul_add]
    have hc : c j = π.a * u j + (1 - π.ε) * v j + p * t := by rw [← ht]; ring
    rw [hc, TensorProduct.tmul_add, tmul_p_mul p k C, add_zero]
  · intro x hx
    refine exact2 _ _ _ ?_ x hx
    intro y hy
    obtain ⟨c, rfl⟩ := hspan y
    rw [Finsupp.sum, Finset.mul_sum] at hy
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul] at hy
    have key : ∀ j ∈ c.support, (p : C) ∣ π.a * c j := hind c.support (fun j => π.a * c j) hy
    choose! u hd using fun j (hj : j ∈ c.support) => π.annA (c j) (key j hj)
    refine ⟨∑ j ∈ c.support, β j ⊗ₜ[ℤ] u j, ?_⟩
    rw [Finsupp.sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨t, ht⟩ := hd j hj
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
    have hc : π.ε * c j = π.g * u j + p * t := by rw [← ht]; ring
    rw [hc, TensorProduct.tmul_add, tmul_p_mul p k C, add_zero]
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.Ord.DimsAlg

variable {k : Type} [Field k] {C : Type} [CommRing C]

private abbrev W (ν : C → k) : Submodule k (k ⊗[ℤ] C) :=
  ⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (ν c)

private theorem mem_W (ν : C → k) (x : k ⊗[ℤ] C) :
    x ∈ W ν ↔ ∀ c : C, ∃ n : ℕ, (((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) ^ n) * x = 0 := by
  simp only [W, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace]
  refine forall_congr' fun c => exists_congr fun n => ?_
  have h : (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c - ν c • (1 : Module.End k (k ⊗[ℤ] C)))
      = Algebra.lmul k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) := by
    have : ν c ⊗ₜ[ℤ] (1 : C) = ν c • (1 : k ⊗[ℤ] C) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_sub, map_smul, map_one]
    rfl
  rw [h, ← map_pow]
  rfl

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

private def frobZ : k ≃ₐ[ℤ] k := AlgEquiv.ofRingEquiv (f := frobeniusEquiv k p) (fun n => by simp)

private def E : (k ⊗[ℤ] C) ≃ₐ[ℤ] (k ⊗[ℤ] C) := Algebra.TensorProduct.congr (frobZ (k := k) p) AlgEquiv.refl

private theorem E_tmul (l : k) (c : C) : E p (l ⊗ₜ[ℤ] c) = (l ^ p) ⊗ₜ[ℤ] c := by
  simp [E, frobZ, frobenius_def]

private theorem E_smul (l : k) (x : k ⊗[ℤ] C) : E p (l • x) = l ^ p • E p x := by
  induction x with
  | zero => simp
  | tmul a c => simp [TensorProduct.smul_tmul', E_tmul, mul_pow]
  | add x y hx hy => simp [smul_add, hx, hy]

private theorem E_mem (ν : C → k) (x : k ⊗[ℤ] C) : E p x ∈ W (fun c => ν c ^ p) ↔ x ∈ W ν := by
  rw [mem_W, mem_W]
  refine forall_congr' fun c => exists_congr fun n => ?_
  have h : E p (((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) ^ n * x)
      = ((1 : k) ⊗ₜ[ℤ] c - (ν c ^ p) ⊗ₜ[ℤ] (1 : C)) ^ n * E p x := by
    rw [map_mul, map_pow, map_sub, E_tmul, E_tmul, one_pow]
  rw [← h]
  exact map_eq_zero_iff _ (E p).injective

private theorem finrank_W_pow (ν : C → k) :
    Module.finrank k ↥(W (fun c => ν c ^ p)) = Module.finrank k ↥(W ν) := by
  let j : ↥(W ν) ≃+ ↥(W (fun c => ν c ^ p)) :=
    { toFun := fun x => ⟨E p x.1, (E_mem p ν x.1).2 x.2⟩
      invFun := fun y => ⟨(E p).symm y.1, (E_mem p ν _).1 (by simpa using y.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hr := rank_eq_of_equiv_equiv (R := k) (R' := k) (M := ↥(W ν)) (M₁ := ↥(W (fun c => ν c ^ p)))
    (⟨fun l => l ^ p, by simp [(Fact.out : p.Prime).ne_zero]⟩ : ZeroHom k k) j
    (frobeniusEquiv k p).bijective (fun r m => Subtype.ext (E_smul p r m.1))
  exact (congrArg Cardinal.toNat hr).symm

end UpperTheory.Gal.Ord.DimsAlg

namespace UpperTheory.Gal.Ord.DimsCoh

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {k : Type} [Field k] {t : Sp k ⟶ Sp R}

private def cohHom (o : Obj b N t) : 𝓞 D.F →+* Module.End k (primDR o.A) :=
  RingHom.mk'
    { toFun := coh o
      map_one' := by
        haveI := o.act.hom
        refine LinearMap.ext fun x => ?_
        exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_id _ _ _ (by rw [map_one, o.act.one]) x
      map_mul' := fun x y => by
        haveI := o.act.hom
        refine LinearMap.ext fun c => ?_
        exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_comp _ _ _ _ _ (by rw [mul_comm x y, map_mul, o.act.mul]) c }
    fun x y => by
      haveI := o.act.hom
      refine LinearMap.ext fun c => ?_
      exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_mul _ _ _ _ _ (by rw [map_add, o.act.add]) c

end UpperTheory.Gal.Ord.DimsCoh

open UpperTheory.Gal.Ord.DimsAlg UpperTheory.Gal.Ord.DimsCoh in
theorem UpperTheory.Gal.Ord.dims :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ j : ℕ, Module.finrank k ↥(⨅ c, (coh o c).maxGenEigenspace (β (b.t i c) ^ p ^ j)) =
        Module.finrank k ↥(⨅ c, (coh o c).maxGenEigenspace (β (b.t i c))) := by
  intro p _ D R _ b N hN hNp _ k _ _ hk β o i w f _ _ _ π j
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o.A o.ab
  obtain ⟨hfd, -, -⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o.A g o.ab hg
  haveI := hfd
  haveI : Module.Finite k (primDR o.A) := (Module.finite_dual_iff k).1 hfd
  haveI := D.freeLa
  haveI := D.finLa
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hk
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out : p.Prime)).2 (by omega)
  have hcopj : ∀ j : ℕ, (l ^ j).Coprime p := fun j => Nat.Coprime.pow_left j hcop
  have hposj : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hl.pos j
  have hlk : (l : k) ≠ 0 := by
    have hu := (b.unit l hcop).map β
    rw [map_natCast] at hu
    exact hu.ne_zero
  obtain ⟨I, -⟩ := o.geom k (𝟙 _) β (by rw [Category.id_comp])
  have hc : ∀ c : 𝓞 D.F, LinearMap.charpoly (cohHom o c) =
      ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n)).map (Int.castRingHom k) := by
    intro c
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e := GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic k o.A o.ab (o.act.act (algebraMap (𝓞 D.F) D.O c)) D.La
      (DistribMulAction.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) l hl hlk (fun j => I.ev (l ^ j))
      (fun j x y => I.add (l ^ j) x y) (fun j x => I.lin (l ^ j) _ x)
      (fun j x => I.ker (l ^ j) (hposj j) (hcopj j) x) (fun j q => I.onto (l ^ j) (hposj j) (hcopj j) q)
    rw [GlobalTheory.T.charpoly_la_eq_pow p D c] at e
    rw [← e]
    exact (GlobalTheory.DeRhamCharpolyP.charpoly_dualMap _).symm
  have key := fun χ : 𝓞 D.F →+* k => GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly k (𝓞 D.F) ↥(primDR o.A) (cohHom o) (D.m * D.n) hc χ
  have e1 := key ((iterateFrobenius k p j).comp (β.comp (b.t i)))
  have e2 := key (β.comp (b.t i))
  have hW : ∀ (j : ℕ) , Module.finrank k ↥(W (C := 𝓞 D.F) (fun c => β (b.t i c) ^ p ^ j)) =
      Module.finrank k ↥(W (C := 𝓞 D.F) (fun c => β (b.t i c))) := by
    intro j
    induction j with
    | zero => exact congrArg (fun ν : 𝓞 D.F → k => Module.finrank k ↥(W ν)) (funext fun c => by simp)
    | succ j ih =>
      rw [← ih, ← finrank_W_pow p (fun c => β (b.t i c) ^ p ^ j)]
      exact congrArg (fun ν : 𝓞 D.F → k => Module.finrank k ↥(W ν)) (funext fun c => by rw [_root_.pow_succ, _root_.pow_mul])
  simp only [RingHom.comp_apply, iterateFrobenius_def] at e1 e2
  refine e1.trans (Eq.trans ?_ e2.symm)
  exact congrArg (D.m * D.n * ·) (hW j)
end
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord.LinPf

variable {k : Type} [Field k]

private theorem dual_annG {C P : Type*} [CommRing C] [AddCommGroup P] [Module k P]
    (ρ : C →+* Module.End k P) (a ε g : C)
    (h : ∀ x : Module.Dual k P, (ρ a).dualMap x = 0 → ∃ u, (ρ ε).dualMap x = (ρ g).dualMap u)
    (x : P) (hx : ρ g x = 0) : ∃ u v, x = ρ a u + ρ (1 - ε) v := by
  have hW : x ∈ LinearMap.range (ρ a) ⊔ LinearMap.range (ρ (1 - ε)) := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have h1 : (ρ a).dualMap φ = 0 :=
      LinearMap.ext fun y ↦ hφ _ (Submodule.mem_sup_left ⟨y, rfl⟩)
    have h2 : (ρ (1 - ε)).dualMap φ = 0 :=
      LinearMap.ext fun y ↦ hφ _ (Submodule.mem_sup_right ⟨y, rfl⟩)
    obtain ⟨u, hu⟩ := h φ h1
    have h3 : φ = (ρ ε).dualMap φ + (ρ (1 - ε)).dualMap φ := by
      refine LinearMap.ext fun y ↦ ?_
      have e : ρ ε y + ρ (1 - ε) y = y := by
        rw [map_sub, map_one]; simp
      rw [LinearMap.add_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply, ← map_add, e]
    rw [h3, h2, add_zero, hu, LinearMap.dualMap_apply, hx, map_zero]
  obtain ⟨y, ⟨u, rfl⟩, z, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 hW
  exact ⟨u, v, e.symm⟩

private theorem dual_annA {C P : Type*} [CommRing C] [AddCommGroup P] [Module k P]
    (ρ : C →+* Module.End k P) (a ε g : C) (hε : ρ ((1 - ε) * ε) = 0)
    (h : ∀ x : Module.Dual k P, (ρ g).dualMap x = 0 →
      ∃ u v, x = (ρ a).dualMap u + (ρ (1 - ε)).dualMap v)
    (x : P) (hx : ρ a x = 0) : ∃ u, ρ ε x = ρ g u := by
  have hW : ρ ε x ∈ LinearMap.range (ρ g) := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have h1 : (ρ g).dualMap φ = 0 := LinearMap.ext fun y ↦ hφ _ ⟨y, rfl⟩
    obtain ⟨u, v, rfl⟩ := h φ h1
    have e1 : ρ a (ρ ε x) = 0 := by
      have : ρ a * ρ ε = ρ ε * ρ a := by rw [← map_mul, ← map_mul, mul_comm]
      have := LinearMap.congr_fun this x
      simpa [hx] using this
    have e2 : ρ (1 - ε) (ρ ε x) = 0 := by
      have : ρ (1 - ε) * ρ ε = 0 := by rw [← map_mul, hε]
      exact LinearMap.congr_fun this x
    rw [LinearMap.add_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply, e1, e2, map_zero,
      map_zero, add_zero]
  obtain ⟨u, hu⟩ := hW
  exact ⟨u, hu.symm⟩

variable {p : ℕ} [Fact p.Prime]

private theorem frob_of_mem (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A)
    (c : primDR A) (hc : c ∈ PrimitiveSubmodule A) : frobDR p k hk A c = 0 := by
  letI : Algebra k k := (frobR p k hk).toAlgebra
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k A hA
  have hπ := isGrpPullback_pullback A (spMap (frobR p k hk))
  obtain ⟨F, hFm, hF⟩ := GlobalTheory.T.exists_relativeFrobenius_grpScheme_charP p k hk A _ _ hπ
  have hker := (GlobalTheory.T.range_relativeFrobenius_primitiveDeRham_eq_conjugate GlobalTheory.abelianDeRham.2.2.1 p k hk A _ _ hπ F hF g hA hg).2
  let m := GlobalTheory.Published.AbelianDeRham.bcMor hπ
  have e : primPull (dp0 k) (𝟙 _) F (m.pull c) = frobDR p k hk A c :=
    GrpMor.pull_pull m (homMor (dp0 k) (𝟙 _) F) (frobMor p k hk A (cast_left p k hk A))
      (fun _ ↦ rfl) hF c
  rw [← e]
  exact hker (m.isMor.pullback1_mem_hodgeFiltration hc)

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {t : Sp k ⟶ Sp R}

private theorem hom_apply (o : Obj b N t) (c : 𝓞 D.F) (h : HdR o.A) (x : primDR o.A) :
    hom o c h x = h (coh o c x) := rfl

private theorem sep (o : Obj b N t) {x y : primDR o.A} (e : ∀ h : HdR o.A, h x = h y) : x = y := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k]
  intro h
  have := e h
  rw [map_sub, sub_eq_zero]
  exact this

private theorem hom_add (o : Obj b N t) (x y : 𝓞 D.F) : hom o (x + y) = hom o x + hom o y := by
  simp only [hom, map_add]

private theorem hom_mul (o : Obj b N t) (x y : 𝓞 D.F) : hom o (x * y) = hom o x * hom o y := by
  simp only [hom, map_mul]

private theorem hom_one (o : Obj b N t) : hom o 1 = 1 := by
  simp only [hom, map_one]

private noncomputable def cohHom (o : Obj b N t) : 𝓞 D.F →+* Module.End k (primDR o.A) where
  toFun := coh o
  map_one' := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [← hom_apply, hom_one]; rfl
  map_mul' x y := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [mul_comm x y, ← hom_apply, hom_mul]; rfl
  map_zero' := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [← hom_apply]; simp [hom]
  map_add' x y := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [← hom_apply, hom_add, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, map_add]; rfl



private theorem cohHom_natCast_zero (hk : (p : k) = 0) (o : Obj b N t) : cohHom o (p : 𝓞 D.F) = 0 := by
  rw [map_natCast, ← map_natCast (algebraMap k (Module.End k (primDR o.A))) p, hk, map_zero]

end UpperTheory.Gal.Ord.LinPf

open UpperTheory.Gal.Ord.LinPf in
theorem UpperTheory.Gal.Ord.lin :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      Lin p π (β.comp (b.t i)) (coh o) (PrimitiveSubmodule o.A) (frobDR p k hk o.A).toAddMonoidHom := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hn hf π
  obtain ⟨h1, ⟨h₀, h2, h3⟩, -⟩ := UpperTheory.Gal.Ord.lie p D R b N hN hNp hm k hk β o i w f hw hn hf π
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hk
  letI := tensorModule (dp0 k) (𝟙 _) (o.act.toF D)
  have hP := GlobalTheory.CrysProj.hdR_projective D.F k o.A o.ab (o.act.toF D)
  obtain ⟨hG, hA⟩ := UpperTheory.Gal.Ord.proj p k (𝓞 D.F) w f π (HdR o.A)
  have hs : ∀ (c : 𝓞 D.F) (x : HdR o.A), ((1 : k) ⊗ₜ[ℤ] c) • x = (cohHom o c).dualMap x := fun c x ↦ by
    change actAlg (dp0 k) (𝟙 _) (o.act.toF D) ((1 : k) ⊗ₜ[ℤ] c) x = _
    rw [actAlg_tmul, one_smul]
    rfl
  have hε : cohHom o ((1 - π.ε) * π.ε) = 0 := by
    obtain ⟨u, hu⟩ := π.idem
    have e : (1 - π.ε) * π.ε = (p : 𝓞 D.F) * (-u) := by
      linear_combination -hu
    rw [e, map_mul, cohHom_natCast_zero hk, zero_mul]
  refine
    { fin := ?_
      add := fun x y ↦ (cohHom o).map_add x y
      mul := fun x y ↦ (cohHom o).map_mul x y
      one := (cohHom o).map_one
      ker := hw
      semi := fun l x ↦ ?_
      comm := fun c x ↦ ?_
      kerΦ := fun x ↦ ⟨fun h ↦ GlobalTheory.T.frobenius_kernel_primitive_de_rham_hodge p k hk o.A o.ab x h, fun h ↦ frob_of_mem hk o.A o.ab x h⟩
      stab := fun c x hx ↦ ?_
      eig := fun c x hx ↦ ?_
      line := ?_
      annG := fun x hx ↦ ?_
      annA := fun x hx ↦ ?_
      dims := UpperTheory.Gal.Ord.dims p D R b N hN hNp hm k hk β o i w f hw hn hf π }
  · obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o.A o.ab
    have H := GlobalTheory.abelianDeRham
    obtain ⟨hfd, -, -⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o.A g o.ab hg
    exact Module.finite_dual_iff k |>.1 hfd
  · change frobDR p k hk o.A (l • x) = l ^ p • frobDR p k hk o.A x
    rw [LinearMap.map_smulₛₗ, frobR_apply]
  · haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    exact GlobalTheory.AbDatum.frobDR_primPull p hk _ x
  · haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    exact (homMor (dp0 k) (𝟙 _) (o.act.act (algebraMap (𝓞 D.F) D.O c))).isMor.pullback1_mem_hodgeFiltration hx
  · refine sep o fun h ↦ ?_
    have e := (Submodule.mem_dualAnnihilator _).1 (h1 c h) x hx
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hom_apply, hom_apply, hom_apply, smul_eq_mul,
      sub_eq_zero] at e
    have ec : coh o c (coh o π.ε x) = coh o π.ε (coh o c x) := by
      have := LinearMap.congr_fun ((cohHom o).map_mul c π.ε) x
      rw [mul_comm, (cohHom o).map_mul] at this
      exact this.symm
    rw [ec, map_smul, e]
    rfl
  · have hx₀ : ∃ x ∈ PrimitiveSubmodule o.A, hom o π.ε h₀ x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h2 ((Submodule.mem_dualAnnihilator _).2 hc)
    obtain ⟨x, hx, hne⟩ := hx₀
    rw [hom_apply] at hne
    refine ⟨x, hx, fun e ↦ hne (by rw [e, map_zero]), fun y hy ↦ ?_⟩
    refine ⟨h₀ (coh o π.ε y) / h₀ (coh o π.ε x), sep o fun h ↦ ?_⟩
    obtain ⟨m, hm⟩ := h3 h
    have ey := (Submodule.mem_dualAnnihilator _).1 hm y hy
    have ex := (Submodule.mem_dualAnnihilator _).1 hm x hx
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hom_apply, hom_apply, smul_eq_mul,
      sub_eq_zero] at ey ex
    rw [map_smul, ey, ex, smul_eq_mul]
    field_simp
  · refine dual_annG (cohHom o) π.a π.ε π.g (fun y hy ↦ ?_) x hx
    obtain ⟨u, hu⟩ := hA y (by rw [hs]; exact hy)
    exact ⟨u, by rw [← hs, ← hs]; exact hu⟩
  · refine dual_annA (cohHom o) π.a π.ε π.g hε (fun y hy ↦ ?_) x hx
    obtain ⟨u, v, huv⟩ := hG y (by rw [hs]; exact hy)
    exact ⟨u, v, by rw [← hs, ← hs]; exact huv⟩
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

section Va

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

private theorem frobN_nat (X : Scheme.{0}) (h : (p : Γ(X, ⊤)) = 0) (f : X ⟶ X) (j : ℕ) :
    frobN p X h j ≫ f = f ≫ frobN p X h j := by
  induction j with
  | zero => exact (Category.id_comp f).trans (Category.comp_id f).symm
  | succ j ih =>
    show (GlobalTheory.VB.frob X p h ≫ frobN p X h j) ≫ f = f ≫ GlobalTheory.VB.frob X p h ≫ frobN p X h j
    rw [Category.assoc, ih, ← Category.assoc, GlobalTheory.VB.frob_naturality p h f h, Category.assoc]

private theorem frobN_succ' (X : Scheme.{0}) (h : (p : Γ(X, ⊤)) = 0) (j : ℕ) :
    frobN p X h (j + 1) = frobN p X h j ≫ GlobalTheory.VB.frob X p h := by
  show GlobalTheory.VB.frob X p h ≫ frobN p X h j = _
  exact (frobN_nat X h _ j).symm

private theorem smor_comp {A : Over (Sp k)} [GrpObj A] {σ τ : k →+* k} {ψ φ : A.left ⟶ A.left}
    (m : SMor A σ ψ) (n : SMor A τ φ) : SMor A (τ.comp σ) (φ ≫ ψ) := by
  have hc := GrpMor.comp m n
  rwa [← GlobalTheory.Cris.spMap_comp] at hc

private noncomputable def rho {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C) :
    Module.End k (primDR A) :=
  haveI := i.hom c
  primPull (dp0 k) (𝟙 _) (i.act c)

private theorem smor_act {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C) :
    SMor A (RingHom.id k) (i.act c).left := by
  haveI := i.hom c
  have hc := homMor (dp0 k) (𝟙 (Sp k)) (i.act c)
  unfold SMor
  rw [spMap_id]
  exact hc

private theorem pull_act {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C)
    (m : SMor A (RingHom.id k) (i.act c).left) (x : primDR A) : m.pull x = rho i c x := rfl

private theorem pull_rho {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C)
    {σ : k →+* k} {ψ : A.left ⟶ A.left} (m : SMor A σ ψ) (M : SMor A σ (ψ ≫ (i.act c).left))
    (x : primDR A) : m.pull (rho i c x) = M.pull x :=
  haveI := i.hom c
  GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) (i.act c)) m M (fun _ => rfl) rfl x

private theorem rho_pull {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C)
    {σ : k →+* k} {ψ : A.left ⟶ A.left} (m : SMor A σ ψ) (M : SMor A σ ((i.act c).left ≫ ψ))
    (x : primDR A) : rho i c (m.pull x) = M.pull x :=
  haveI := i.hom c
  GrpMor.pull_pull m (homMor (dp0 k) (𝟙 _) (i.act c)) M (fun _ => rfl) rfl x

private theorem card_bound {C : Type} [CommRing C] (χ : C →+* k) {f j : ℕ}
    (hN : Nat.card (C ⧸ RingHom.ker χ) = p ^ f) (hj0 : 0 < j) (hjf : j < f)
    (hc : ∀ c, χ c ^ p ^ j = χ c) : False := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hq : 1 < p ^ j := Nat.one_lt_pow hj0.ne' hp1
  have hcard : Nat.card χ.range = p ^ f := by
    rw [← hN]
    exact Nat.card_congr (RingHom.quotientKerEquivRange χ).toEquiv.symm
  have hfin : Finite χ.range := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hS : (χ.range : Set k).Finite := Set.finite_coe_iff.mp hfin
  have hZ : hS.toFinset.card = p ^ f := by
    rw [← Set.ncard_eq_toFinset_card _ hS, ← Nat.card_coe_set_eq]
    exact hcard
  have hsub : hS.toFinset.val ⊆ (Polynomial.X ^ (p ^ j) - Polynomial.X : Polynomial k).roots := by
    intro x hx
    have hx' : x ∈ (χ.range : Set k) := by
      rw [Finset.mem_val, Set.Finite.mem_toFinset] at hx
      exact hx
    obtain ⟨c, rfl⟩ := RingHom.mem_range.mp hx'
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero k hq)]
    simp [hc c]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hq, hZ] at hle
  exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right hp1 hjf))

private theorem rho_ringHom {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] {w : Ideal C} {f : ℕ}
    {π : Par p w f} {χ : C →+* k} {i : OAct C A} {F : Submodule k (primDR A)} {Φ : primDR A →+ primDR A}
    (hL : Lin p π χ (rho i) F Φ) (hk : (p : k) = 0) (c : C) (x : primDR A) :
    rho i ((p : C) * c) x = 0 := by
  have hn : ∀ n : ℕ, rho i (n : C) = (n : Module.End k (primDR A)) := by
    intro n
    induction n with
    | zero =>
      have h0 := hL.add 0 0
      simp only [add_zero] at h0
      simpa using h0
    | succ n ih => rw [Nat.cast_succ, hL.add, ih, hL.one, Nat.cast_succ]
  rw [hL.mul, Module.End.mul_apply, hn, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul k, hk,
    zero_smul]

private theorem sig_eq (hk : (p : k) = 0) {j : ℕ} {σ τ : k →+* k} (h1 : ∀ x, σ x ^ p ^ j = x)
    (h2 : ∀ x, τ x ^ p ^ j = x) : τ = σ := by
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hk
  haveI : ExpChar k p := ExpChar.prime Fact.out
  ext x
  apply (iterateFrobenius k p j).injective
  simp only [iterateFrobenius_def]
  rw [h1, h2]

private theorem pull_congr {A : Over (Sp k)} [GrpObj A] {σ : k →+* k} {ψ ψ' : A.left ⟶ A.left}
    (e : ψ = ψ') (m : SMor A σ ψ) (m' : SMor A σ ψ') (x : primDR A) : m.pull x = m'.pull x := by
  subst e; rfl

private theorem smor_right {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C)
    {σ : k →+* k} {ψ : A.left ⟶ A.left} (m : SMor A σ ψ) : SMor A σ (ψ ≫ (i.act c).left) := by
  haveI := i.hom c
  have hc := GrpMor.comp (homMor (dp0 k) (𝟙 (Sp k)) (i.act c)) m
  rwa [RingHom.comp_id, Category.comp_id] at hc

private theorem smor_left {A : Over (Sp k)} [GrpObj A] {C : Type} [CommRing C] (i : OAct C A) (c : C)
    {σ : k →+* k} {ψ : A.left ⟶ A.left} (m : SMor A σ ψ) : SMor A σ ((i.act c).left ≫ ψ) := by
  haveI := i.hom c
  have hc := GrpMor.comp m (homMor (dp0 k) (𝟙 (Sp k)) (i.act c))
  rwa [RingHom.id_comp, Category.id_comp] at hc

private theorem frob_pull (hk : (p : k) = 0) {A : Over (Sp k)} [GrpObj A] {σ : k →+* k}
    {ψ : A.left ⟶ A.left} (m : SMor A σ ψ) (z : primDR A) :
    frobDR p k hk A (m.pull z) = m.pull (frobDR p k hk A z) := by
  have F := frobMor p k hk A (cast_left p k hk A)
  have M := GrpMor.comp F m
  have e1 := GrpMor.pull_pull m F M
    (fun r => by simp only [RingHom.comp_apply, frobR_apply, map_pow])
    (GlobalTheory.VB.frob_naturality p _ ψ _) z
  have e2 := GrpMor.pull_pull F m M (fun _ => rfl) rfl z
  exact e1.trans e2.symm

private theorem kill (hk : (p : k) = 0) {A : Over (Sp k)} [GrpObj A] [IsReduced A.left]
    {C : Type} [CommRing C] {w : Ideal C} {f : ℕ} (π : Par p w f) {χ : C →+* k} (i : OAct C A)
    (hL : Lin p π χ (rho i) (PrimitiveSubmodule A) (frobDR p k hk A).toAddMonoidHom)
    (hN : Nat.card (C ⧸ RingHom.ker χ) = p ^ f) {j : ℕ} (hjf : j < f)
    {σ τ : k →+* k} {ψ V : A.left ⟶ A.left} (m : SMor A σ ψ) (n : SMor A τ V)
    (hσ : ∀ x, σ x ^ p ^ j = x) (hτ : ∀ x, τ x ^ p ^ j = x)
    (ha : frobN p A.left (cast_left p k hk A) j ≫ ψ = (i.act π.a).left)
    (hV : frobN p A.left (cast_left p k hk A) j ≫ V = (i.act ((p : C) ^ j)).left) :
    ∀ x ∈ PrimitiveSubmodule A, m.pull x = 0 := by
  have hst : σ = τ := (sig_eq hk hσ hτ).symm
  subst hst
  haveI := (UpperTheory.Gal.Ord.epi p A.left (cast_left p k hk A)).2 j
  have hcomm : ∀ c : C, (i.act c).left ≫ ψ = ψ ≫ (i.act c).left := by
    intro c
    apply Epi.left_cancellation (f := frobN p A.left (cast_left p k hk A) j)
    rw [← Category.assoc, frobN_nat A.left (cast_left p k hk A) (i.act c).left j, Category.assoc, ha,
      ← Category.assoc, ha, ← Over.comp_left, ← Over.comp_left, ← i.mul, ← i.mul, mul_comm c π.a]
  have hcom' : ∀ (c : C) (y : primDR A), rho i c (m.pull y) = m.pull (rho i c y) := by
    intro c y
    rw [rho_pull i c m (smor_left i c m) y, pull_rho i c m (smor_right i c m) y]
    exact pull_congr (hcomm c) _ _ y
  intro x hx
  have h2 : m.pull (rho i (1 - π.ε) x) = 0 := by
    have hpow : (p : C) ^ f * π.s = (p : C) ^ j * ((p : C) * ((p : C) ^ (f - j - 1) * π.s)) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← pow_succ, ← pow_add, show j + 1 + (f - j - 1) = f by omega]
    have e : ψ ≫ (i.act (1 - π.ε)).left = V ≫ (i.act ((p : C) * ((p : C) ^ (f - j - 1) * π.s))).left := by
      apply Epi.left_cancellation (f := frobN p A.left (cast_left p k hk A) j)
      rw [← Category.assoc, ha, ← Category.assoc, hV, ← Over.comp_left, ← Over.comp_left, ← i.mul,
        ← i.mul, π.away, hpow]
    rw [pull_rho i _ m (smor_right i (1 - π.ε) m) x,
      pull_congr e (smor_right i (1 - π.ε) m) (smor_right i ((p : C) * ((p : C) ^ (f - j - 1) * π.s)) n) x,
      ← pull_rho i _ n (smor_right i ((p : C) * ((p : C) ^ (f - j - 1) * π.s)) n) x,
      rho_ringHom hL hk _ x, map_zero]
  have h1 : m.pull (rho i π.ε x) = 0 := by
    by_cases hj : j = 0
    · subst hj
      have hσid : σ = RingHom.id k := RingHom.ext fun y => by simpa using hσ y
      subst hσid
      have hψ : ψ = (i.act π.a).left := (Category.id_comp ψ).symm.trans ha
      have hχa : χ π.a = 0 := by
        rw [← RingHom.mem_ker, hL.ker]
        exact π.mem
      rw [pull_congr hψ m (smor_act i π.a) _, pull_act i π.a (smor_act i π.a) _, hL.eig π.a x hx, hχa,
        zero_smul]
    · have hj0 : 0 < j := Nat.pos_of_ne_zero hj
      by_contra hne
      have hu : rho i π.ε x ∈ PrimitiveSubmodule A := hL.stab π.ε x hx
      have hu'F : m.pull (rho i π.ε x) ∈ PrimitiveSubmodule A := by
        rw [← hL.kerΦ]
        show frobDR p k hk A (m.pull (rho i π.ε x)) = 0
        rw [frob_pull hk m _]
        have h0 : frobDR p k hk A (rho i π.ε x) = 0 := (hL.kerΦ _).mpr hu
        rw [h0, map_zero]
      have hεu : rho i π.ε (m.pull (rho i π.ε x)) = m.pull (rho i π.ε x) := by
        rw [hcom', ← Module.End.mul_apply, ← hL.mul]
        obtain ⟨t, ht⟩ := π.idem
        have hee : π.ε * π.ε = (p : C) * t + π.ε := by rw [← ht]; ring
        rw [hee, hL.add, LinearMap.add_apply, rho_ringHom hL hk t x, zero_add]
      apply card_bound χ hN hj0 hjf
      intro c
      have h1c : rho i c (m.pull (rho i π.ε x)) = χ c • m.pull (rho i π.ε x) := by
        have h3 := hL.eig c _ hu'F
        rwa [hεu] at h3
      have h2c : rho i c (m.pull (rho i π.ε x)) = σ (χ c) • m.pull (rho i π.ε x) := by
        rw [hcom', hL.eig c x hx, map_smulₛₗ]
      have hsame : σ (χ c) = χ c := smul_left_injective k hne (h2c.symm.trans h1c)
      calc χ c ^ p ^ j = σ (χ c) ^ p ^ j := by rw [hsame]
        _ = χ c := hσ _
  have hdec : x = rho i π.ε x + rho i (1 - π.ε) x := by
    rw [← LinearMap.add_apply, ← hL.add, add_sub_cancel, hL.one, Module.End.one_apply]
  rw [hdec, map_add, h1, h2, add_zero]

private theorem vRoot [IsAlgClosed k] (hk : (p : k) = 0) {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A]
    (hab : IsAbelianScheme A) {C : Type} [CommRing C] {w : Ideal C} {f : ℕ} (π : Par p w f)
    {χ : C →+* k} (i : OAct C A)
    (hL : Lin p π χ (rho i) (PrimitiveSubmodule A) (frobDR p k hk A).toAddMonoidHom) (j : ℕ) :
    ∃ (τ : k →+* k) (V : A.left ⟶ A.left), SMor A τ V ∧ (∀ x, τ x ^ p ^ j = x) ∧
      frobN p A.left (cast_left p k hk A) j ≫ V = (i.act ((p : C) ^ j)).left := by
  induction j with
  | zero =>
    refine ⟨RingHom.id k, (i.act 1).left, smor_act i 1, fun x => by simp, ?_⟩
    rw [pow_zero]
    exact Category.id_comp _
  | succ j ih =>
    obtain ⟨τ, V, n, hτ, hV⟩ := ih
    obtain ⟨σ1, ψ1, -, m1, hσ1, hψ1⟩ := root p k hk A hab (RingHom.id k) Function.bijective_id
      ((i.act (p : C)).left) (smor_act i (p : C)) (fun x _ => by
        rw [pull_act i _ (smor_act i (p : C)) x]
        have h0 := rho_ringHom hL hk 1 x
        rwa [_root_.mul_one] at h0)
    refine ⟨τ.comp σ1, V ≫ ψ1, smor_comp m1 n, fun x => ?_, ?_⟩
    · rw [RingHom.comp_apply, pow_succ', pow_mul, ← map_pow, hσ1, RingHom.id_apply, hτ]
    · rw [frobN_succ', Category.assoc, ← Category.assoc (GlobalTheory.VB.frob _ p _) V,
        GlobalTheory.VB.frob_naturality p (cast_left p k hk A) V (cast_left p k hk A), Category.assoc, hψ1,
        ← Category.assoc, hV, pow_succ, i.mul, Over.comp_left]

private theorem vaGen [IsAlgClosed k] (hk : (p : k) = 0) {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A]
    (hab : IsAbelianScheme A) {C : Type} [CommRing C] {w : Ideal C} {f : ℕ} (π : Par p w f)
    {χ : C →+* k} (i : OAct C A)
    (hL : Lin p π χ (rho i) (PrimitiveSubmodule A) (frobDR p k hk A).toAddMonoidHom)
    (hN : Nat.card (C ⧸ RingHom.ker χ) = p ^ f) :
    ∃ (σ : k →+* k) (ψ : A.left ⟶ A.left), Function.Bijective σ ∧ SMor A σ ψ ∧
      frobN p A.left (cast_left p k hk A) f ≫ ψ = (i.act π.a).left := by
  haveI : Smooth A.hom := IsAbelianScheme.smooth (self := hab)
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have key : ∀ j ≤ f, ∃ (σ : k →+* k) (ψ : A.left ⟶ A.left), Function.Bijective σ ∧ SMor A σ ψ ∧
      (∀ x, σ x ^ p ^ j = x) ∧ frobN p A.left (cast_left p k hk A) j ≫ ψ = (i.act π.a).left := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨RingHom.id k, (i.act π.a).left, Function.bijective_id, smor_act i π.a,
        fun x => by simp, Category.id_comp _⟩
    | succ j ih =>
      intro hj
      obtain ⟨σ, ψ, hσb, m, hσ, hψ⟩ := ih (by omega)
      obtain ⟨τ, V, n, hτ, hV⟩ := vRoot hk hab π i hL j
      have hk0 := kill hk π i hL hN (by omega : j < f) m n hσ hτ hψ hV
      obtain ⟨σ', ψ', hb', m', hσ', hψ'⟩ := root p k hk A hab σ hσb ψ m hk0
      refine ⟨σ', ψ', hb', m', fun x => ?_, ?_⟩
      · rw [pow_succ', pow_mul, hσ', hσ]
      · rw [frobN_succ', Category.assoc, hψ', hψ]
  obtain ⟨σ, ψ, hb, m, -, hψ⟩ := key f le_rfl
  exact ⟨σ, ψ, hb, m, hψ⟩

end Va

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.va :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∃ (σ : k →+* k) (ψ : o.A.left ⟶ o.A.left), Function.Bijective σ ∧ SMor o.A σ ψ ∧ frobN p o.A.left (cast_left p k hk o.A) f ≫ ψ = (o.act.act (algebraMap (𝓞 D.F) D.O π.a)).left := by
  intro p _ D R _ b N hN3 hNp hm k _ _ hk β o i w f hker hnorm hf π
  have hL := UpperTheory.Gal.Ord.lin p D R b N hN3 hNp hm k hk β o i w f hker hnorm hf π
  have hC : Nat.card (𝓞 D.F ⧸ RingHom.ker (β.comp (b.t i))) = p ^ f := by
    rw [hker, ← hnorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact vaGen hk o.ab π (o.act.toF D) hL hC
end
