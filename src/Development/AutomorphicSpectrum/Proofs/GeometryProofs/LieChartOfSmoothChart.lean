import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.AmpleLineBundles.SquareZeroDeformationAdditivity

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanChart

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem spMap_fromSpec_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) {D : Type} [CommRing D]
    (ψ : Γ(X, U) →+* D) :
    spMap ψ ≫ hU.fromSpec ≫ f = spMap (ψ.comp (f.appLE V U hUV).hom) ≫ hV.fromSpec := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem ringHom_eq_of_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {D : Type} [CommRing D]
    {ψ ψ' : Γ(X, U) →+* D} (h : spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec) : ψ = ψ' := by
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_ringHom_of_le {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {D : Type} [CommRing D]
    (x : Sp D ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U) : ∃ φ : Γ(X, U) →+* D, x = spMap φ ≫ hU.fromSpec := by
  refine ⟨(x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Spec (CommRingCat.of D))) hx
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  change x = Spec.map (CommRingCat.ofHom (x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom).hom) ≫ _
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem le_preimage_of_fst {X : Scheme.{0}} {U : X.Opens} {C : Type} [CommRing C] (x : Sp (DualNumber C) ⟶ X)
    (h : ∀ p, (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ x) p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (TrivSqZeroExt.fstHom C C C).toRingHom := fun c => ⟨TrivSqZeroExt.inl c, by simp⟩
  have hker : RingHom.ker (TrivSqZeroExt.fstHom C C C).toRingHom ≤ p.asIdeal := fun a ha => by
    have h0 : a.fst = 0 := ha
    have h2 : a ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    exact p.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact zero_mem _)
  haveI := p.isPrime
  have hprime := Ideal.map_isPrime_of_surjective hs hker
  let p₀ : ↥(Sp C) := (⟨p.asIdeal.map (TrivSqZeroExt.fstHom C C C).toRingHom, hprime⟩ : PrimeSpectrum C)
  have hp : (spMap (TrivSqZeroExt.fstHom C C C).toRingHom).base p₀ = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap (TrivSqZeroExt.fstHom C C C).toRingHom
      (Ideal.map (TrivSqZeroExt.fstHom C C C).toRingHom p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left.mpr hker]
  have e := h p₀
  simp only [Scheme.Hom.comp_apply] at e
  show x p ∈ U
  rw [← hp]
  exact e

theorem tan_iff_der (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C) :
    (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
    (∀ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) →
       (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) →
       ∃ v : epsAt y ⟶ G, IsTanAt G y v ∧ v.left = spMap φ ≫ hU.fromSpec) ∧
    (∀ v : epsAt y ⟶ G, IsTanAt G y v → ∃ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) ∧
       (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) ∧ v.left = spMap φ ≫ hU.fromSpec) := by
  intro h1
  have hal : ∀ c : C, algebraMap C (DualNumber C) c = TrivSqZeroExt.inl c := fun _ => rfl
  have hy : y = spMap (u.comp (G.hom.appLE V U hUV).hom) ≫ hV.fromSpec := by
    have hw := Over.w (1 : Over.mk y ⟶ G)
    rw [h1, Category.assoc, spMap_fromSpec_hom G.hom hU hV hUV u] at hw
    exact hw.symm
  have hbase : spMap (algebraMap C (DualNumber C)) ≫ y =
      spMap (((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom) ≫ hV.fromSpec := by
    rw [hy, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨fun φ hφ hb => ?_, fun v hv => ?_⟩
  · have hcomp : φ.comp (G.hom.appLE V U hUV).hom =
        ((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom := by
      ext b
      · simpa [hal] using hφ _
      · simpa [hal] using hb b
    refine ⟨Over.homMk (spMap φ ≫ hU.fromSpec) ?_, ?_, rfl⟩
    · change (spMap φ ≫ hU.fromSpec) ≫ G.hom = spMap (algebraMap C (DualNumber C)) ≫ y
      rw [Category.assoc, spMap_fromSpec_hom G.hom hU hV hUV φ, hbase, hcomp]
    · have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp φ = u := by
        ext a
        exact hφ a
      change spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap φ ≫ hU.fromSpec = _
      rw [h1, ← Category.assoc, ← Spec.map_comp, ← hfst]
      rfl
  · have hv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = spMap u ≫ hU.fromSpec := hv.trans h1
    have hle : ⊤ ≤ v.left ⁻¹ᵁ U := by
      refine le_preimage_of_fst v.left fun p => ?_
      rw [hv']
      simp only [Scheme.Hom.comp_apply]
      exact hU.range_fromSpec.subset (Set.mem_range_self _)
    obtain ⟨φ, hφ⟩ := exists_ringHom_of_le hU v.left hle
    have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp φ = u := by
      apply ringHom_eq_of_fromSpec hU
      rw [← hv', hφ, ← Category.assoc, ← Spec.map_comp]
      rfl
    have hcomp : φ.comp (G.hom.appLE V U hUV).hom =
        ((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom := by
      apply ringHom_eq_of_fromSpec hV
      rw [← hbase, ← spMap_fromSpec_hom G.hom hU hV hUV φ, ← Category.assoc, ← hφ]
      exact Over.w v
    refine ⟨φ, fun a => RingHom.congr_fun hfst a, fun b => ?_, hφ⟩
    have := RingHom.congr_fun hcomp b
    simpa [hal] using congrArg TrivSqZeroExt.snd this

end GlobalTheory.CompanionTheory.Ar.TanChart
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_of_dual_hom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  (∀ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) →
     (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) →
     ∃ v : epsAt y ⟶ G, IsTanAt G y v ∧ v.left = spMap φ ≫ hU.fromSpec) ∧
  (∀ v : epsAt y ⟶ G, IsTanAt G y v → ∃ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) ∧
     (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) ∧ v.left = spMap φ ≫ hU.fromSpec) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

private theorem isHecke_div_and_resEtaPow_div {P G1 : Scheme.{0}} (π1 π2 : P ⟶ G1)
    (hmono : ∀ (T : Scheme.{0}) (f1 f2 : T ⟶ P), f1 ≫ π1 = f2 ≫ π1 → f1 ≫ π2 = f2 ≫ π2 → f1 = f2)
    (C : Type) [CommRing C] [IsLocalRing C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (u1 u2 u3 u4 : Spec (CommRingCat.of C) ⟶ P)
    (h12 : u1 ≫ π1 = u2 ≫ π1) (h34 : u3 ≫ π1 = u4 ≫ π1)
    (h13 : u1 ≫ π2 = u3 ≫ π2) (h24 : u2 ≫ π2 = u4 ≫ π2)
    (e1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (e2 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u2 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (e3 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u3 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (O : P.Opens) (o1 : ⊤ ≤ u1 ⁻¹ᵁ O) (o2 : ⊤ ≤ u2 ⁻¹ᵁ O) (o3 : ⊤ ≤ u3 ⁻¹ᵁ O)
    (o4 : ⊤ ≤ u4 ⁻¹ᵁ O) (s : Γ(P, O)) :
    (u1.appLE O ⊤ o1).hom s + (u4.appLE O ⊤ o4).hom s =
      (u2.appLE O ⊤ o2).hom s + (u3.appLE O ⊤ o3).hom s := by
  have appLE_eq : ∀ {X Y : Scheme.{0}} (f g : X ⟶ Y), f = g → ∀ (U : Y.Opens) (V : X.Opens)
      (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U), f.appLE U V e = g.appLE U V e' := by
    intro X Y f g h U V e e'
    subst h
    rfl
  have hJP : ∀ (Q : Ideal C), Q.IsPrime → J ≤ Q := by
    intro Q hQ z hz
    have hz2 : z ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow hz 2
    rw [hJ, Ideal.mem_bot] at hz2
    exact hQ.mem_of_pow_mem 2 (hz2 ▸ Q.zero_mem)
  have hsurj : ∀ t : PrimeSpectrum C, ∃ t' : PrimeSpectrum (C ⧸ J),
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).base t' = t := by
    intro t
    have : (t.asIdeal.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hJP _ t.2)
    refine ⟨⟨t.asIdeal.map (Ideal.Quotient.mk J), this⟩, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk J) (t.asIdeal.map (Ideal.Quotient.mk J)) = t.asIdeal
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr (hJP _ t.2)
  have hpt : ∀ (u : Spec (CommRingCat.of C) ⟶ P),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4 →
      ∀ t : PrimeSpectrum C, u.base t = u4.base t := by
    intro u hu t
    obtain ⟨t', rfl⟩ := hsurj t
    exact congrArg (fun h => h.base t') hu
  let c : PrimeSpectrum C := IsLocalRing.closedPoint C
  have hc4 : u4.base c ∈ O := o4 trivial
  obtain ⟨W1, hW1, hpW1, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := π1.base (u4.base c)) (U := ⊤) trivial
  obtain ⟨W2, hW2, hpW2, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := π2.base (u4.base c)) (U := ⊤) trivial
  obtain ⟨Z, hZ, hpZ, hZsub⟩ := exists_isAffineOpen_mem_and_subset
    (x := u4.base c) (U := O ⊓ π1 ⁻¹ᵁ W1 ⊓ π2 ⁻¹ᵁ W2) ⟨⟨hc4, hpW1⟩, hpW2⟩
  have hZO : Z ≤ O := fun z hz => (hZsub hz).1.1
  have hZ1 : Z ≤ π1 ⁻¹ᵁ W1 := fun z hz => (hZsub hz).1.2
  have hZ2 : Z ≤ π2 ⁻¹ᵁ W2 := fun z hz => (hZsub hz).2
  have hZk : ∀ (u : Spec (CommRingCat.of C) ⟶ P), (∀ t : PrimeSpectrum C, u.base t = u4.base t) →
      ⊤ ≤ u ⁻¹ᵁ Z := by
    intro u hu t _
    show u.base t ∈ Z
    rw [hu t]
    exact ((IsLocalRing.specializes_closedPoint (R := C) t).map u4.base.hom.continuous).mem_open
      Z.isOpen hpZ
  have z1 := hZk u1 (hpt u1 e1)
  have z2 := hZk u2 (hpt u2 e2)
  have z3 := hZk u3 (hpt u3 e3)
  have z4 := hZk u4 (fun _ => rfl)
  have key : ∀ (w : Spec (CommRingCat.of C) ⟶ P) (hw : ⊤ ≤ w ⁻¹ᵁ Z),
      w.appLE Z ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫
          CommRingCat.ofHom (Ideal.Quotient.mk J) =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ w).appLE Z ⊤ (fun _ _ => hw trivial) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (C ⧸ J))).hom := by
    intro w hw
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) w Z ⊤ ⊤ hw
      (fun _ _ => trivial), Category.assoc, ← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  have hmod : ∀ (u : Spec (CommRingCat.of C) ⟶ P) (hu : ⊤ ≤ u ⁻¹ᵁ Z),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4 →
      ∀ v, (u.appLE Z ⊤ hu ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom v -
        (u4.appLE Z ⊤ z4 ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom v ∈ J := by
    intro u hu he v
    rw [← Ideal.Quotient.eq]
    have k1 := congrArg (fun φ => φ.hom v) (key u hu)
    have k4 := congrArg (fun φ => φ.hom v) (key u4 z4)
    have k := appLE_eq _ _ he Z ⊤ (fun _ _ => hu trivial) (fun _ _ => z4 trivial)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at k1 k4 ⊢
    rw [k1, k4, k]
  obtain ⟨a1, ha1⟩ : ∃ a : Γ(P, Z) →+* C,
    a = (u1.appLE Z ⊤ z1 ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a : Γ(P, Z) →+* C,
    a = (u2.appLE Z ⊤ z2 ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a : Γ(P, Z) →+* C,
    a = (u3.appLE Z ⊤ z3 ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom := ⟨_, rfl⟩
  obtain ⟨a4, ha4⟩ : ∃ a : Γ(P, Z) →+* C,
    a = (u4.appLE Z ⊤ z4 ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom := ⟨_, rfl⟩
  have d1 : ∀ v, a1 v - a4 v ∈ J := by rw [ha1, ha4]; exact hmod u1 z1 e1
  have d2 : ∀ v, a2 v - a4 v ∈ J := by rw [ha2, ha4]; exact hmod u2 z2 e2
  have d3 : ∀ v, a3 v - a4 v ∈ J := by rw [ha3, ha4]; exact hmod u3 z3 e3
  have hsq : ∀ a b : C, a ∈ J → b ∈ J → a * b = 0 := by
    intro a b ha hb
    have hab : a * b ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hJ] at hab
    exact (Ideal.mem_bot).mp hab
  let ψ : Γ(P, Z) →+* C :=
    { toFun := fun v => a1 v - a2 v - a3 v + a4 v + a4 v
      map_one' := by simp only [map_one]; ring
      map_mul' := by
        intro v w
        simp only [map_mul]
        have z11 := hsq _ _ (d1 v) (d1 w)
        have z12 := hsq _ _ (d1 v) (d2 w)
        have z13 := hsq _ _ (d1 v) (d3 w)
        have z21 := hsq _ _ (d2 v) (d1 w)
        have z22 := hsq _ _ (d2 v) (d2 w)
        have z23 := hsq _ _ (d2 v) (d3 w)
        have z31 := hsq _ _ (d3 v) (d1 w)
        have z32 := hsq _ _ (d3 v) (d2 w)
        have z33 := hsq _ _ (d3 v) (d3 w)
        linear_combination z11 - z22 - z33 -
          (z11 - z12 - z13 - z21 + z22 + z23 - z31 + z32 + z33)
      map_zero' := by simp only [map_zero]; ring
      map_add' := by intro v w; simp only [map_add]; ring }
  have hc : ∀ (Wi : G1.Opens) (πi : P ⟶ G1) (hi : Z ≤ πi ⁻¹ᵁ Wi)
      (u u' : Spec (CommRingCat.of C) ⟶ P) (hu : ⊤ ≤ u ⁻¹ᵁ Z) (hu' : ⊤ ≤ u' ⁻¹ᵁ Z),
      u ≫ πi = u' ≫ πi → ∀ r,
      (u.appLE Z ⊤ hu ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom ((πi.appLE Wi Z hi).hom r) =
        (u'.appLE Z ⊤ hu' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom
          ((πi.appLE Wi Z hi).hom r) := by
    intro Wi πi hi u u' hu hu' h r
    have := congrArg (fun φ => (φ ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom r)
      ((Scheme.Hom.appLE_comp_appLE u πi Wi Z ⊤ hi hu).trans
        ((appLE_eq _ _ h Wi ⊤ _ _).trans
          (Scheme.Hom.appLE_comp_appLE u' πi Wi Z ⊤ hi hu').symm))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have hside : ∀ (Wi : G1.Opens) (πi : P ⟶ G1) (hWi : IsAffineOpen Wi) (hi : Z ≤ πi ⁻¹ᵁ Wi),
      (∀ r, ψ ((πi.appLE Wi Z hi).hom r) = a4 ((πi.appLE Wi Z hi).hom r)) →
      (Spec.map (CommRingCat.ofHom ψ) ≫ hZ.fromSpec) ≫ πi =
        (Spec.map (CommRingCat.ofHom a4) ≫ hZ.fromSpec) ≫ πi := by
    intro Wi πi hWi hi hr
    rw [Category.assoc, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec πi hWi hZ hi,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext r
    exact hr r
  have hψ : CommRingCat.ofHom ψ = CommRingCat.ofHom a4 := by
    have hfrom : Spec.map (CommRingCat.ofHom ψ) ≫ hZ.fromSpec =
        Spec.map (CommRingCat.ofHom a4) ≫ hZ.fromSpec := by
      apply hmono
      · apply hside W1 π1 hW1 hZ1
        intro r
        have q12 := hc W1 π1 hZ1 u1 u2 z1 z2 h12 r
        have q34 := hc W1 π1 hZ1 u3 u4 z3 z4 h34 r
        rw [← ha1, ← ha2] at q12
        rw [← ha3, ← ha4] at q34
        show a1 _ - a2 _ - a3 _ + a4 _ + a4 _ = a4 _
        rw [q12, q34]
        ring
      · apply hside W2 π2 hW2 hZ2
        intro r
        have q13 := hc W2 π2 hZ2 u1 u3 z1 z3 h13 r
        have q24 := hc W2 π2 hZ2 u2 u4 z2 z4 h24 r
        rw [← ha1, ← ha3] at q13
        rw [← ha2, ← ha4] at q24
        show a1 _ - a2 _ - a3 _ + a4 _ + a4 _ = a4 _
        rw [q13, q24]
        ring
    rw [cancel_mono] at hfrom
    exact Spec.map_inj.mp hfrom
  obtain ⟨s', hs'⟩ : ∃ s' : Γ(P, Z), s' = (P.presheaf.map (homOfLE hZO).op).hom s := ⟨_, rfl⟩
  have hfin : a1 s' - a2 s' - a3 s' + a4 s' = 0 := by
    have h := congrArg (fun φ => φ.hom s') hψ
    simp only [CommRingCat.hom_ofHom] at h
    change a1 s' - a2 s' - a3 s' + a4 s' + a4 s' = a4 s' at h
    linear_combination h
  have hres : ∀ (u : Spec (CommRingCat.of C) ⟶ P) (hu : ⊤ ≤ u ⁻¹ᵁ O) (hz : ⊤ ≤ u ⁻¹ᵁ Z),
      (u.appLE O ⊤ hu).hom s = (u.appLE Z ⊤ hz).hom s' := by
    intro u hu hz
    rw [hs', ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
  rw [hres u1 o1 z1, hres u2 o2 z2, hres u3 o3 z3, hres u4 o4 z4]
  apply (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.injective
  simp only [map_add]
  have hiso : ∀ (u : Spec (CommRingCat.of C) ⟶ P) (hz : ⊤ ≤ u ⁻¹ᵁ Z),
      (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv ((u.appLE Z ⊤ hz).hom s') =
        (u.appLE Z ⊤ hz ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom s' := fun _ _ => rfl
  rw [hiso u1 z1, hiso u2 z2, hiso u3 z3, hiso u4 z4, ← ha1, ← ha2, ← ha3, ← ha4]
  linear_combination hfin

private theorem isPair_and_isPair_of_isTriple {P G1 : Scheme.{0}} (π1 π2 : P ⟶ G1)
    (hmono : ∀ (T : Scheme.{0}) (f1 f2 : T ⟶ P), f1 ≫ π1 = f2 ≫ π1 → f1 ≫ π2 = f2 ≫ π2 → f1 = f2)
    (A : Type) [CommRing A] (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (u1 u2 u3 u4 : Spec (CommRingCat.of A) ⟶ P)
    (h12 : u1 ≫ π1 = u2 ≫ π1) (h34 : u3 ≫ π1 = u4 ≫ π1)
    (h13 : u1 ≫ π2 = u3 ≫ π2) (h24 : u2 ≫ π2 = u4 ≫ π2)
    (e1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (e2 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u2 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (e3 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u3 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (O : P.Opens) (o1 : ⊤ ≤ u1 ⁻¹ᵁ O) (o2 : ⊤ ≤ u2 ⁻¹ᵁ O) (o3 : ⊤ ≤ u3 ⁻¹ᵁ O)
    (o4 : ⊤ ≤ u4 ⁻¹ᵁ O) (s : Γ(P, O)) :
    (u1.appLE O ⊤ o1).hom s + (u4.appLE O ⊤ o4).hom s =
      (u2.appLE O ⊤ o2).hom s + (u3.appLE O ⊤ o3).hom s := by
  apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
  have hiso : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv x =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x := fun _ => rfl
  simp only [map_add, hiso]
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro m hm
  have natm : ∀ (u : Spec (CommRingCat.of A) ⟶ P) (hu : ⊤ ≤ u ⁻¹ᵁ O),
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u).appLE O ⊤
          (fun _ _ => hu trivial) ≫ (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime m))).hom =
        u.appLE O ⊤ hu ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
          CommRingCat.ofHom (algebraMap A (Localization.AtPrime m)) := by
    intro u hu
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))))
      u O ⊤ ⊤ hu (fun _ _ => trivial), Category.assoc, ← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  have natE : ∀ (u : Spec (CommRingCat.of A) ⟶ P) (hu : ⊤ ≤ u ⁻¹ᵁ O),
      (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime m))).hom.hom
          (((Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u).appLE O ⊤
            (fun _ _ => hu trivial)).hom s) =
        algebraMap A (Localization.AtPrime m)
          ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((u.appLE O ⊤ hu).hom s)) := by
    intro u hu
    have := congrArg (fun φ => φ.hom s) (natm u hu)
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using this
  have hsq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap A (Localization.AtPrime m))))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map (algebraMap A (Localization.AtPrime m)))
        (algebraMap A (Localization.AtPrime m)) Ideal.le_comap_map)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have he : ∀ (u : Spec (CommRingCat.of A) ⟶ P),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4 →
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap A (Localization.AtPrime m))))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap A (Localization.AtPrime m))))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u4 := by
    intro u hu
    rw [← Category.assoc, hsq, Category.assoc, hu, ← Category.assoc, ← hsq, Category.assoc]
  have hloc := isHecke_div_and_resEtaPow_div π1 π2 hmono (Localization.AtPrime m) (J.map (algebraMap A (Localization.AtPrime m)))
    (by rw [← Ideal.map_pow, hJ, Ideal.map_bot])
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u1)
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u2)
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u3)
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u4)
    (by simp only [Category.assoc, h12]) (by simp only [Category.assoc, h34])
    (by simp only [Category.assoc, h13]) (by simp only [Category.assoc, h24])
    (he u1 e1) (he u2 e2) (he u3 e3) O
    (fun _ _ => o1 trivial) (fun _ _ => o2 trivial) (fun _ _ => o3 trivial) (fun _ _ => o4 trivial) s
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime m))).hom.hom hloc
  simp only [map_add] at h
  rw [natE u1 o1, natE u2 o2, natE u3 o3, natE u4 o4] at h
  rw [map_sub, map_add, map_add]
  linear_combination h

theorem sqzero_add : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (B : Type) [CommRing B] [IsLocalRing B] (b : Sp B ⟶ S) (A : Type) [CommRing A] (g : B →+* A) (J : Ideal A), J ^ 2 = ⊥ → ∀ x y : Over.mk (spMap g ≫ b) ⟶ G, spMap (Ideal.Quotient.mk J) ≫ x.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → spMap (Ideal.Quotient.mk J) ≫ y.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → ∀ (V : G.left.Opens) (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V) (hxy : ⊤ ≤ (x * y).left ⁻¹ᵁ V) (h1 : ⊤ ≤ (1 : Over.mk (spMap g ≫ b) ⟶ G).left ⁻¹ᵁ V) (f : Γ(G.left, V)), ((x * y).left.appLE V ⊤ hxy).hom f + ((1 : Over.mk (spMap g ≫ b) ⟶ G).left.appLE V ⊤ h1).hom f = (x.left.appLE V ⊤ hx).hom f + (y.left.appLE V ⊤ hy).hom f := by
  intro S G _ B _ _ b A _ g J hJ x y hx1 hy1 V hx hy hxy h1 f
  have hmono : ∀ (T : Scheme.{0}) (f1 f2 : T ⟶ (G ⊗ G).left), f1 ≫ (fst G G).left = f2 ≫ (fst G G).left →
      f1 ≫ (snd G G).left = f2 ≫ (snd G G).left → f1 = f2 :=
    fun T f1 f2 k1 k2 => Over.tensorObj_ext f1 f2 k1 k2
  have eq_of : ∀ (a c : Over.mk (spMap g ≫ b) ⟶ G),
      spMap (Ideal.Quotient.mk J) ≫ a.left =
        spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left →
      spMap (Ideal.Quotient.mk J) ≫ c.left =
        spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left →
      spMap (Ideal.Quotient.mk J) ≫ (lift a c).left =
        spMap (Ideal.Quotient.mk J) ≫ (lift (1 : Over.mk (spMap g ≫ b) ⟶ G) 1).left := by
    intro a c ha hc
    apply hmono
    · rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, ha]
    · rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, hc]
  have m1 : (lift x y).left ≫ (μ : G ⊗ G ⟶ G).left = (x * y).left := by
    rw [← Over.comp_left]
    rfl
  have m2 : (lift x 1).left ≫ (μ : G ⊗ G ⟶ G).left = x.left := by
    rw [← Over.comp_left]
    show (x * 1).left = x.left
    rw [_root_.mul_one]
  have m3 : (lift 1 y).left ≫ (μ : G ⊗ G ⟶ G).left = y.left := by
    rw [← Over.comp_left]
    show (1 * y).left = y.left
    rw [_root_.one_mul]
  have m4 : (lift (1 : Over.mk (spMap g ≫ b) ⟶ G) 1).left ≫ (μ : G ⊗ G ⟶ G).left =
      (1 : Over.mk (spMap g ≫ b) ⟶ G).left := by
    rw [← Over.comp_left]
    show ((1 : Over.mk (spMap g ≫ b) ⟶ G) * 1).left = _
    rw [_root_.mul_one]
  have oo : ∀ (u : (Over.mk (spMap g ≫ b)).left ⟶ (G ⊗ G).left) (w : (Over.mk (spMap g ≫ b)).left ⟶ G.left),
      u ≫ (μ : G ⊗ G ⟶ G).left = w → ⊤ ≤ w ⁻¹ᵁ V → ⊤ ≤ u ⁻¹ᵁ ((μ : G ⊗ G ⟶ G).left ⁻¹ᵁ V) := by
    intro u w h hw
    subst h
    exact hw
  have conv : ∀ (u : (Over.mk (spMap g ≫ b)).left ⟶ (G ⊗ G).left) (w : (Over.mk (spMap g ≫ b)).left ⟶ G.left)
      (h : u ≫ (μ : G ⊗ G ⟶ G).left = w) (hw : ⊤ ≤ w ⁻¹ᵁ V)
      (hu : ⊤ ≤ u ⁻¹ᵁ ((μ : G ⊗ G ⟶ G).left ⁻¹ᵁ V)),
      (w.appLE V ⊤ hw).hom f =
        (u.appLE ((μ : G ⊗ G ⟶ G).left ⁻¹ᵁ V) ⊤ hu).hom
          (((μ : G ⊗ G ⟶ G).left.appLE V ((μ : G ⊗ G ⟶ G).left ⁻¹ᵁ V) le_rfl).hom f) := by
    intro u w h hw hu
    subst h
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  have o1 := oo _ _ m1 hxy
  have o2 := oo _ _ m2 hx
  have o3 := oo _ _ m3 hy
  have o4 := oo _ _ m4 h1
  rw [conv _ _ m1 hxy o1, conv _ _ m2 hx o2, conv _ _ m3 hy o3, conv _ _ m4 h1 o4]
  exact isPair_and_isPair_of_isTriple (fst G G).left (snd G G).left hmono A J hJ (lift x y).left (lift x 1).left (lift 1 y).left
    (lift (1 : Over.mk (spMap g ≫ b) ⟶ G) 1).left
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd])
    (eq_of x y hx1 hy1) (eq_of x 1 hx1 rfl) (eq_of 1 y rfl hy1)
    ((μ : G ⊗ G ⟶ G).left ⁻¹ᵁ V) o1 o2 o3 o4 _

end GlobalTheory.CompanionTheory.Ar
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_order_points_commute : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (B : Type) [CommRing B] [IsLocalRing B] (b : Sp B ⟶ S) (A : Type) [CommRing A] (g : B →+* A) (J : Ideal A), J ^ 2 = ⊥ → ∀ x y : Over.mk (spMap g ≫ b) ⟶ G, spMap (Ideal.Quotient.mk J) ≫ x.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → spMap (Ideal.Quotient.mk J) ≫ y.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → ∀ (V : G.left.Opens) (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V) (hxy : ⊤ ≤ (x * y).left ⁻¹ᵁ V) (h1 : ⊤ ≤ (1 : Over.mk (spMap g ≫ b) ⟶ G).left ⁻¹ᵁ V) (f : Γ(G.left, V)), ((x * y).left.appLE V ⊤ hxy).hom f + ((1 : Over.mk (spMap g ≫ b) ⟶ G).left.appLE V ⊤ h1).hom f = (x.left.appLE V ⊤ hx).hom f + (y.left.appLE V ⊤ hy).hom f := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.sqzero_add
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SqAdd

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {S : Scheme.{0}} {C B : Type} [CommRing C] [CommRing B]

theorem dualMap_comp_algebraMap (φ : C →+* B) :
    (dualMap φ).comp (algebraMap C (DualNumber C)) = (algebraMap B (DualNumber B)).comp φ := by
  refine RingHom.ext fun c => ?_
  apply TrivSqZeroExt.ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : C →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualMap φ) =
      φ.comp (TrivSqZeroExt.fstHom C C C).toRingHom := by
  refine RingHom.ext fun c => ?_
  simp [dualMap]

def epsIdeal (B : Type) [CommRing B] : Ideal (DualNumber B) :=
  RingHom.ker (TrivSqZeroExt.fstHom B B B).toRingHom

theorem epsIdeal_sq : epsIdeal B ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have ha' : a.fst = 0 := ha
  have hb' : b.fst = 0 := hb
  rw [Ideal.mem_bot]
  apply TrivSqZeroExt.ext <;> simp [ha', hb']

def redMap (B : Type) [CommRing B] : B →+* DualNumber B ⧸ epsIdeal B :=
  (Ideal.Quotient.mk (epsIdeal B)).comp (algebraMap B (DualNumber B))

theorem mk_eq_redMap_comp :
    Ideal.Quotient.mk (epsIdeal B) = (redMap B).comp (TrivSqZeroExt.fstHom B B B).toRingHom := by
  refine RingHom.ext fun a => ?_
  change Ideal.Quotient.mk (epsIdeal B) a = Ideal.Quotient.mk (epsIdeal B) (algebraMap B (DualNumber B) a.fst)
  rw [Ideal.Quotient.eq]
  change (TrivSqZeroExt.fstHom B B B).toRingHom _ = 0
  simp [TrivSqZeroExt.algebraMap_eq_inl]

def restr (φ : C →+* B) (y : Sp C ⟶ S) :
    Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ epsAt y :=
  Over.homMk (spMap (dualMap φ)) (by
    change spMap _ ≫ spMap _ ≫ y = spMap _ ≫ spMap _ ≫ y
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom (dualMap_comp_algebraMap φ))

theorem red_restr (G : Over S) [GrpObj G] (φ : C →+* B) (y : Sp C ⟶ S) (v : epsAt y ⟶ G) (tv : IsTanAt G y v) :
    spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ (restr φ y ≫ v).left =
      spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
        (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left := by
  have hred : spMap (redMap B) = spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (algebraMap B (DualNumber B)) := by
    rw [← Spec.map_comp]; rfl
  have hmk : spMap (Ideal.Quotient.mk (epsIdeal B)) =
      spMap (redMap B) ≫ spMap (TrivSqZeroExt.fstHom B B B).toRingHom := by
    rw [← Spec.map_comp]
    exact congrArg (fun f => spMap f) mk_eq_redMap_comp
  have hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (dualMap φ) =
      spMap φ ≫ spMap (TrivSqZeroExt.fstHom C C C).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => spMap f) (fst_comp_dualMap φ)
  let T : Over S := Over.mk (spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
    spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y)
  let m₁ : T ⟶ Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) :=
    Over.homMk (spMap (Ideal.Quotient.mk (epsIdeal B))) rfl
  let m₂ : T ⟶ Over.mk y := Over.homMk (spMap (redMap B) ≫ spMap φ) (by
    change (spMap (redMap B) ≫ spMap φ) ≫ y = _
    rw [hred]
    simp [T])
  have c : m₁ ≫ (1 : _ ⟶ G) = m₂ ≫ (1 : _ ⟶ G) := by
    rw [MonObj.comp_one, MonObj.comp_one]
  have c' : spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
      (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left =
      (spMap (redMap B) ≫ spMap φ) ≫ (1 : Over.mk y ⟶ G).left := congrArg CommaMorphism.left c
  rw [c']
  have tv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left := tv
  rw [← tv']
  change spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (dualMap φ) ≫ v.left = _
  rw [hmk]
  simp only [Category.assoc]
  rw [reassoc_of% hfst]

theorem top_le_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (k : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ k ⁻¹ᵁ U) :
    ⊤ ≤ (p ≫ k) ⁻¹ᵁ U := fun z _ => by
  change k (p z) ∈ U
  exact h (show p z ∈ (⊤ : Y.Opens) from trivial)

theorem appTop_appLE {X Y Z : Scheme.{0}} (p : X ⟶ Y) (k : Y ⟶ Z) (k' : X ⟶ Z) (e : k' = p ≫ k) (U : Z.Opens)
    (h : ⊤ ≤ k ⁻¹ᵁ U) (h' : ⊤ ≤ k' ⁻¹ᵁ U) (s : Γ(Z, U)) :
    p.appTop.hom ((k.appLE U ⊤ h).hom s) = (k'.appLE U ⊤ h').hom s := by
  subst e
  have hle : (⊤ : X.Opens) ≤ p ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  have hp : p.appTop = p.appLE ⊤ ⊤ hle := Scheme.Hom.app_eq_appLE ..
  have : k.appLE U ⊤ h ≫ p.appTop = (p ≫ k).appLE U ⊤ h' := by
    rw [hp]
    exact Scheme.Hom.appLE_comp_appLE ..
  rw [← this]
  rfl

theorem tan_local (G : Over S) [GrpObj G] [IsLocalRing B] (φ : C →+* B) (y : Sp C ⟶ S) (v w : epsAt y ⟶ G)
    (tv : IsTanAt G y v) (tw : IsTanAt G y w) (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U)
    (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U) (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)) :
    (spMap (dualMap φ)).appTop.hom
        (((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s) =
      (spMap (dualMap φ)).appTop.hom ((v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s) := by
  have hmul : ((restr φ y ≫ v) * (restr φ y ≫ w)).left = spMap (dualMap φ) ≫ (v * w).left :=
    congrArg CommaMorphism.left (MonObj.comp_mul (restr φ y) v w).symm
  have hone : (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left =
      spMap (dualMap φ) ≫ (1 : epsAt y ⟶ G).left :=
    congrArg CommaMorphism.left (MonObj.comp_one (restr φ y)).symm
  have hxv : ⊤ ≤ (restr φ y ≫ v).left ⁻¹ᵁ U := top_le_comp (spMap (dualMap φ)) v.left U hv
  have hxw : ⊤ ≤ (restr φ y ≫ w).left ⁻¹ᵁ U := top_le_comp (spMap (dualMap φ)) w.left U hw
  have hxvw : ⊤ ≤ ((restr φ y ≫ v) * (restr φ y ≫ w)).left ⁻¹ᵁ U := by
    rw [hmul]; exact top_le_comp _ _ U hvw
  have hx1 : ⊤ ≤ (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left ⁻¹ᵁ U := by
    rw [hone]; exact top_le_comp _ _ U h1
  have key := GlobalTheory.T.first_order_points_commute S G B (spMap φ ≫ y) (DualNumber B) (algebraMap B (DualNumber B)) (epsIdeal B)
    epsIdeal_sq (restr φ y ≫ v) (restr φ y ≫ w) (red_restr G φ y v tv) (red_restr G φ y w tw) U hxv hxw hxvw hx1 s
  rw [map_add, map_add,
    appTop_appLE (spMap (dualMap φ)) _ _ hmul U hvw hxvw s,
    appTop_appLE (spMap (dualMap φ)) _ _ hone U h1 hx1 s,
    appTop_appLE (spMap (dualMap φ)) v.left (restr φ y ≫ v).left rfl U hv hxv s,
    appTop_appLE (spMap (dualMap φ)) w.left (restr φ y ≫ w).left rfl U hw hxw s]
  exact key

theorem dualMap_fst (φ : C →+* B) (a : DualNumber C) : (dualMap φ a).fst = φ a.fst := by
  simp [dualMap]

theorem dualMap_snd (φ : C →+* B) (a : DualNumber C) : (dualMap φ a).snd = φ a.snd := by
  simp [dualMap]

theorem dual_eq_of_localization (a b : DualNumber C)
    (h : ∀ (q : Ideal C) [q.IsMaximal], dualMap (algebraMap C (Localization.AtPrime q)) a =
      dualMap (algebraMap C (Localization.AtPrime q)) b) : a = b := by
  have h0 : ∀ r r' : C, (∀ (q : Ideal C) [q.IsMaximal], algebraMap C (Localization.AtPrime q) r =
      algebraMap C (Localization.AtPrime q) r') → r = r' := by
    intro r r' hr
    rw [← sub_eq_zero]
    refine eq_zero_of_localization _ fun q hq => ?_
    rw [map_sub, hr q, sub_self]
  apply TrivSqZeroExt.ext
  · exact h0 _ _ fun q _ => by
      rw [← dualMap_fst, ← dualMap_fst, h q]
  · exact h0 _ _ fun q _ => by
      rw [← dualMap_snd, ← dualMap_snd, h q]

theorem gamma_eq_of_localization (a b : Γ(Sp (DualNumber C), ⊤))
    (h : ∀ (q : Ideal C) [q.IsMaximal], (spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom a =
      (spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom b) : a = b := by
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).commRingCatIsoToRingEquiv.injective
  refine hinj (dual_eq_of_localization _ _ fun q _ => ?_)
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap (algebraMap C (Localization.AtPrime q))))
  have e' : ∀ c : Γ(Sp (DualNumber C), ⊤), dualMap (algebraMap C (Localization.AtPrime q))
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Localization.AtPrime q)))).hom
        ((spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom c) := fun c =>
    (congrArg (fun f => f.hom c) e).symm
  rw [e', e', h q]

theorem tan_mul_add : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S)
    (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
    ∀ (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U) (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U)
      (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)),
      ((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s =
        (v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s := by
  intro S G _ C _ y v w tv tw U hv hw hvw h1 s
  exact gamma_eq_of_localization _ _ fun q _ =>
    tan_local G (algebraMap C (Localization.AtPrime q)) y v w tv tw U hv hw hvw h1 s

end GlobalTheory.CompanionTheory.Ar.SqAdd
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_section_additive : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S) (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U) (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U)
    (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)),
    ((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s =
      (v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.SqAdd.tan_mul_add
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanMul

abbrev red (C : Type) [CommRing C] : Sp C ⟶ Sp (DualNumber C) :=
  spMap (TrivSqZeroExt.fstHom C C C).toRingHom

theorem red_surj (C : Type) [CommRing C] (p : Sp (DualNumber C)) : ∃ q : Sp C, red C q = p := by
  let P : PrimeSpectrum (DualNumber C) := p
  have hker : RingHom.ker (TrivSqZeroExt.fstHom C C C).toRingHom ≤ P.asIdeal := by
    intro a ha
    have h0 : a.fst = 0 := ha
    have h2 : a * a = 0 := by
      ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    have : a * a ∈ P.asIdeal := by rw [h2]; exact zero_mem _
    rcases P.isPrime.mem_or_mem this with h | h <;> exact h
  have hs : Function.Surjective (TrivSqZeroExt.fstHom C C C).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  haveI := P.isPrime
  have hprime := Ideal.map_isPrime_of_surjective hs hker
  refine ⟨(⟨_, hprime⟩ : PrimeSpectrum C), ?_⟩
  have e : PrimeSpectrum.comap (TrivSqZeroExt.fstHom C C C).toRingHom ⟨_, hprime⟩ = P := by
    apply PrimeSpectrum.ext
    change Ideal.comap (TrivSqZeroExt.fstHom C C C).toRingHom
      (Ideal.map (TrivSqZeroExt.fstHom C C C).toRingHom P.asIdeal) = P.asIdeal
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left.mpr hker]
  exact e

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)

include hU in

theorem top_le {C : Type} [CommRing C] (t : Sp (DualNumber C) ⟶ X) (u : Γ(X, U) →+* C)
    (h : red C ≫ t = spMap u ≫ hU.fromSpec) : ⊤ ≤ t ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := red_surj C p
  show t (red C q) ∈ U
  have e : t (red C q) = hU.fromSpec (spMap u q) := by
    have := congrArg (fun f : Sp C ⟶ X => f q) h
    simpa using this
  rw [e]
  exact hU.range_fromSpec.subset (Set.mem_range_self _)

def ringOf {A : Type} [CommRing A] (t : Sp A ⟶ X) (h : ⊤ ≤ t ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem ringOf_spec {A : Type} [CommRing A] (t : Sp A ⟶ X) (h : ⊤ ≤ t ⁻¹ᵁ U) :
    spMap (ringOf t h) ≫ hU.fromSpec = t := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec t hU (isAffineOpen_top (Spec (CommRingCat.of A))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have e2 : spMap (ringOf t h) = Spec.map (t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) := by
    unfold ringOf spMap
    rw [CommRingCat.ofHom_hom]
  rw [e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

include hU in
theorem ring_inj {A : Type} [CommRing A] {f g : Γ(X, U) →+* A}
    (h : spMap f ≫ hU.fromSpec = spMap g ≫ hU.fromSpec) : f = g := by
  rw [cancel_mono] at h
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

theorem ringOf_eq {A : Type} [CommRing A] {t : Sp A ⟶ X} (h : ⊤ ≤ t ⁻¹ᵁ U) {f : Γ(X, U) →+* A}
    (e : t = spMap f ≫ hU.fromSpec) : ringOf t h = f :=
  ring_inj hU ((ringOf_spec hU t h).trans e)

variable {S : Scheme.{0}} {C : Type} [CommRing C] (y : Sp C ⟶ S)

def redO : Over.mk y ⟶ epsAt y :=
  Over.homMk (red C) (by
    have h : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (algebraMap C (DualNumber C)) = RingHom.id C := by
      ext a; simp
    show red C ≫ spMap (algebraMap C (DualNumber C)) ≫ y = y
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    simp)

def projO : epsAt y ⟶ Over.mk y :=
  Over.homMk (spMap (algebraMap C (DualNumber C))) rfl

theorem comp_one_O {G T T' : Over S} [GrpObj G] (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem comp_mul_O {G T T' : Over S} [GrpObj G] (f : T' ⟶ T) (a b : T ⟶ G) :
    f ≫ (a * b) = (f ≫ a) * (f ≫ b) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem mul_left_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  intro S G _ U hU C _ y u hu v w hv hw φ ψ χ hφ hψ hχ hs ev ew
  have rv : redO y ≫ v = 1 := Over.OverMorphism.ext hv
  have rw' : redO y ≫ w = 1 := Over.OverMorphism.ext hw
  have rvw : redO y ≫ (v * w) = 1 := by rw [comp_mul_O, rv, rw', _root_.one_mul]
  have r1 : redO y ≫ (1 : epsAt y ⟶ G) = 1 := comp_one_O _
  have lv : red C ≫ v.left = spMap u ≫ hU.fromSpec := hv.trans hu
  have lw : red C ≫ w.left = spMap u ≫ hU.fromSpec := hw.trans hu
  have lvw : red C ≫ (v * w).left = spMap u ≫ hU.fromSpec :=
    (congrArg (fun f => CommaMorphism.left f) rvw).trans hu
  have l1 : red C ≫ (1 : epsAt y ⟶ G).left = spMap u ≫ hU.fromSpec :=
    (congrArg (fun f => CommaMorphism.left f) r1).trans hu
  have hv' := top_le hU _ u lv
  have hw' := top_le hU _ u lw
  have hvw := top_le hU _ u lvw
  have h1 := top_le hU _ u l1
  have e1 : (1 : epsAt y ⟶ G).left = spMap ((algebraMap C (DualNumber C)).comp u) ≫ hU.fromSpec := by
    have p1 : projO y ≫ (1 : Over.mk y ⟶ G) = 1 := comp_one_O _
    have p2 : spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left = (1 : epsAt y ⟶ G).left :=
      congrArg (fun f => CommaMorphism.left f) p1
    rw [← p2, hu, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (ringOf (v * w).left hvw) = u := by
    apply ring_inj hU
    have : spMap ((TrivSqZeroExt.fstHom C C C).toRingHom.comp (ringOf (v * w).left hvw)) =
        red C ≫ spMap (ringOf (v * w).left hvw) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc, ringOf_spec hU, lvw]
  have hχ' : ringOf (v * w).left hvw = χ := by
    ext s
    · rw [hχ]
      exact RingHom.congr_fun hfst s
    · have key := congrArg (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom.hom
        (GlobalTheory.T.tangent_section_additive S G C y v w hv hw U hv' hw' hvw h1 s)
      rw [map_add, map_add] at key
      change ringOf (v * w).left hvw s + ringOf (1 : epsAt y ⟶ G).left h1 s =
        ringOf v.left hv' s + ringOf w.left hw' s at key
      rw [ringOf_eq hU h1 e1, ringOf_eq hU hv' ev, ringOf_eq hU hw' ew] at key
      have := congrArg TrivSqZeroExt.snd key
      have h0 : TrivSqZeroExt.snd (((algebraMap C (DualNumber C)).comp u) s) = 0 := by
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, h0, add_zero] at this
      rw [hs, this]
  rw [← hχ', ringOf_spec hU]

end GlobalTheory.CompanionTheory.Ar.TanMul
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_sum_dual_number : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq | exact GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartDer

open scoped TensorProduct

theorem exists_diffModule {A B : Type} [CommRing A] [CommRing B] (g : B →+* A) (hg : g.Smooth)
    {R : Type} [CommRing R] (f : R) (u : A →+* Localization.Away f) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module (Localization.Away f) P)
      (_ : IsScalarTower R (Localization.Away f) P) (_ : Module.Finite (Localization.Away f) P)
      (_ : Module.Projective (Localization.Away f) P) (d : A → P),
      (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = u a • d b + u b • d a) ∧ (∀ b, d (g b) = 0) ∧
      ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
        κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
        (∀ (w : P →ₗ[R] C) (r : Localization.Away f) (p : P), w (r • p) = κ r * w p) ∧
        (∀ w w' : P →ₗ[R] C, (∀ a, w (d a) = w' (d a)) → w = w') ∧
        (∀ δ : A → C, (∀ a b, δ (a + b) = δ a + δ b) →
          (∀ a b, δ (a * b) = κ (u a) * δ b + κ (u b) * δ a) → (∀ b, δ (g b) = 0) →
          ∃ w : P →ₗ[R] C, ∀ a, w (d a) = δ a) := by
  letI iB : Algebra B A := g.toAlgebra
  haveI : Algebra.Smooth B A := hg
  letI iA : Algebra A (Localization.Away f) := u.toAlgebra
  haveI tw : IsScalarTower R (Localization.Away f) (Localization.Away f ⊗[A] Ω[A⁄B]) := inferInstance
  have hsmul : ∀ (a : A) (x : Ω[A⁄B]), (1 : Localization.Away f) ⊗ₜ[A] (a • x) =
      u a • ((1 : Localization.Away f) ⊗ₜ[A] x) := fun a x => by
    have e : a • (1 : Localization.Away f) = u a := by
      rw [Algebra.smul_def, _root_.mul_one]; rfl
    rw [← TensorProduct.smul_tmul, e, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  refine ⟨Localization.Away f ⊗[A] Ω[A⁄B], inferInstance, inferInstance, inferInstance, tw,
    Module.Finite.base_change A _ _, inferInstance, fun a => 1 ⊗ₜ[A] KaehlerDifferential.D B A a,
    fun a b => by simp [TensorProduct.tmul_add], fun a b => ?_, fun b => ?_, ?_⟩
  · simp only [Derivation.leibniz, TensorProduct.tmul_add, hsmul]
  · have : g b = algebraMap B A b := rfl
    simp [this]
  intro C _ _ κ hκ
  letI aC : Algebra (Localization.Away f) C := κ.toAlgebra
  haveI : IsScalarTower R (Localization.Away f) C := IsScalarTower.of_algebraMap_eq' hκ.symm
  have lin : ∀ (w : (Localization.Away f ⊗[A] Ω[A⁄B]) →ₗ[R] C) (r : Localization.Away f) p,
      w (r • p) = κ r * w p := fun w r p => by
    have h : w (r • p) = r • w p :=
      (w.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)).map_smul r p
    rw [h, Algebra.smul_def]
    rfl
  refine ⟨lin, fun w w' h => LinearMap.ext fun p => ?_, fun δ h1 h2 h3 => ?_⟩
  · have hD : ∀ x : Ω[A⁄B], w ((1 : Localization.Away f) ⊗ₜ[A] x) = w' ((1 : Localization.Away f) ⊗ₜ[A] x) := by
      intro x
      have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D B A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
      | smul a x _ ih => rw [hsmul, lin, lin, ih]
    induction p using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul r x =>
      have e : r ⊗ₜ[A] x = r • ((1 : Localization.Away f) ⊗ₜ[A] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e, lin, lin, hD]
  · letI aA : Algebra A C := (κ.comp u).toAlgebra
    haveI : IsScalarTower A (Localization.Away f) C := IsScalarTower.of_algebraMap_eq' rfl
    letI aB : Algebra B C := ((κ.comp u).comp g).toAlgebra
    haveI : IsScalarTower B A C := IsScalarTower.of_algebraMap_eq' rfl
    let L : A →ₗ[B] C :=
      { toFun := δ
        map_add' := h1
        map_smul' := fun b a => by
          change δ (g b * a) = κ (u (g b)) * δ a
          rw [h2, h3, mul_zero, add_zero] }
    let Dv : Derivation B A C := Derivation.mk' L fun a b => by
      change δ (a * b) = κ (u a) * δ b + κ (u b) * δ a
      exact h2 a b
    refine ⟨(Dv.liftKaehlerDifferential.liftBaseChange (Localization.Away f)).restrictScalars R, fun a => ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D]
    rfl

def dualOf {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C)
    (h1 : ∀ a b, δ (a + b) = δ a + δ b) (h2 : ∀ a b, δ (a * b) = v a * δ b + v b * δ a) :
    A →+* DualNumber C where
  toFun a := TrivSqZeroExt.inl (v a) + TrivSqZeroExt.inr (δ a)
  map_one' := by
    have h : δ 1 = 0 := by simpa using h2 1 1
    ext <;> simp [h]
  map_mul' a b := by
    ext
    · simp
    · simp [h2, TrivSqZeroExt.snd_mul]
      ring
  map_zero' := by
    have h : δ 0 = 0 := by simpa using h1 0 0
    ext <;> simp [h]
  map_add' a b := by
    ext
    · simp
    · simp [h1]

theorem dualOf_fst {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C) (h1 h2) (a : A) :
    (dualOf v δ h1 h2 a).fst = v a := by
  simp [dualOf]

theorem dualOf_snd {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C) (h1 h2) (a : A) :
    (dualOf v δ h1 h2 a).snd = δ a := by
  simp [dualOf]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem one_left {T : Scheme.{0}} {X M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem exists_lieModel {S : Scheme.{0}} (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (v : Γ(G.left, U) →+* C)
    (h1 : (1 : Over.mk y ⟶ G).left = spMap v ≫ hU.fromSpec)
    {E : Type} [AddCommGroup E] [Module C E] (δ : E → Γ(G.left, U) → C)
    (hadd : ∀ e a b, δ e (a + b) = δ e a + δ e b)
    (hmul : ∀ e a b, δ e (a * b) = v a * δ e b + v b * δ e a)
    (hker : ∀ e b, δ e ((G.hom.appLE V U hUV).hom b) = 0)
    (hEadd : ∀ e e' a, δ (e + e') a = δ e a + δ e' a)
    (hEsmul : ∀ (c : C) e a, δ (c • e) a = c * δ e a)
    (hinj : ∀ e e', (∀ a, δ e a = δ e' a) → e = e')
    (hsurj : ∀ δ' : Γ(G.left, U) → C, (∀ a b, δ' (a + b) = δ' a + δ' b) →
      (∀ a b, δ' (a * b) = v a * δ' b + v b * δ' a) →
      (∀ b, δ' ((G.hom.appLE V U hUV).hom b) = 0) → ∃ e, ∀ a, δ e a = δ' a) :
    ∃ M : LieModel G y E, ∀ e, ∃ φ : Γ(G.left, U) →+* DualNumber C,
      (∀ a, (φ a).fst = v a) ∧ (∀ a, (φ a).snd = δ e a) ∧ (M.pt e).left = spMap φ ≫ hU.fromSpec := by
  obtain ⟨c1, c2⟩ := GlobalTheory.T.tangent_vector_of_dual_hom S G U V hU hV hUV C y v h1
  let φ : E → (Γ(G.left, U) →+* DualNumber C) := fun e => dualOf v (δ e) (hadd e) (hmul e)
  have φfst : ∀ e a, (φ e a).fst = v a := fun e a => dualOf_fst ..
  have φsnd : ∀ e a, (φ e a).snd = δ e a := fun e a => dualOf_snd ..
  have ex : ∀ e, ∃ t : epsAt y ⟶ G, IsTanAt G y t ∧ t.left = spMap (φ e) ≫ hU.fromSpec :=
    fun e => c1 (φ e) (φfst e) fun b => by rw [φsnd, hker]
  choose pt ptan pleft using ex
  have spinj : ∀ ψ ψ' : Γ(G.left, U) →+* DualNumber C,
      spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec → ψ = ψ' := fun ψ ψ' h => by
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h)
    simpa using congrArg CommRingCat.Hom.hom h2
  refine ⟨{ pt := pt, tan := ptan, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun e => ⟨φ e, φfst e, φsnd e, pleft e⟩⟩
  · intro e e' h
    have h2 := spinj _ _ (by rw [← pleft, ← pleft, h] : spMap (φ e) ≫ hU.fromSpec = spMap (φ e') ≫ hU.fromSpec)
    exact hinj _ _ fun a => by rw [← φsnd, h2, φsnd]
  · intro t ht
    obtain ⟨ψ, f1, f2, f3⟩ := c2 t ht
    obtain ⟨e, he⟩ := hsurj (fun a => (ψ a).snd) (fun a b => by simp)
      (fun a b => by
        simp only [map_mul, TrivSqZeroExt.snd_mul, f1]
        simp [mul_comm, add_comm]) f2
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    have h2 : φ e = ψ := RingHom.ext fun a => TrivSqZeroExt.ext (by rw [φfst, f1]) (by rw [φsnd, he])
    rw [pleft, f3, h2]
  · intro e e'
    refine Over.OverMorphism.ext ?_
    rw [GlobalTheory.T.tangent_vector_sum_dual_number S G U hU C y v h1 (pt e) (pt e') (ptan e) (ptan e') (φ e) (φ e') (φ (e + e'))
      (φfst e) (φfst e') (φfst _) (fun a => by rw [φsnd, φsnd, φsnd, hEadd]) (pleft e) (pleft e'), pleft]
  · intro c e
    have h2 : φ (c • e) = (epsMul c).comp (φ e) := RingHom.ext fun a => TrivSqZeroExt.ext
      (by simp [epsMul, φfst]) (by simp [epsMul, φsnd, hEsmul])
    rw [pleft, pleft, h2, spMap_comp, Category.assoc]

theorem lieChart_of_smooth_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Sp R ⟶ S) (f : R) (U : G.left.Opens) (V : S.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V), RingHom.Smooth (G.hom.appLE V U hUV).hom →
  ∀ u : Γ(G.left, U) →+* Localization.Away f,
    (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec → LieChart G x f := by
  intro S G _ R _ x f U V hU hV hUV hsm u h1
  obtain ⟨P, i1, i2, i3, i4, i5, i6, d, dadd, dmul, dker, hP⟩ :=
    exists_diffModule (G.hom.appLE V U hUV).hom hsm f u
  have hunit : ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
      κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
      (1 : Over.mk (spMap (algebraMap R C) ≫ x) ⟶ G).left = spMap (κ.comp u) ≫ hU.fromSpec := by
    intro C _ _ κ hκ
    rw [one_left] at h1 ⊢
    simp only [Over.mk_hom] at h1 ⊢
    have e : spMap (algebraMap R C) = spMap κ ≫ spMap (algebraMap R (Localization.Away f)) := by
      rw [← spMap_comp, hκ]
    have h3 : ((spMap κ ≫ spMap (algebraMap R (Localization.Away f))) ≫ x) ≫ η[G].left =
        spMap κ ≫ (spMap (algebraMap R (Localization.Away f)) ≫ x) ≫ η[G].left := by
      simp only [Category.assoc]
    rw [e, h3, h1, spMap_comp κ u]
    exact (Category.assoc _ _ _).symm
  have key : ∀ (C : Type) [CommRing C] [Algebra R C] (hC : IsUnit (algebraMap R C f)),
      ∃ M : LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C), ∀ w,
        ∃ φ : Γ(G.left, U) →+* DualNumber C,
          (∀ a, (φ a).fst = ((IsLocalization.Away.lift f hC).comp u) a) ∧ (∀ a, (φ a).snd = w (d a)) ∧
          (M.pt w).left = spMap φ ≫ hU.fromSpec := by
    intro C _ _ hC
    have hκ := IsLocalization.Away.lift_comp (S := Localization.Away f) f hC
    obtain ⟨l1, l2, l3⟩ := hP C _ hκ
    exact exists_lieModel (E := P →ₗ[R] C) G U V hU hV hUV C _ _ (hunit C _ hκ)
      (fun (w : P →ₗ[R] C) a => w (d a))
      (fun w a b => by simp [dadd]) (fun w a b => by simp only [dmul, map_add, l1, RingHom.comp_apply])
      (fun w b => by simp [dker]) (fun w w' a => rfl) (fun c w a => by simp) l2 l3
  refine ⟨P, i1, i2, i3, i4, i5, i6, fun C _ _ hC => (key C hC).choose, ?_⟩
  intro C C' _ _ _ _ hC hC' c w
  obtain ⟨φ, f1, f2, f3⟩ := (key C hC).choose_spec w
  obtain ⟨φ', g1, g2, g3⟩ := (key C' hC').choose_spec (c.toLinearMap ∘ₗ w)
  have hc : c.toRingHom.comp (IsLocalization.Away.lift (S := Localization.Away f) f hC) =
      IsLocalization.Away.lift (S := Localization.Away f) f hC' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]
    exact c.comp_algebraMap
  have h2 : φ' = (dualMap c.toRingHom).comp φ := RingHom.ext fun a => TrivSqZeroExt.ext
    (by
      simp only [g1, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, f1]
      exact (RingHom.congr_fun hc (u a)).symm)
    (by
      simp only [g2, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, f2]
      rfl)
  rw [g3, f3, h2, spMap_comp, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.ChartDer
end
end
