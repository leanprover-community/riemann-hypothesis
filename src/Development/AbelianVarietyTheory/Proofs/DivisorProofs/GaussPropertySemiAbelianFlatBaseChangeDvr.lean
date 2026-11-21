import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtPointFunctionFieldMapOfGenericPointComp
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimFiberStalkEqQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPoint
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageRegSet

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Desc.GenFibre

theorem maximalIdeal_eq_span_of_isReduced {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hR : ringKrullDim R = 1) {a : R} (ha : a ≠ 0) (ha' : a ∈ maximalIdeal R)
    (hred : _root_.IsReduced (R ⧸ Ideal.span {a})) : maximalIdeal R = Ideal.span {a} := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.2 hR.le
  have hrad := (Ideal.isRadical_iff_quotient_reduced _).2 hred
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 ha')
  rw [← hrad.radical, Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro P ⟨hP, hPp⟩
  have hne : P ≠ ⊥ := fun h => ha (by
    have := hP (Ideal.mem_span_singleton_self a)
    rwa [h, Ideal.mem_bot] at this)
  exact (IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hne)).ge

theorem isReduced_quot_of_smooth {X B : Scheme.{0}} (π : X ⟶ B) [Smooth π] (y : X) :
    _root_.IsReduced (X.presheaf.stalk y ⧸
      (maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by
  obtain ⟨b, z, rfl⟩ : ∃ (b : B) (z : π.fiber b), π.fiberι b z = y := ⟨π y, π.asFiber y, π.fiberι_asFiber y⟩
  have : Smooth (π.fiberToSpecResidueField b) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback π (B.fromSpecResidueField b)) ‹_›
  have : IsReduced (π.fiber b) := GlobalTheory.isReduced_of_smooth_of_isReduced (π.fiberToSpecResidueField b)
  obtain ⟨e⟩ := GlobalTheory.FibreStalk.nonempty_ringEquiv_stalk_fiber B X π b z
  exact isReduced_of_injective e.toRingHom e.injective

theorem unif : ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (H : Over (Sp T)) [GrpObj H]
    [IsIntegral H.left], IsSemiAbelian H → ∀ y : H.left, H.hom y = closedPoint T →
    ringKrullDim (H.left.presheaf.stalk y) = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} →
    GlobalTheory.Desc.cst H.hom ϖ ≠ 0 ∧ ∀ u : H.left.functionField, u ≠ 0 → ∃ (k : ℤ) (w : H.left.functionField),
      GlobalTheory.Cartier.UnitAt y w ∧ u = GlobalTheory.Desc.cst H.hom ϖ ^ k * w := by
  intro T _ _ _ H _ _ hH y hy hdim ϖ hϖ
  have hsm : Smooth H.hom := hH.smooth
  let S := (Sp T).presheaf.stalk (H.hom y)
  letI : Algebra T S := StructureSheaf.stalkAlgebra T (H.hom y)
  haveI : (H.hom y).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  haveI : IsLocalization.AtPrime S (H.hom y).asIdeal := StructureSheaf.IsLocalization.to_stalk T _
  have hb : (H.hom y).asIdeal = maximalIdeal T := by rw [hy]; rfl
  have hmS : maximalIdeal S = Ideal.span {algebraMap T S ϖ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (H.hom y).asIdeal S, hb, hϖ, Ideal.map_span,
      Set.image_singleton]
  let O := H.left.presheaf.stalk y
  let a₀ : O := (H.hom.stalkMap y).hom (algebraMap T S ϖ)

  have hcst : cst H.hom ϖ = algebraMap O H.left.functionField a₀ := by
    have e₁ := algebraMap_germ (X := H.left) (x := y) (U := ⊤) trivial
      (H.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ϖ))
    have e₂ := Scheme.Hom.germ_stalkMap_apply H.hom ⊤ y trivial ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ϖ)
    refine e₁.symm.trans ?_
    refine congrArg _ (e₂.symm.trans ?_)
    rfl

  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field T (by rw [hϖ, Ideal.span_singleton_eq_bot.2 rfl])
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (H.hom y).asIdeal.primeCompl_le_nonZeroDivisors
  have hs0 : algebraMap T S ϖ ≠ 0 := fun h => hϖ0 ((IsLocalization.injective S
    (H.hom y).asIdeal.primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm))
  have ha₀ : a₀ ≠ 0 := by
    letI : Algebra S O := (H.hom.stalkMap y).hom.toAlgebra
    haveI : Module.Flat S O := Flat.stalkMap H.hom y
    have hr : IsSMulRegular O (algebraMap T S ϖ) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs0)
    intro h
    have h1 : (algebraMap T S ϖ) • (1 : O) = (algebraMap T S ϖ) • (0 : O) := by
      rw [smul_zero, Algebra.smul_def, _root_.mul_one]
      exact h
    exact one_ne_zero (hr h1)
  have ha₀m : a₀ ∈ maximalIdeal O := map_nonunit (H.hom.stalkMap y).hom _
    (hmS ▸ Ideal.mem_span_singleton_self _)

  have hred := isReduced_quot_of_smooth H.hom y
  rw [hmS, Ideal.map_span, Set.image_singleton] at hred
  have hm : maximalIdeal O = Ideal.span {a₀} :=
    maximalIdeal_eq_span_of_isReduced hdim ha₀ ha₀m hred

  haveI : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  have hnf : ¬ IsField O := fun h => ha₀ (by
    have := (IsLocalRing.isField_iff_maximalIdeal_eq.1 h) ▸ ha₀m
    rwa [Ideal.mem_bot] at this)
  have hpr : Submodule.IsPrincipal (maximalIdeal O) := ⟨⟨a₀, hm⟩⟩
  haveI : IsDiscreteValuationRing O :=
    ((IsDiscreteValuationRing.TFAE O hnf).out 0 4).2 hpr
  have hirr : Irreducible a₀ := IsDiscreteValuationRing.irreducible_iff_uniformizer a₀ |>.2 hm
  have hc : cst H.hom ϖ ≠ 0 := by
    rw [hcst]
    exact fun h => ha₀ (IsFractionRing.injective O H.left.functionField (h.trans (map_zero _).symm))
  refine ⟨hc, fun u hu => ?_⟩
  obtain ⟨x, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) u
  have hx : x ≠ 0 := by rintro rfl; simp at hu
  obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hirr
  obtain ⟨n, v', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hd) hirr
  have hv' : algebraMap O H.left.functionField (v' : O) ≠ 0 :=
    (v'.isUnit.map (algebraMap O H.left.functionField)).ne_zero
  refine ⟨(m : ℤ) - n, algebraMap O _ (v : O) * (algebraMap O _ (v' : O))⁻¹,
    UnitAt.mul ⟨_, v.isUnit, rfl⟩ (UnitAt.inv ⟨_, v'.isUnit, rfl⟩), ?_⟩
  rw [hcst, zpow_sub₀ (fun h => hc (hcst.trans h)), zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow]
  have hc' : algebraMap O H.left.functionField a₀ ≠ 0 := hcst ▸ hc
  field_simp

end GlobalTheory.Desc.GenFibre
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser : ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left], IsSemiAbelian H → ∀ y : H.left, H.hom y = closedPoint T → ringKrullDim (H.left.presheaf.stalk y) = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} → GlobalTheory.Desc.cst H.hom ϖ ≠ 0 ∧ ∀ u : H.left.functionField, u ≠ 0 → ∃ (k : ℤ) (w : H.left.functionField), GlobalTheory.Cartier.UnitAt y w ∧ u = GlobalTheory.Desc.cst H.hom ϖ ^ k * w := by
  atlas_forward_decl GlobalTheory.Desc.GenFibre.unif
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem pushout_residue_linearIndependent :
  ∀ (T D A B : Type) [CommRing T] [CommRing D] [CommRing A] [CommRing B] [IsLocalRing T] [IsLocalRing D] [Algebra T D] [Algebra T A] [Algebra D B] [Algebra A B] [Algebra T B] [IsScalarTower T D B] [IsScalarTower T A B] [Algebra.IsPushout T D A B], (maximalIdeal T).map (algebraMap T D) = maximalIdeal D → ∀ (n : ℕ) (x : Fin n → A), (∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T A) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, ∑ i, d i • algebraMap A B (x i) ∈ (maximalIdeal D).map (algebraMap D B) → ∀ i, d i ∈ maximalIdeal D := by
  intro T D A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTD n x hx d hd j

  haveI : IsLocalHom (algebraMap T D) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : a ∈ maximalIdeal T := (mem_maximalIdeal a).2 hna
    have h2 : algebraMap T D a ∈ maximalIdeal D := hTD ▸ Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).1 h2 ha
  letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _

  let v : Fin n → A ⧸ (maximalIdeal T • (⊤ : Submodule T A)) := fun i => Submodule.Quotient.mk (x i)
  have hmem : ∀ y : A, y ∈ maximalIdeal T • (⊤ : Submodule T A) ↔
      y ∈ (maximalIdeal T).map (algebraMap T A) := by
    intro y; rw [Ideal.smul_top_eq_map]; rfl
  have hli : LinearIndependent (T ⧸ maximalIdeal T) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    obtain ⟨c', rfl⟩ : ∃ c' : Fin n → T, (fun k => Ideal.Quotient.mk (maximalIdeal T) (c' k)) = c :=
      ⟨fun k => (Ideal.Quotient.mk_surjective (c k)).choose,
        funext fun k => (Ideal.Quotient.mk_surjective (c k)).choose_spec⟩
    have hsum : (∑ k, Ideal.Quotient.mk (maximalIdeal T) (c' k) • v k) =
        Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) (∑ k, c' k • x k) := by
      rw [← Submodule.mkQ_apply, map_sum]
      rfl
    rw [hsum, Submodule.Quotient.mk_eq_zero, hmem] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hx c' hc i)

  let bs := Module.Basis.span hli
  obtain ⟨f, hf⟩ := LinearMap.exists_extend (K := T ⧸ maximalIdeal T) (bs.coord j)
  have hfv : ∀ i, f (v i) = if i = j then 1 else 0 := by
    intro i
    have := congrArg (fun F => F (bs i)) hf
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Module.Basis.coord_apply,
      Module.Basis.repr_self] at this
    rw [Module.Basis.span_apply] at this
    rw [this, Finsupp.single_apply]

  let φ : T ⧸ maximalIdeal T →+* ResidueField D := ResidueField.map (algebraMap T D)
  have hφ : ∀ t : T, φ (Ideal.Quotient.mk _ t) = algebraMap T (ResidueField D) t := fun t => rfl

  let g : A →ₗ[T] ResidueField D :=
    { toFun := fun a => φ (f (Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) a))
      map_add' := fun a b => by simp only [Submodule.Quotient.mk_add, map_add]
      map_smul' := fun t a => by
        simp only [RingHom.id_apply]
        have hq : Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) (t • a) =
            Ideal.Quotient.mk (maximalIdeal T) t •
              Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) a :=
          (Module.Quotient.mk_smul_mk A (maximalIdeal T) t a).symm
        rw [hq, map_smul, smul_eq_mul, map_mul, hφ, ← Algebra.smul_def] }
  have hg : ∀ i, g (x i) = if i = j then 1 else 0 := by
    intro i
    show φ (f (v i)) = _
    rw [hfv]; split_ifs <;> simp

  have hbc := (Algebra.IsPushout.out (R := T) (S := D) (R' := A) (S' := B))
  let ψ := hbc.lift g
  have hψ : ∀ a : A, ψ (algebraMap A B a) = g a := fun a => hbc.lift_eq g a
  have hkill : ∀ y ∈ (maximalIdeal D).map (algebraMap D B), ψ y = 0 := by
    intro y hy
    have hy' : y ∈ maximalIdeal D • (⊤ : Submodule D B) := by
      rw [Ideal.smul_top_eq_map]; exact hy
    refine Submodule.smul_induction_on hy' ?_ ?_
    · intro r hr b _
      rw [map_smul, Algebra.smul_def]
      have : algebraMap D (ResidueField D) r = 0 := (residue_eq_zero_iff r).2 hr
      rw [this, zero_mul]
    · intro a b ha hb; rw [map_add, ha, hb, add_zero]
  have := hkill _ hd
  rw [map_sum, Finset.sum_eq_single j (fun i _ hi => by rw [map_smul, hψ, hg, if_neg hi, smul_zero])
    (by simp)] at this
  rw [map_smul, hψ, hg, if_pos rfl, Algebra.smul_def, mul_one] at this
  exact (residue_eq_zero_iff _).1 this

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushout_residue_linearIndependent' : ∀ (T D A B : Type) [CommRing T] [CommRing D] [CommRing A] [CommRing B] [IsLocalRing T] [IsLocalRing D] [Algebra T D] [Algebra T A] [Algebra D B] [Algebra A B] [Algebra T B] [IsScalarTower T D B] [IsScalarTower T A B] [Algebra.IsPushout T D A B], (maximalIdeal T).map (algebraMap T D) = maximalIdeal D → ∀ (n : ℕ) (x : Fin n → A), (∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T A) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, ∑ i, d i • algebraMap A B (x i) ∈ (maximalIdeal D).map (algebraMap D B) → ∀ i, d i ∈ maximalIdeal D := by
  atlas_forward_decl GlobalTheory.pushout_residue_linearIndependent
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory

theorem abLawCst_eq_smallExtLiftCst {X : Scheme} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    GlobalTheory.AbLaw.cst f U = GlobalTheory.SmallExtLift.cst f U := by
  ext r
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.SmallExtLift.cst, GlobalTheory.AbLaw.rs, Scheme.Hom.appLE,
    CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
  rfl

theorem isDomain_quot_maximalIdeal_of_smooth :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)), Smooth G.hom →
      GeometricallyConnected G.hom → ∀ (U : G.left.Opens), IsAffineOpen U → ∀ y ∈ U,
        G.hom y = closedPoint R →
          IsDomain (Γ(G.left, U) ⧸ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U)) := by
  intro R _ _ G hsm hgc U hU y hyU hy
  haveI := hsm
  haveI := hgc
  let f : G.left ⟶ Spec (CommRingCat.of R) := G.hom
  let g : Spec (CommRingCat.of (ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (residue R))
  haveI hI : IsIntegral (pullback f g) := GlobalTheory.isIntegral_specialFibre_of_smooth f
  let q := pullback.fst f g
  have H : IsPullback q (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have hsurj : Function.Surjective (q.app U).hom :=
    GlobalTheory.SmallExtLift.app_surj (residue_surjective) H hU
  have hker : RingHom.ker (q.app U).hom = (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U) := by
    rw [abLawCst_eq_smallExtLiftCst]
    apply le_antisymm
    · intro a ha
      have := GlobalTheory.SmallExtLift.mem_of_app_eq_zero (residue_surjective) H hU a ha
      rwa [ker_residue] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, GlobalTheory.SmallExtLift.app_cst H.w,
        (residue_eq_zero_iff r).2 hr, map_zero]
  have hne : Nonempty (q ⁻¹ᵁ U) := by
    have hpt : f y = g (closedPoint (ResidueField R)) := by
      rw [show f y = G.hom y from rfl, hy]
      exact (IsLocalRing.comap_closedPoint (residue R)).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ hpt
    exact ⟨⟨z, show q z ∈ U from hz ▸ hyU⟩⟩
  haveI : IsDomain Γ(pullback f g, q ⁻¹ᵁ U) := inferInstance
  rw [← hker]
  exact (RingHom.quotientKerEquivOfSurjective hsurj).toMulEquiv.isDomain

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_sections_quot_maximalIdeal_smooth_connected : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)), Smooth G.hom → GeometricallyConnected G.hom → ∀ (U : G.left.Opens), IsAffineOpen U → ∀ y ∈ U, G.hom y = closedPoint R → IsDomain (Γ(G.left, U) ⧸ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U)) := by
  atlas_forward_decl GlobalTheory.isDomain_quot_maximalIdeal_of_smooth
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem eq_map_maximalIdeal_of_ringKrullDim_eq_one (R A : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A]
    (p : Ideal A) [p.IsPrime] :
    (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 →
      IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) →
      p = (maximalIdeal R).map (algebraMap R A) := by
  intro hle hdim hdom
  set I := (maximalIdeal R).map (algebraMap R A) with hI
  haveI : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).1 hdom
  have hp1 : p.height = 1 := by
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
    rw [hdim] at h
    exact_mod_cast h.symm
  haveI : p.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]; right; rw [hp1]; exact ENat.one_ne_top
  haveI : I.FiniteHeight := Ideal.finiteHeight_of_le hle (Ideal.IsPrime.ne_top ‹_›)

  have hIne : I ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hmem : ϖ ∈ maximalIdeal R := by
      rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
    have hreg : IsSMulRegular A ϖ :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    have hne : algebraMap R A ϖ ≠ 0 := by
      intro h0
      have : ϖ • (1 : A) = ϖ • (0 : A) := by rw [Algebra.smul_def, mul_one, h0, smul_zero]
      exact one_ne_zero (hreg this)
    intro hbot
    apply hne
    have : algebraMap R A ϖ ∈ I := Ideal.mem_map_of_mem _ hmem
    rw [hbot] at this
    exact (Ideal.mem_bot).1 this
  have hIh : 1 ≤ I.height := by
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    exact hIne (Ideal.height_eq_zero_iff_eq_bot.1 h0)
  exact (Ideal.eq_of_le_of_height_le I hle (by rw [hp1]; exact hIh)).symm

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_map_maximalIdeal_of_ringKrullDim_eq_one' : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A] (p : Ideal A) [p.IsPrime], (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 → IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) → p = (maximalIdeal R).map (algebraMap R A) := by
  atlas_forward_decl GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.ResInj

theorem cst_eq_fnOf {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (V : X.Opens)
    (hV : genericPoint X ∈ V) (r : R) : GlobalTheory.Desc.cst p r = fnOf V hV (GlobalTheory.AbLaw.cst p V r) := by
  simp only [GlobalTheory.Desc.cst, GlobalTheory.AbLaw.cst, fnOf, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp]
  rw [TopCat.Presheaf.germ_res_apply]

theorem zeroAt_fnOf_iff {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} {x : X} (hx : x ∈ U) (b : Γ(X, U)) :
    ZeroAt x (fnOf U (gen_mem hx) b) ↔ (X.presheaf.germ U x hx).hom b ∈ maximalIdeal (X.presheaf.stalk x) := by
  refine ⟨fun ⟨a, ha, e⟩ => ?_, fun h => ⟨_, h, algebraMap_germ hx b⟩⟩
  rwa [IsFractionRing.injective (X.presheaf.stalk x) X.functionField (e.trans (algebraMap_germ hx b).symm)] at ha

theorem cst_zeroAt (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X)
    (hx : p x = closedPoint R) (r : R) (hr : r ∈ maximalIdeal R) : ZeroAt x (GlobalTheory.Desc.cst p r) := by
  have hreg : RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

end GlobalTheory.Desc.ResInj

theorem GlobalTheory.Desc.ResInj.exists_affine_fnOf : ∀ (X : Scheme.{0}) [IsIntegral X] (x : X) (n : ℕ) (u : Fin n → X.functionField), (∀ i, GlobalTheory.Cartier.RegAt x (u i)) → ∃ (U : X.Opens) (hx : x ∈ U), IsAffineOpen U ∧ ∃ s : Fin n → Γ(X, U), ∀ i, GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem hx) (s i) = u i := by
  intro X _ x n u hu
  choose W hxW s hs using fun i => (hu i).exists_fnOf
  let W₀ : X.Opens := ⟨⋂ i, (W i : Set X), isOpen_iInter_of_finite fun i => (W i).isOpen⟩
  have hx₀ : x ∈ W₀ := Set.mem_iInter.2 hxW
  obtain ⟨U, hU, hxU, hUW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hx₀
  have hle : ∀ i, U ≤ W i := fun i z hz => Set.mem_iInter.1 (hUW hz) i
  refine ⟨U, hxU, hU, fun i => resG X (hle i) (s i), fun i => ?_⟩
  rw [fnOf_resG, hs]

theorem GlobalTheory.Desc.ResInj.mem_map_of_germ_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (G : Over (Sp R)) [IsIntegral G.left], Smooth G.hom → GeometricallyConnected G.hom → ∀ y : G.left, G.hom y = closedPoint R → ringKrullDim (G.left.presheaf.stalk y) = 1 → ∀ (U : G.left.Opens) (hy : y ∈ U), IsAffineOpen U → ∀ b : Γ(G.left, U), (G.left.presheaf.germ U y hy).hom b ∈ maximalIdeal (G.left.presheaf.stalk y) → b ∈ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U) := by
  intro R _ _ _ G _ hsm hgc y hy hdim U hyU hU b hb
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  letI : Algebra R Γ(G.left, U) := (GlobalTheory.AbLaw.cst G.hom U).toAlgebra
  haveI : Module.Flat R Γ(G.left, U) := GlobalTheory.AbLaw.flat_cst G.hom hU
  let p := hU.primeIdealOf ⟨y, hyU⟩
  letI : Algebra Γ(G.left, U) (G.left.presheaf.stalk y) := G.left.presheaf.algebra_section_stalk ⟨y, hyU⟩
  haveI hloc := hU.isLocalization_stalk ⟨y, hyU⟩
  have hmem : ∀ c : Γ(G.left, U), (G.left.presheaf.germ U y hyU).hom c ∈ maximalIdeal (G.left.presheaf.stalk y) ↔ c ∈ p.asIdeal := by
    intro c
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (G.left.presheaf.stalk y) p.asIdeal c
  have hle : (maximalIdeal R).map (algebraMap R Γ(G.left, U)) ≤ p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap, ← hmem, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU]
    have := GlobalTheory.Desc.ResInj.cst_zeroAt R G.left G.hom y hy t ht
    rwa [GlobalTheory.Desc.ResInj.cst_eq_fnOf G.hom U (gen_mem hyU)] at this
  have hd : ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
    rw [← hdim]
    exact ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) (G.left.presheaf.stalk y)).toRingEquiv
  have e := GlobalTheory.T.eq_map_maximalIdeal_of_ringKrullDim_eq_one' R Γ(G.left, U) p.asIdeal hle hd (GlobalTheory.T.isDomain_sections_quot_maximalIdeal_smooth_connected R G hsm hgc U hU y hyU hy)
  have : b ∈ p.asIdeal := (hmem b).1 hb
  rw [e] at this
  exact this

theorem GlobalTheory.Desc.ResInj.residue_linearIndependent : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ (n : ℕ) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) → (∀ c : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, GlobalTheory.Desc.cst H.hom (c i) * u i) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, GlobalTheory.Cartier.ZeroAt y' (∑ i, GlobalTheory.Desc.cst H'.hom (d i) * θ (u i)) → ∀ i, d i ∈ maximalIdeal D := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hpff y y' hy hy' hdy hdy' n u hu hind d hz
  have hπy : π y' = y := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb hpff y y' hy hy' hdy hdy'
  obtain ⟨U, hyU, hUa, x, hx⟩ := GlobalTheory.Desc.ResInj.exists_affine_fnOf H.left y n u hu
  set V : H'.left.Opens := π ⁻¹ᵁ U with hVdef
  have hy'V : y' ∈ V := by show π y' ∈ U; rw [hπy]; exact hyU
  have hgU : genericPoint H.left ∈ U := gen_mem hyU
  have hgV : genericPoint H'.left ∈ V := gen_mem hy'V
  letI : Algebra T D := a.toAlgebra
  letI : Algebra T Γ(H.left, U) := (GlobalTheory.AbLaw.cst H.hom U).toAlgebra
  letI : Algebra D Γ(H'.left, V) := (GlobalTheory.AbLaw.cst H'.hom V).toAlgebra
  letI : Algebra Γ(H.left, U) Γ(H'.left, V) := (π.app U).hom.toAlgebra
  letI : Algebra T Γ(H'.left, V) := ((GlobalTheory.AbLaw.cst H'.hom V).comp a).toAlgebra
  haveI : IsScalarTower T D Γ(H'.left, V) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T Γ(H.left, U) Γ(H'.left, V) := .of_algebraMap_eq fun r => by
    have e := GlobalTheory.AbLaw.appLE_cst hpb.w (V := U) (V' := V) le_rfl r
    rw [Scheme.Hom.appLE_eq_app] at e
    exact e.symm
  haveI : Algebra.IsPushout T D Γ(H.left, U) Γ(H'.left, V) := by
    have po := GlobalTheory.AbLaw.isPushout_cst hpb hUa (V' := V) rfl
    rw [Scheme.Hom.appLE_eq_app] at po
    exact CommRingCat.isPushout_iff_isPushout.mp po
  have hsm : Smooth H'.hom := MorphismProperty.of_isPullback hpb hH.smooth
  have hgc : GeometricallyConnected H'.hom := MorphismProperty.of_isPullback hpb hH.geomConnected

  have hindA : ∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T Γ(H.left, U)) →
      ∀ i, c i ∈ maximalIdeal T := by
    intro c hc
    apply hind c
    have hle : (maximalIdeal T).map (algebraMap T Γ(H.left, U)) ≤
        Ideal.comap (H.left.presheaf.germ U y hyU).hom (maximalIdeal _) := by
      rw [Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, Ideal.mem_comap, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU]
      have := GlobalTheory.Desc.ResInj.cst_zeroAt T H.left H.hom y hy t ht
      rwa [GlobalTheory.Desc.ResInj.cst_eq_fnOf H.hom U hgU] at this
    have h1 := hle hc
    rw [Ideal.mem_comap, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU] at h1
    convert h1 using 1
    simp only [map_sum, Algebra.smul_def, map_mul, hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.Desc.ResInj.cst_eq_fnOf H.hom U hgU]
    rfl

  have hd := GlobalTheory.T.pushout_residue_linearIndependent' T D Γ(H.left, U) Γ(H'.left, V) hm n x hindA d
  apply hd
  apply GlobalTheory.Desc.ResInj.mem_map_of_germ_mem D H' hsm hgc y' hy' hdy' V hy'V (GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback hpb hUa)
  rw [← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hy'V]
  convert hz using 1
  simp only [map_sum, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hx i, ← GlobalTheory.Desc.fnOf_app_of_pff H.left H'.left π θ hpff U hgU hgV, GlobalTheory.Desc.ResInj.cst_eq_fnOf H'.hom V hgV]
  rfl
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_linearIndependent_closedFibre_genericPoints : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ (n : ℕ) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) → (∀ c : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, GlobalTheory.Desc.cst H.hom (c i) * u i) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, GlobalTheory.Cartier.ZeroAt y' (∑ i, GlobalTheory.Desc.cst H'.hom (d i) * θ (u i)) → ∀ i, d i ∈ maximalIdeal D := by
  atlas_forward_decl GlobalTheory.Desc.ResInj.residue_linearIndependent
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ModPi

theorem gp_comp_cst (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, gp,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.Desc.cst, fnOf, Scheme.functionField]

theorem cst_reg_zero (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X)
    (hx : p x = closedPoint R) (r : R) :
    GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) ∧ (r ∈ maximalIdeal R → GlobalTheory.Cartier.ZeroAt x (GlobalTheory.Desc.cst p r)) := by
  have hreg : GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine ⟨hreg, fun hr => zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

theorem span_add {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁) {S : Set F₁} {v w : F₁}
    (hv : v ∈ spanBy c S) (hw : w ∈ spanBy c S) : v + w ∈ spanBy c S := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  obtain ⟨m, r', t', ht', rfl⟩ := hw
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ht i
    · rw [Fin.append_right]; exact ht' i
  · rw [Fin.sum_univ_add]; simp

theorem regAt_npow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : GlobalTheory.Cartier.RegAt x f) (n : ℕ) :
    GlobalTheory.Cartier.RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem modPi : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} → ∀ z ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), GlobalTheory.Cartier.ZeroAt y' z → ∃ z₁ ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), z = GlobalTheory.Desc.cst H'.hom (a ϖ) * z₁ := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hff y y' hy hy' hdy hdy' ϖ hmT
  have hmD : maximalIdeal D = Ideal.span {a ϖ} := by rw [← hm, hmT, Ideal.map_span, Set.image_singleton]
  have hcomp : θ.comp (cst H.hom) = (cst H'.hom).comp a := by
    obtain ⟨l, hl1, hl2⟩ := hff
    have e1 := gp_comp_cst H.left T H.hom
    have e2 := gp_comp_cst H'.left D H'.hom
    have hl : l = gp H'.left := by simpa using hl1
    have key : spMap (θ.comp (cst H.hom)) = spMap ((cst H'.hom).comp a) := by
      calc spMap (θ.comp (cst H.hom)) = spMap θ ≫ spMap (cst H.hom) := by simp [spMap, CommRingCat.ofHom_comp]
        _ = spMap θ ≫ gp H.left ≫ H.hom := by rw [e1]
        _ = l ≫ π ≫ H.hom := by rw [← Category.assoc, ← hl2, Category.assoc]
        _ = gp H'.left ≫ H'.hom ≫ spMap a := by rw [hpb.w, hl]
        _ = spMap (cst H'.hom) ≫ spMap a := by rw [← Category.assoc, e2]
        _ = spMap ((cst H'.hom).comp a) := by simp [spMap, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hθc : ∀ t, θ (cst H.hom t) = cst H'.hom (a t) := fun t => by
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply]
  set c := cst H'.hom with hc
  have hreg : ∀ u, GlobalTheory.Cartier.RegAt y u → GlobalTheory.Cartier.RegAt y' (θ u) := by
    intro u hu
    have hpt := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy'
    exact GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp H.left H'.left π θ ⟨_, hff.choose_spec⟩ y' u (hpt ▸ hu)
  have hcreg : ∀ d, GlobalTheory.Cartier.RegAt y' (c d) := fun d => (cst_reg_zero D H'.left H'.hom y' hy' d).1
  have hc0reg : ∀ t, GlobalTheory.Cartier.RegAt y (cst H.hom t) := fun t => (cst_reg_zero T H.left H.hom y hy t).1
  have hϖz : GlobalTheory.Cartier.ZeroAt y (cst H.hom ϖ) :=
    (cst_reg_zero T H.left H.hom y hy ϖ).2 (by rw [hmT]; exact Ideal.subset_span rfl)
  obtain ⟨hϖ0, hfac⟩ := GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser T H hH y hy hdy ϖ hmT

  have hdiv : ∀ x, GlobalTheory.Cartier.ZeroAt y x → ∃ w, GlobalTheory.Cartier.RegAt y w ∧ x = cst H.hom ϖ * w := by
    intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, regAt_zero y, by rw [hx0, mul_zero]⟩
    obtain ⟨k, w, hw, rfl⟩ := hfac x hx0
    rcases le_or_gt 1 k with hk | hk
    · refine ⟨cst H.hom ϖ ^ (k - 1).toNat * w, (regAt_npow (hc0reg ϖ) _).mul hw.regAt, ?_⟩
      rw [← _root_.mul_assoc, ← pow_succ', ← zpow_natCast]
      congr 2; omega
    · exfalso
      have hk' : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have e : cst H.hom ϖ ^ k * w * cst H.hom ϖ ^ (-k).toNat = w := by
        rw [mul_comm _ (cst H.hom ϖ ^ (-k).toNat), ← _root_.mul_assoc, ← zpow_natCast, hk',
          ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, _root_.one_mul]
      exact (zeroAt_iff.1 (e ▸ hx.mul (regAt_npow (hc0reg ϖ) _))).2 hw
  have hgeo := GlobalTheory.T.residueField_linearIndependent_closedFibre_genericPoints T D a ha hm H H' π θ hH hpb hff y y' hy hy' hdy hdy'
  set S := spanBy c (θ '' regSet y) with hS

  have hyes : ∀ (n : ℕ) (d : Fin n → D) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) →
      (∀ cc : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, cst H.hom (cc i) * u i) → ∀ i, cc i ∈ maximalIdeal T) →
      GlobalTheory.Cartier.ZeroAt y' (∑ i, c (d i) * θ (u i)) → ∃ z₁ ∈ S, ∑ i, c (d i) * θ (u i) = c (a ϖ) * z₁ := by
    intro n d u hu hind hz
    have hd := hgeo n u hu hind d hz
    choose e he using fun i => Ideal.mem_span_singleton'.1 (hmD ▸ hd i)
    refine ⟨∑ i, c (e i) * θ (u i), ⟨n, e, fun i => θ (u i), fun i => ⟨u i, hu i, rfl⟩, rfl⟩, ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he i, map_mul]; ring
  have hmain : ∀ (n : ℕ) (d : Fin n → D) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) →
      GlobalTheory.Cartier.ZeroAt y' (∑ i, c (d i) * θ (u i)) → ∃ z₁ ∈ S, ∑ i, c (d i) * θ (u i) = c (a ϖ) * z₁ := by
    intro n
    induction n with
    | zero => intro d u hu hz; exact hyes 0 d u hu (fun _ _ i => i.elim0) hz
    | succ n ih =>
      intro d u hu hz
      by_cases hind : ∀ cc : Fin (n + 1) → T, GlobalTheory.Cartier.ZeroAt y (∑ i, cst H.hom (cc i) * u i) → ∀ i, cc i ∈ maximalIdeal T
      · exact hyes _ d u hu hind hz
      push_neg at hind
      obtain ⟨cc, hZ, k, hk⟩ := hind
      obtain ⟨ν, hν⟩ : ∃ ν : T, ν * cc k = 1 := by
        obtain ⟨v, hv⟩ := IsLocalRing.notMem_maximalIdeal.1 hk
        exact ⟨↑v⁻¹, by rw [← hv, Units.inv_mul]⟩
      obtain ⟨w, hw, hrel⟩ := hdiv _ hZ
      rw [Fin.sum_univ_succAbove _ k] at hrel
      have hrel' := congrArg θ hrel
      simp only [map_add, map_sum, map_mul, hθc] at hrel'
      have hν' : c (a ν) * c (a (cc k)) = 1 := by rw [← map_mul, ← map_mul, hν, map_one, map_one]
      set d' : Fin n → D := fun j => d (k.succAbove j) - d k * a ν * a (cc (k.succAbove j)) with hd'
      set u' : Fin n → H.left.functionField := fun j => u (k.succAbove j) with hu'
      have hsplit : ∑ i, c (d i) * θ (u i) = c (a ϖ) * (c (d k * a ν) * θ w) + ∑ j, c (d' j) * θ (u' j) := by
        rw [Fin.sum_univ_succAbove _ k]
        have : ∑ j, c (d' j) * θ (u' j) = ∑ j, c (d (k.succAbove j)) * θ (u (k.succAbove j)) -
            c (d k) * c (a ν) * ∑ j, c (a (cc (k.succAbove j))) * θ (u (k.succAbove j)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hd', hu', map_sub, map_mul]; ring
        rw [this, map_mul]
        linear_combination (c (d k) * c (a ν)) * hrel' - (c (d k) * θ (u k)) * hν'
      have hz' : GlobalTheory.Cartier.ZeroAt y' (∑ j, c (d' j) * θ (u' j)) := by
        have e : ∑ j, c (d' j) * θ (u' j) = ∑ i, c (d i) * θ (u i) + c (a ϖ) * (c (-(d k * a ν)) * θ w) := by
          rw [hsplit, map_neg]; ring
        rw [e]
        refine hz.add (ZeroAt.mul ?_ ((hcreg _).mul (hreg w hw)))
        exact (cst_reg_zero D H'.left H'.hom y' hy' (a ϖ)).2 (by rw [hmD]; exact Ideal.subset_span rfl)
      obtain ⟨z₁, hz₁, e₁⟩ := ih d' u' (fun j => hu _) hz'
      refine ⟨c (d k * a ν) * θ w + z₁, span_add c ⟨1, fun _ => d k * a ν, fun _ => θ w, fun _ => ⟨w, hw, rfl⟩, by simp⟩ hz₁, ?_⟩
      rw [hsplit, e₁]; ring
  intro z hz hzy
  obtain ⟨n, r, t, ht, rfl⟩ := hz
  choose u hu hut using ht
  have e : ∑ i, c (r i) * t i = ∑ i, c (r i) * θ (u i) := Finset.sum_congr rfl fun i _ => by rw [hut i]
  rw [e] at hzy ⊢
  exact hmain n r u hu hzy

end GlobalTheory.Desc.ModPi
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSpan_vanishing_eq_uniformiser_mul : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} → ∀ z ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), GlobalTheory.Cartier.ZeroAt y' z → ∃ z₁ ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), z = GlobalTheory.Desc.cst H'.hom (a ϖ) * z₁ := by
  atlas_forward_decl GlobalTheory.Desc.ModPi.modPi
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.FlatLin

theorem fnOf_algX {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (U : X.Opens)
    (hU : genericPoint X ∈ U) (r : R) :
    fnOf U hU (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U r) = cst p r := by
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, cst, RingHom.comp_apply, fnOf, Scheme.Hom.appLE,
    CommRingCat.hom_comp]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem gen_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {π : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) : π (genericPoint Y) = genericPoint X := by
  obtain ⟨l, h1, h2⟩ := h
  rw [Category.comp_id] at h1
  subst h1
  have eY : gp Y (closedPoint (Y.presheaf.stalk (genericPoint Y))) = genericPoint Y :=
    Scheme.fromSpecStalk_closedPoint
  have hc : (spMap θ) (closedPoint (Y.presheaf.stalk (genericPoint Y))) =
      closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  calc π (genericPoint Y) = π (gp Y (closedPoint (Y.presheaf.stalk (genericPoint Y)))) := by rw [eY]
    _ = (gp Y ≫ π) (closedPoint (Y.presheaf.stalk (genericPoint Y))) := (Scheme.Hom.comp_apply _ _ _).symm
    _ = (spMap θ ≫ gp X) (closedPoint (Y.presheaf.stalk (genericPoint Y))) := by rw [h2]
    _ = gp X (spMap θ (closedPoint (Y.presheaf.stalk (genericPoint Y)))) := Scheme.Hom.comp_apply _ _ _
    _ = genericPoint X := by rw [hc]; exact Scheme.fromSpecStalk_closedPoint

theorem fnOf_appLE {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {π : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (U : X.Opens) (V : Y.Opens)
    (e : V ≤ π ⁻¹ᵁ U) (hU : genericPoint X ∈ U) (hV : genericPoint Y ∈ V) (a : Γ(X, U)) :
    fnOf V hV ((π.appLE U V e).hom a) = θ (fnOf U hU a) := by
  rw [GaussPt.theta_fnOf h U hU (e hV) a]
  simp only [fnOf, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]

theorem linDisj_of_flat : ∀ (T D : Type) [CommRing T] [CommRing D] (a : T →+* D), a.Flat → ∀ (H : Over (Sp T)) [IsIntegral H.left] (H' : Over (Sp D)) [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  intro T D _ _ a ha H _ H' _ π θ hpb hθ n u hu r hr
  classical
  letI : Algebra T D := a.toAlgebra
  haveI : Module.Flat T D := ha
  have hη : π (genericPoint H'.left) = genericPoint H.left := gen_map hθ
  obtain ⟨U, hUa, hηU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 H.left.isBasis_affineOpens)
    (show genericPoint H.left ∈ (⊤ : H.left.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen H.left U hUa
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Γ(H.left, U)) u
  choose A hA using hs
  have hA' : ∀ i, fnOf U hηU (A i) = fnOf U hηU s * u i := fun i => by
    have := hA i; rw [Algebra.smul_def] at this; exact this
  have hs0 : fnOf U hηU s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  letI : Algebra T Γ(H.left, U) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX H.hom U).toAlgebra
  let f : (Fin n → T) →ₗ[T] Γ(H.left, U) :=
    { toFun := fun c => ∑ i, c i • A i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun t c => by simp [Finset.smul_sum, smul_smul] }
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply hu c
    have h1 := congrArg (fnOf U hηU) hc
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zero, Algebra.smul_def, map_mul,
      RingHom.algebraMap_toAlgebra, fnOf_algX, hA'] at h1
    have e : fnOf U hηU s * ∑ i, cst H.hom (c i) * u i = 0 := by
      rw [Finset.mul_sum, ← h1]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    exact (mul_eq_zero.1 e).resolve_left hs0
  have hfD : Function.Injective (f.lTensor D) := Module.Flat.lTensor_preserves_injective_linearMap f hf
  let x := (TensorProduct.piScalarRight T T D (Fin n)).symm r
  have hx : f.lTensor D x = ∑ i, r i ⊗ₜ[T] A i := by
    conv_lhs => rw [show x = ∑ i, (TensorProduct.piScalarRight T T D (Fin n)).symm (Pi.single i (r i)) by
      simp only [x, ← map_sum, Finset.univ_sum_single]]
    simp only [TensorProduct.piScalarRight_symm_single, map_sum, LinearMap.lTensor_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp [f, Pi.single_apply]
  let V' : H'.left.Opens := π ⁻¹ᵁ U ⊓ H'.hom ⁻¹ᵁ ⊤
  have hV' : genericPoint H'.left ∈ V' := ⟨show π _ ∈ U by rw [hη]; exact hηU, trivial⟩
  let E := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens H.hom H'.hom π hpb U hUa
  let y : TensorProduct T Γ(H.left, U) D := TensorProduct.comm T D Γ(H.left, U) (f.lTensor D x)
  have hy : y = ∑ i, A i ⊗ₜ[T] r i := by
    simp only [y, hx, map_sum, TensorProduct.comm_tmul]
  have hEy : fnOf V' hV' (E y) = 0 := by
    rw [hy, map_sum, map_sum]
    have step : ∀ i, fnOf V' hV' (E (A i ⊗ₜ[T] r i)) = θ (fnOf U hηU s * u i) * cst H'.hom (r i) := fun i => by
      rw [show E (A i ⊗ₜ[T] r i) = _ from ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul H.hom H'.hom π hpb U hUa (A i) (r i)]
      rw [map_mul, fnOf_appLE hθ U V' inf_le_left hηU hV', fnOf_algX, hA']
    rw [Finset.sum_congr rfl fun i _ => step i]
    have e : ∑ i, θ (fnOf U hηU s * u i) * cst H'.hom (r i) =
        θ (fnOf U hηU s) * ∑ i, cst H'.hom (r i) * θ (u i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul]; ring
    rw [e, hr, mul_zero]
  have hy0 : y = 0 := by
    have : E y = 0 := fnOf_injective V' hV' (by rw [hEy, map_zero])
    exact E.injective (this.trans E.map_zero.symm)
  have hx0 : x = 0 := by
    apply hfD
    rw [map_zero]
    exact (TensorProduct.comm T D Γ(H.left, U)).injective (hy0.trans (map_zero _).symm)
  have : r = (TensorProduct.piScalarRight T T D (Fin n)) x := by simp only [x, LinearEquiv.apply_symm_apply]
  rw [this, hx0, map_zero]

end GlobalTheory.Desc.FlatLin
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearlyDisjoint_functionField_of_flat_baseChange : ∀ (T D : Type) [CommRing T] [CommRing D] (a : T →+* D), a.Flat → ∀ (H : Over (Sp T)) [IsIntegral H.left] (H' : Over (Sp D)) [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  atlas_forward_decl GlobalTheory.Desc.FlatLin.linDisj_of_flat
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.GaussBC

theorem gp_comp_eq_spMap_cst : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R),
    gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := by
  intro X _ R _ p
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, gp,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.Desc.cst, fnOf, Scheme.functionField]

theorem cst_regAt_zeroAt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X), p x = closedPoint R → ∀ r : R, GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) ∧ (r ∈ maximalIdeal R → GlobalTheory.Cartier.ZeroAt x (GlobalTheory.Desc.cst p r)) := by
  intro R _ _ X _ p x hx r
  have hreg : GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine ⟨hreg, fun hr => zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

end GlobalTheory.Desc.GaussBC

namespace GlobalTheory.Desc.GaussBC

section Span

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁)

theorem zero_mem_spanBy (T : Set F₁) : (0 : F₁) ∈ spanBy c T := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_spanBy {T : Set F₁} {v w : F₁} (hv : v ∈ spanBy c T) (hw : w ∈ spanBy c T) :
    v + w ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  obtain ⟨m, r', t', ht', rfl⟩ := hw
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ht i
    · rw [Fin.append_right]; exact ht' i
  · rw [Fin.sum_univ_add]; simp

theorem mul_mem_spanBy {T : Set F₁} {v : F₁} (hv : v ∈ spanBy c T) (d : R₁) : c d * v ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  exact ⟨n, fun i => d * r i, t, ht, by rw [Finset.mul_sum]; simp only [map_mul, _root_.mul_assoc]⟩

theorem spanBy_induction {T : Set F₁} (p : F₁ → Prop) (h0 : p 0) (hadd : ∀ a b, p a → p b → p (a + b))
    (hmul : ∀ r, ∀ t ∈ T, p (c r * t)) : ∀ v ∈ spanBy c T, p v := by
  rintro v ⟨n, r, t, ht, rfl⟩
  exact Finset.sum_induction _ p hadd h0 fun i _ => hmul (r i) (t i) (ht i)

end Span

theorem regAt_pow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : GlobalTheory.Cartier.RegAt x f) (n : ℕ) :
    GlobalTheory.Cartier.RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem gauss_baseChange : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → GaussAt (GlobalTheory.Desc.cst H'.hom) (maximalIdeal D) θ (regSet y) (regSet y') ∧ θ ⁻¹' (regSet y') = regSet y ∧ LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hff y y' hy hy' hdy hdy'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have hmT := hϖ.maximalIdeal_eq
  have hmD : maximalIdeal D = Ideal.span {a ϖ} := by rw [← hm, hmT, Ideal.map_span, Set.image_singleton]

  have hcomp : θ.comp (cst H.hom) = (cst H'.hom).comp a := by
    obtain ⟨l, hl1, hl2⟩ := hff
    have e1 := gp_comp_eq_spMap_cst H.left T H.hom
    have e2 := gp_comp_eq_spMap_cst H'.left D H'.hom
    have hl : l = gp H'.left := by simpa using hl1
    have key : spMap (θ.comp (cst H.hom)) = spMap ((cst H'.hom).comp a) := by
      calc spMap (θ.comp (cst H.hom)) = spMap θ ≫ spMap (cst H.hom) := by simp [spMap, CommRingCat.ofHom_comp]
        _ = spMap θ ≫ gp H.left ≫ H.hom := by rw [e1]
        _ = l ≫ π ≫ H.hom := by rw [← Category.assoc, ← hl2, Category.assoc]
        _ = gp H'.left ≫ H'.hom ≫ spMap a := by rw [hpb.w, hl]
        _ = spMap (cst H'.hom) ≫ spMap a := by rw [← Category.assoc, e2]
        _ = spMap ((cst H'.hom).comp a) := by simp [spMap, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  set c := cst H'.hom with hc
  set P := c (a ϖ) with hPdef
  have hP : P = θ (cst H.hom ϖ) := by rw [hPdef, ← RingHom.comp_apply, ← hcomp, RingHom.comp_apply]
  obtain ⟨hϖ0, hfac⟩ := GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser T H hH y hy hdy ϖ hmT
  have hP0 : P ≠ 0 := by rw [hP]; exact (map_ne_zero θ).2 hϖ0
  have hPz : GlobalTheory.Cartier.ZeroAt y' P :=
    (cst_regAt_zeroAt D H'.left H'.hom y' hy' (a ϖ)).2 (by rw [hmD]; exact Ideal.subset_span rfl)
  have hreg : ∀ u, GlobalTheory.Cartier.RegAt y u → GlobalTheory.Cartier.RegAt y' (θ u) := by
    intro u hu
    have hpt := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy'
    exact GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp H.left H'.left π θ ⟨_, hff.choose_spec⟩ y' u (hpt ▸ hu)
  have hcreg : ∀ d, GlobalTheory.Cartier.RegAt y' (c d) := fun d => (cst_regAt_zeroAt D H'.left H'.hom y' hy' d).1
  have hc0reg : ∀ t, GlobalTheory.Cartier.RegAt y (cst H.hom t) := fun t => (cst_regAt_zeroAt T H.left H.hom y hy t).1
  have hmod := GlobalTheory.T.thetaSpan_vanishing_eq_uniformiser_mul T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy' ϖ hmT
  set S := spanBy c (θ '' regSet y) with hS
  have hSreg : ∀ v ∈ S, GlobalTheory.Cartier.RegAt y' v :=
    spanBy_induction c _ (regAt_zero y') (fun _ _ h h' => h.add h') (by
      rintro r _ ⟨t, ht, rfl⟩; exact (hcreg r).mul (hreg t ht))
  have hSP : ∀ v ∈ S, ∀ N : ℕ, P ^ N * v ∈ S := by
    intro v hv N
    induction N with
    | zero => simpa using hv
    | succ N ih => rw [pow_succ', _root_.mul_assoc]; exact mul_mem_spanBy c ih _

  have hQ : ∀ v ∈ spanBy c (Set.range θ), ∃ N : ℕ, P ^ N * v ∈ S := by
    refine spanBy_induction c _ ⟨0, by simpa using zero_mem_spanBy c _⟩ ?_ ?_
    · rintro v w ⟨N, hN⟩ ⟨M, hM⟩
      refine ⟨N + M, ?_⟩
      have := add_mem_spanBy c (hSP _ hN M) (hSP _ hM N)
      convert this using 1; ring
    · rintro r _ ⟨u, rfl⟩
      by_cases hu : u = 0
      · exact ⟨0, by simpa [hu] using zero_mem_spanBy c _⟩
      obtain ⟨k, w, hw, rfl⟩ := hfac u hu
      refine ⟨(-k).toNat, ?_⟩
      have hk : ((-k).toNat : ℤ) + k = ((((-k).toNat : ℤ) + k).toNat : ℤ) :=
        (Int.toNat_of_nonneg (by omega)).symm
      have e : P ^ (-k).toNat * (c r * θ (cst H.hom ϖ ^ k * w)) =
          c r * θ (cst H.hom ϖ ^ (((-k).toNat : ℤ) + k).toNat * w) := by
        rw [hP, map_mul, map_mul, map_zpow₀, map_pow]
        have hq : θ (cst H.hom ϖ) ^ (-k).toNat * θ (cst H.hom ϖ) ^ k =
            θ (cst H.hom ϖ) ^ (((-k).toNat : ℤ) + k).toNat := by
          rw [← zpow_natCast, ← zpow_natCast _ (((-k).toNat : ℤ) + k).toNat, ← hk,
            zpow_add₀ ((map_ne_zero θ).2 hϖ0)]
        linear_combination (c r * θ w) * hq
      rw [e]
      exact mul_mem_spanBy c (subset_spanBy c (θ '' regSet y) (Set.mem_image_of_mem θ
        (show _ ∈ regSet y from (regAt_pow (hc0reg ϖ) _).mul hw.regAt))) r

  have hB : ∀ (N : ℕ) (t : H'.left.functionField), GlobalTheory.Cartier.RegAt y' t → P ^ N * t ∈ S → t ∈ S := by
    intro N
    induction N with
    | zero => intro t _ h; simpa using h
    | succ N ih =>
      intro t ht h
      rw [pow_succ', _root_.mul_assoc] at h
      obtain ⟨z₁, hz₁, e⟩ := hmod _ h (hPz.mul ((regAt_pow hPz.regAt N).mul ht))
      have : P ^ N * t = z₁ := mul_left_cancel₀ hP0 e
      exact ih t ht (this ▸ hz₁)
  refine ⟨fun v ⟨d, hd0, hdv⟩ => ⟨fun hv => ?_, fun ⟨s, hs, hsv⟩ => ?_⟩, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hQ _ hdv
    have hirr : Irreducible (a ϖ) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmD
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hirr
    have e : P ^ (N + n) * v = c (↑u⁻¹ : D) * (P ^ N * (c (↑u * a ϖ ^ n) * v)) := by
      rw [hPdef, map_mul, map_pow]
      have : c (↑u⁻¹ : D) * c ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(c (a ϖ) ^ (N + n) * v)) * this
    refine ⟨1, fun h => (maximalIdeal.isMaximal D).ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [map_one, _root_.one_mul]
    exact hB (N + n) v hv (e ▸ mul_mem_spanBy c hN _)
  · obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hs
    have e : v = c (↑u⁻¹ : D) * (c ↑u * v) := by rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    rw [e]; exact (hcreg _).mul (hSreg _ hsv)
  · ext u
    refine ⟨fun h => ?_, fun h => hreg u h⟩
    change GlobalTheory.Cartier.RegAt y' (θ u) at h
    change GlobalTheory.Cartier.RegAt y u
    by_cases hu : u = 0
    · rw [hu]; exact regAt_zero y
    obtain ⟨k, w, hw, rfl⟩ := hfac u hu
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [zpow_natCast]; exact (regAt_pow (hc0reg ϖ) k).mul hw.regAt
    · exfalso
      have hw0 := hw.ne_zero
      obtain ⟨hw1, hw2⟩ := (unitAt_iff hw0).1 hw
      have hθw : GlobalTheory.Cartier.UnitAt y' (θ w) :=
        (unitAt_iff ((map_ne_zero θ).2 hw0)).2 ⟨hreg w hw1, by rw [← map_inv₀]; exact hreg _ hw2⟩
      have hm1 : ((-(k + 1)).toNat : ℤ) = -(k + 1) := Int.toNat_of_nonneg (by omega)
      have e : P⁻¹ = θ (cst H.hom ϖ ^ k * w) * (θ w)⁻¹ * P ^ (-(k + 1)).toNat := by
        rw [map_mul, map_zpow₀, ← hP, _root_.mul_assoc (P ^ k), mul_inv_cancel₀ ((map_ne_zero θ).2 hw0),
          _root_.mul_one, ← zpow_natCast, hm1, ← zpow_add₀ hP0, show k + -(k + 1) = -1 by ring, zpow_neg_one]
      have hPi : GlobalTheory.Cartier.RegAt y' P⁻¹ := by
        rw [e]; exact (h.mul hθw.inv.regAt).mul (regAt_pow hPz.regAt _)
      exact (zeroAt_iff.1 hPz).2 ((unitAt_iff hP0).2 ⟨hPz.regAt, hPi⟩)
  · exact GlobalTheory.T.linearlyDisjoint_functionField_of_flat_baseChange T D a ha H H' π θ hpb ⟨_, hff.choose_spec⟩

end GlobalTheory.Desc.GaussBC
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussProperty_semiAbelian_flat_baseChange_dvr : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → GaussAt (GlobalTheory.Desc.cst H'.hom) (maximalIdeal D) θ (regSet y) (regSet y') ∧ θ ⁻¹' (regSet y') = regSet y ∧ LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  atlas_forward_decl GlobalTheory.Desc.GaussBC.gauss_baseChange
end
