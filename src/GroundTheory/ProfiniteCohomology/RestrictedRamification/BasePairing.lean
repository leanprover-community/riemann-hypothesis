import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.MkFiniteEmbeddingGlobalUniformizer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupKummer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupGlob
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseClass
import GroundTheory.ProfiniteCohomology.PoincarePairs.Natural

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh

universe u

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]

omit [NeZero n] in

theorem localInvU_eq_brauerInvOfIsSepClosure (v : HeightOneSpectrum (𝓞 K.1))
    (x : cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2) :
    localInvU v x = brauerInvOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) x :=
  ((DFunLike.congr_fun (localInvU_eq v) x).trans ((AddMonoidHom.comp_apply _ _ _).trans
    (congrArg _ (AddMonoidHom.comp_apply _ _ _)))).trans
    ((brauerInvZOfIsSepClosure_cohomologyMap_uliftInt_base _ (𝟙 _) (galUnitsToZ _ _) (fun _ => rfl) x).trans
      (congrArg _ (congrArg (fun f => ModuleCat.Hom.hom f x) (cohomologyMap_id 2))))

omit [NeZero n] in

theorem gsRootsOmegaMor_eq_gsRootsLocalMor (v : S) : gsRootsOmegaMor S ιs n v = gsRootsLocalMor S ιs n v := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun ζ => ?_))
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact (restrictRootsOfUnity_coe_apply _ _).trans (gsRootsLocalMor_hom_apply S ιs n v ζ).symm

theorem zmodToQZ_gsLocalInvRoots_eq_localInvU (v : S)
    (z : cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    zmodToQZ n (gsLocalInvRoots S ιs n v z) =
      localInvU (v : HeightOneSpectrum (𝓞 K.1))
        ((cohomologyMap (gsRootsOmegaMor S ιs n v ≫ rootsOfUnityToUnits _ _ n) 2).hom z) := by
  exact (zmodToQZ_gsLocalInvRoots S ιs n v z).trans ((gsLocalInvRootsQZ_eq_brauerInv_base S ιs n v z).trans
    ((congrArg (fun f => brauerInvOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        ((cohomologyMap (f ≫ rootsOfUnityToUnits _ _ n) 2).hom z))
      (gsRootsOmegaMor_eq_gsRootsLocalMor S ιs n v).symm).trans (localInvU_eq_brauerInvOfIsSepClosure _ _).symm))


theorem compactCup_congr_apply {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]
    (φ : ∀ v, H v →ₜ* G) {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
    {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
    {μ₁ μ₂ : A ⊗ B ⟶ C} {μ₁ᵥ μ₂ᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v}
    (h₁ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₁ ≫ c v = resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μ₁ᵥ v)
    (h₂ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₂ ≫ c v = resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μ₂ᵥ v)
    (e : μ₁ = μ₂) (eᵥ : ∀ v, μ₁ᵥ v = μ₂ᵥ v) {r s m : ℕ} (h : r + s = m) (y : compactCohomology φ A Aᵥ a r)
    (x : cohomology B s) :
    compactCup φ μ₁ μ₁ᵥ h₁ h y x = compactCup φ μ₂ μ₂ᵥ h₂ h y x := by
  subst e
  obtain rfl : μ₁ᵥ = μ₂ᵥ := funext eᵥ
  rfl

section ActNatural

variable {H : Type} [Group H]

omit [NeZero n] in

theorem zmodActPairing_comp (D D' Z' : Rep.{0} (ULift.{0} ℤ) H) (hD : ∀ d : D, n • d = 0)
    (hD' : ∀ d : D', n • d = 0) (e : Z' →+ ZMod n) (hZ : ∀ (g : H) (z : Z'), Z'.ρ g z = z) (f : D ⟶ D') :
    zmodActPairing n D Z' hD e hZ ≫ f = (f ⊗ₘ 𝟙 Z') ≫ zmodActPairing n D' Z' hD' e hZ := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun (d : D) (z : Z') => ?_))
  change f.hom ((zmodActPairing n D Z' hD e hZ).hom (d ⊗ₜ[ULift.{0} ℤ] z)) =
    (zmodActPairing n D' Z' hD' e hZ).hom (f.hom d ⊗ₜ[ULift.{0} ℤ] z)
  rw [zmodActPairing_tmul, zmodActPairing_tmul, map_zsmul]

end ActNatural

omit [NeZero n] in

theorem zmodMulPairingRight_gsRoots_eq :
    zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n) =
      zmodActPairing n (gsRoots S n) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
        (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (ζ : gsRoots S n) (a : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) => ?_))
  change (zmodMulPairing n (gsRoots S n) (nsmul_gsRoots S n)).hom (a ⊗ₜ[ULift.{0} ℤ] ζ) =
    (zmodActPairing n (gsRoots S n) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
      (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl)).hom (ζ ⊗ₜ[ULift.{0} ℤ] a)
  exact (zmodMulPairing_tmul n _ _ a.down ζ).trans (zmodActPairing_tmul n (gsRoots S n)
    (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
    (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) ζ a).symm

section ResPairing

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (ψ : H →* G) {A B C : Rep.{u} k G} {C' : Rep.{u} k H}

theorem resFunctor_map_comp_id_comp (μ : A ⊗ B ⟶ C) (g : Rep.res ψ C ⟶ C') :
    (Rep.resFunctor ψ).map (μ ≫ 𝟙 C) ≫ g =
      resTensorHom ψ (𝟙 (Rep.res ψ A)) (𝟙 (Rep.res ψ B)) ≫ ((Rep.resFunctor ψ).map μ ≫ g) :=
  (congrArg (· ≫ g) ((congrArg (Rep.resFunctor ψ).map (Category.comp_id μ)).trans
    ((Category.comp_id _).symm.trans (resFunctor_map_comp_id ψ μ)))).trans (Category.assoc _ _ _)

theorem resFunctor_map_id_tensor_comp (μ : A ⊗ B ⟶ C) (g : Rep.res ψ C ⟶ C')
    (ν : Rep.res ψ A ⊗ Rep.res ψ B ⟶ C') (e : (Rep.resFunctor ψ).map μ ≫ g = ν) :
    (Rep.resFunctor ψ).map ((𝟙 A ⊗ₘ 𝟙 B) ≫ μ) ≫ g = resTensorHom ψ (𝟙 (Rep.res ψ A)) (𝟙 (Rep.res ψ B)) ≫ ν :=
  (congrArg (fun f => (Rep.resFunctor ψ).map f ≫ g)
    (((congrArg (· ≫ μ) (MonoidalCategory.id_tensorHom_id A B)).trans (Category.id_comp μ)).trans
      (Category.comp_id μ).symm)).trans
    ((resFunctor_map_comp_id_comp ψ μ g).trans (congrArg (resTensorHom ψ (𝟙 _) (𝟙 _) ≫ ·) e))

end ResPairing

abbrev gsZmodPairing :
    gsRoots S n ⊗ zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n ⟶ gsRoots S n :=
  zmodActPairing n (gsRoots S n) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (nsmul_gsRoots S n)
    (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl)

abbrev gsZmodPairingᵥ (v : S) :
    galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n ⊗
      Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) ⟶
    galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n :=
  zmodActPairing n _ _ (nsmul_galRootsOfUnity_eq_zero' n) (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom
    (fun _ _ => rfl)

omit [NeZero n] in
theorem resFunctor_map_gsZmodPairing (v : S) :
    (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (gsZmodPairing S n) =
      zmodActPairing n (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
        (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) (nsmul_gsRoots S n)
        (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ => rfl))

omit [NeZero n] in
theorem gsZmodPairing_hμ (v : S) :
    (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (gsZmodPairing S n) ≫ gsRootsOmegaMor S ιs n v =
      resTensorHom (gsFinFamily S ιs v).toMonoidHom (gsRootsOmegaMor S ιs n v) (𝟙 _) ≫ gsZmodPairingᵥ S ιs n v :=
  (congrArg (· ≫ gsRootsOmegaMor S ιs n v) (resFunctor_map_gsZmodPairing S ιs n v)).trans
    (zmodActPairing_comp n (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
      (galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
      (Rep.res (gsFinFamily S ιs v).toMonoidHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n))
      (nsmul_gsRoots S n) (nsmul_galRootsOfUnity_eq_zero' n)
      (AddEquiv.ulift : ULift.{0} (ZMod n) ≃+ ZMod n).toAddMonoidHom (fun _ _ => rfl) (gsRootsOmegaMor S ιs n v))

omit [NeZero n] in

theorem gsRootsComparison_compactCupRes (y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2)
    (x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    (gsRootsComparison S ιs n 3).hom (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) =
      compactCup (gsFinFamily S ιs) (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
        (show 2 + 1 = 3 from rfl) ((gsRootsComparison S ιs n 2).hom y) x := by
  have hg : ∀ v, 𝟙 (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v =
      (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (𝟙 (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v :=
    fun _ => Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  have e1 := compactCohomologyMap_compactCup (gsFinFamily S ιs) (A := gsRoots S n)
    (B := zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (C := gsRoots S n) (C' := gsRoots S n)
    (Aᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
    (Cᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) (C'ᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (a := fun _ => 𝟙 _) (c := fun _ => 𝟙 _) (c' := gsRootsOmegaMor S ιs n)
    (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
    (fun v => (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map
      (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)))
    (fun v => resFunctor_map_comp_id _ _) (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n) hg
    (fun v => resFunctor_map_comp_id_comp _ _ _) (show 2 + 1 = 3 from rfl) y x
  have e2 := compactCup_compactCohomologyMap (gsFinFamily S ιs) (A := gsRoots S n) (A' := gsRoots S n)
    (B := zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (C := gsRoots S n)
    (Aᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) (A'ᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (Cᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (a := fun _ => 𝟙 _) (a' := gsRootsOmegaMor S ιs n) (c := gsRootsOmegaMor S ιs n)
    (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n) hg
    (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
    (fun v => resFunctor_map_id_tensor_comp _ _ _ _ (gsZmodPairing_hμ S ιs n v)) (show 2 + 1 = 3 from rfl) y x
  have eμ : zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n) ≫ 𝟙 (gsRoots S n) =
      (𝟙 (gsRoots S n) ⊗ₘ 𝟙 (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)) ≫ gsZmodPairing S n :=
    ((Category.comp_id _).trans (zmodMulPairingRight_gsRoots_eq S n)).trans
      ((congrArg (· ≫ gsZmodPairing S n) (MonoidalCategory.id_tensorHom_id _ _)).trans (Category.id_comp _)).symm
  have eμᵥ : ∀ v, (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map
      (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v =
      (gsRootsOmegaMor S ιs n v ⊗ₘ 𝟙 _) ≫ gsZmodPairingᵥ S ιs n v := fun v =>
    (congrArg (fun f => (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map f ≫ gsRootsOmegaMor S ιs n v)
      (zmodMulPairingRight_gsRoots_eq S n)).trans (gsZmodPairing_hμ S ιs n v)
  refine e1.trans (Eq.trans ?_ e2.symm)
  exact compactCup_congr_apply (gsFinFamily S ιs) _ _ eμ eμᵥ (show 2 + 1 = 3 from rfl) y x

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

section ConstCup

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {H : ι → Type} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]
  (φ : ∀ v, H v →ₜ* G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem cupCochain_const_left {A B : Rep.{0} k G} {q n : ℕ} (h : 0 + q = n) (m : A) (g : (Fin q → G) → B)
    (x : Fin n → G) :
    cupCochain h (fun _ => m) g x = m ⊗ₜ[k] g (fun j : Fin q => x ⟨j, by omega⟩) := by
  rw [cupCochain_apply]
  congr 1
  have h0 : Fin.partialProd x ⟨0, by omega⟩ = 1 := Fin.partialProd_zero x
  rw [h0, map_one, Module.End.one_apply]
  congr 1
  funext j
  congr 1
  ext
  simp

variable {U X B : Rep.{0} k G} [IsDiscreteRep U] [IsDiscreteRep X] [IsDiscreteRep B] (j : U ⟶ X)
  (μU : U ⊗ B ⟶ U) (μX : X ⊗ B ⟶ X) (hj : μU ≫ j = (j ⊗ₘ 𝟙 B) ≫ μX)

noncomputable def constCupSub (m : X) {s : ℕ} (e : (cochainsComplex B).X s) (z : (cochainsComplex U).X s) :
    (cochainsComplex X).X s :=
  cupPairingCochains μX (show 0 + s = s by omega) (constCochain X m) e - ((cochainsMap j).f s).hom z

theorem cochainOf_constCupSub (m : X) {s : ℕ} (e : (cochainsComplex B).X s) (z : (cochainsComplex U).X s)
    (σ : Fin s → G) :
    cochainOf X (constCupSub j μX m e z) σ = μX.hom (m ⊗ₜ[k] cochainOf B e σ) - j.hom (cochainOf U z σ) := by
  change cochainOf X (cupPairingCochains μX (show 0 + s = s by omega) (constCochain X m) e) σ -
    cochainOf X (((cochainsMap j).f s).hom z) σ = _
  rw [cochainOf_cochainsMap_f, cochainOf_cupPairingCochains]
  congr 1
  refine (congrArg μX.hom (cupCochain_const_left (show 0 + s = s by omega) m _ σ)).trans ?_
  congr 3

include hj in

theorem d_constCupSub (m : X) (x : (cochainsComplex U).X 1)
    (hx : ((cochainsMap j).f 1).hom x = ((cochainsComplex X).d 0 1).hom (constCochain X m))
    {s : ℕ} (e : (cochainsComplex B).X s) (he : ((cochainsComplex B).d s (s + 1)).hom e = 0)
    (z : (cochainsComplex U).X s)
    (hz : ((cochainsComplex U).d s (s + 1)).hom z = cupPairingCochains μU (show 1 + s = s + 1 by omega) x e) :
    ((cochainsComplex X).d s (s + 1)).hom (constCupSub j μX m e z) = 0 := by
  have L := (cupLeibniz μX).leibniz (show 0 + s = s by omega) (constCochain X m) e
  change ((cochainsComplex X).d s (s + 1)).hom (cupPairingCochains μX _ (constCochain X m) e) = _ at L
  rw [constCupSub, map_sub, L, he, map_zero, smul_zero, add_zero, ← hx,
    hom_apply_hom_apply_eq_of_comp_eq ((cochainsMap j).comm s (s + 1)) z, hz, sub_eq_zero]
  apply cochainOf_injective
  funext σ
  rw [cochainOf_cochainsMap_f]
  exact (cupCochain_tensorHom_eq' ((j ⊗ₘ 𝟙 B) ≫ μX) μX j rfl (show 1 + s = s + 1 by omega) (cochainOf U x)
    (cochainOf B e) σ).symm.trans (congrArg (fun f : U ⊗ B ⟶ X =>
      f.hom (cupCochain (show 1 + s = s + 1 by omega) (cochainOf U x) (cochainOf B e) σ)) hj.symm)

variable (Ωᵥ : ∀ v, Rep.{0} k (H v)) [∀ v, IsDiscreteRep (Ωᵥ v)] (l : ∀ v, Rep.res (φ v).toMonoidHom X ⟶ Ωᵥ v)
  (μΩ : ∀ v, Ωᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Ωᵥ v)
  (hl : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μX ≫ l v = resTensorHom (φ v).toMonoidHom (l v) (𝟙 _) ≫ μΩ v)

include hj hl in

theorem exists_compactCup_const
    (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μU ≫ ((Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) =
      resTensorHom (φ v).toMonoidHom ((Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) (𝟙 _) ≫ μΩ v)
    (Xc : (compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).cycles 1)
    (m : X) (x : (cochainsComplex U).X 1)
    (hX1 : (((compactCochains φ U Ωᵥ _).iCycles 1).hom Xc).1 = x) (y : ∀ v, Ωᵥ v)
    (hX2 : (((compactCochains φ U Ωᵥ _).iCycles 1).hom Xc).2 = piConst Ωᵥ y) (hy : ∀ v, y v = (l v).hom m)
    (hx : ((cochainsMap j).f 1).hom x = ((cochainsComplex X).d 0 1).hom (constCochain X m))
    {s : ℕ} (e : (cochainsComplex B).cycles s) (z : (cochainsComplex U).X s)
    (hz : ((cochainsComplex U).d s (s + 1)).hom z =
      cupPairingCochains μU (show 1 + s = s + 1 by omega) x (((cochainsComplex B).iCycles s).hom e)) :
    ∃ W : cocycles X s, cochainOf X (cocycleι X s W) =
        cochainOf X (constCupSub j μX m (((cochainsComplex B).iCycles s).hom e) z) ∧
      compactCup φ μU μΩ hμ (show 1 + s = s + 1 by omega)
          (((compactCochains φ U Ωᵥ _).homologyπ 1).hom Xc) (((cochainsComplex B).homologyπ s).hom e) =
        (localToCompact φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) s).hom
          (fun v => (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (l v) s).hom
            (cohomologyπ X s W)) := by
  have hdW := d_constCupSub j μU μX hj m x hx (((cochainsComplex B).iCycles s).hom e)
    (iCycles_d_apply _ s (s + 1) e) z hz
  let W : cocycles X s := (cochainsComplex X).cyclesMk _ (s + 1) (by simp) hdW
  have hW : cochainOf X (cocycleι X s W) = cochainOf X (constCupSub j μX m (((cochainsComplex B).iCycles s).hom e) z) :=
    congrArg (cochainOf X) ((cochainsComplex X).i_cyclesMk _ _ _ _)
  refine ⟨W, hW, ?_⟩
  obtain ⟨w, hw1, hw2⟩ := LeibnizPairing.exists_coconeLeft_homology_eq_homologyδ
    (LeibnizPairing.pi fun v => cupLeibniz (μΩ v))
    (localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) fun _ => 𝟙 _) (cupLeibniz μU)
    (localRes_cupPairingCochains φ μU μΩ hμ) (show 0 + 1 + s = s + 1 by omega) Xc e z
    (hz.trans (congrArg (fun a => cupPairingCochains μU (show 1 + s = s + 1 by omega) a
      (((cochainsComplex B).iCycles s).hom e)) hX1.symm))
  refine hw2.trans ((homologyδ_homologyπ_eq_localToCompact φ w).trans (congrArg _ (funext fun v => ?_)))
  rw [cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMapAlong, hW]
  funext σ
  have e1 := iCycles_cyclesMap_apply (piProj (fun v => cochainsComplex (Ωᵥ v)) v) s w
  rw [cocycleι, e1, piProj_f_hom_apply, hw1, cochainOf_constCupSub, map_sub]
  change cochainOf (Ωᵥ v) (cupPairingCochains (μΩ v) (show 0 + s = s by omega)
      ((((compactCochains φ U Ωᵥ _).iCycles 1).hom Xc).2 v)
      (((localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) fun _ => 𝟙 _).f s).hom
        (((cochainsComplex B).iCycles s).hom e) v)) σ -
    cochainOf (Ωᵥ v) (((localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v).f s).hom z v) σ = _
  rw [hX2, piConst_apply, cochainOf_cupPairingCochains, cochainOf_localRes_f_apply]
  congr 1
  refine (congrArg (μΩ v).hom (cupCochain_const_left (show 0 + s = s by omega) (y v) _ σ)).trans ?_
  rw [hy v]
  refine Eq.trans ?_ (congrArg (fun f => f.hom ((m ⊗ₜ[k] cochainOf B (((cochainsComplex B).iCycles s).hom e)
    (⇑(φ v).toMonoidHom ∘ σ)) : Rep.res (φ v).toMonoidHom (X ⊗ B))) (hl v)).symm
  rfl

end ConstCup

section Exists

theorem nsmul_apply_eq_zero_of {F M N : Type*} [AddMonoid M] [AddMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (n : ℕ) {y : M} (hy : n • y = 0) : n • f y = 0 := by
  rw [← map_nsmul, hy, map_zero]

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B C : Rep.{0} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

theorem exists_d_eq_cupPairingCochains (μ : A ⊗ B ⟶ C) {p q m : ℕ} (h : p + q = m + 1) (x : cocycles A p)
    (y : cocycles B q) (h0 : cupPairing μ h (cohomologyπ A p x) (cohomologyπ B q y) = 0) :
    ∃ z : (cochainsComplex C).X m, ((cochainsComplex C).d m (m + 1)).hom z =
      cupPairingCochains μ h (cocycleι A p x) (cocycleι B q y) := by
  rw [cupPairing_cohomologyπ] at h0
  have h1 := (homologyπ_eq_zero_iff (cochainsComplex C) _).1 h0
  rw [CochainComplex.prev_nat_succ] at h1
  obtain ⟨z, hz⟩ := h1
  refine ⟨z, hz.trans (cochainOf_injective (funext fun σ => ?_))⟩
  exact (cochainOf_cocycleι_cyclesMap_cupCocycles μ h x y σ).trans rfl

end Exists

section Units

theorem toMul_zsmul_sub_mul_inv_mem {M : Type*} [CommGroup M] (H : Subgroup M) (u : M) (b : ℤ) (w : M) (hw : w ∈ H) :
    Additive.toMul (b • Additive.ofMul u - Additive.ofMul w) * (u ^ b)⁻¹ ∈ H := by
  have e : Additive.toMul (b • Additive.ofMul u - Additive.ofMul w) * (u ^ b)⁻¹ = w⁻¹ := by
    rw [toMul_sub, toMul_zsmul, toMul_ofMul, toMul_ofMul, div_eq_mul_inv, mul_comm (u ^ b) w⁻¹, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [e]
  exact H.inv_mem hw

theorem toMul_mem_of_eq {M : Type*} [CommGroup M] (H : Subgroup M) (u : M) (b : ℤ) (w : M) (X : Additive M)
    (hX : X = b • Additive.ofMul u - Additive.ofMul w) (hw : w ∈ H) : Additive.toMul X * (u ^ b)⁻¹ ∈ H := by
  rw [hX]
  exact toMul_zsmul_sub_mul_inv_mem H u b w hw

end Units

section Concrete

open IsDedekindDomain NumberField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

noncomputable abbrev gsPairingK :
    galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ⊗ intRepTriv (galUnramifiedOutside K.1 ℚ̄ S) ⟶
      galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) :=
  intActPairing _ _ (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom (fun _ _ => rfl)

theorem gsPairingK_tmul (x : galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S))
    (m : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)) :
    (gsPairingK S).hom (x ⊗ₜ[ULift.{0} ℤ] m) = m.down • x :=
  intActPairing_tmul _ _ _ _ x m

theorem gsPairingU_sUnitsToUnits :
    gsPairingU S ≫ sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S) =
      (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ⊗ₘ 𝟙 (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))) ≫
        gsPairingK S := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (x : galSUnitsMax K.1 ℚ̄ S) (m : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)) => ?_))
  change (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom ((gsPairingU S).hom (x ⊗ₜ[ULift.{0} ℤ] m)) =
    (gsPairingK S).hom ((sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom x ⊗ₜ[ULift.{0} ℤ] m)
  exact (congrArg (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom (gsPairingU_tmul S x m)).trans
    ((map_zsmul (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom m.down x).trans
      (gsPairingK_tmul S _ m).symm)

theorem gsPairingK_gsUnitsLocalMor (v : S) :
    (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (gsPairingK S) ≫ gsUnitsLocalMor.{0} S ιs v =
      resTensorHom (gsFinFamily S ιs v).toMonoidHom (gsUnitsLocalMor.{0} S ιs v) (𝟙 _) ≫
        mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext'
    fun (x : galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S))
      (m : intRepTriv (galUnramifiedOutside K.1 ℚ̄ S)) => ?_))
  change (gsUnitsLocalMor.{0} S ιs v).hom ((gsPairingK S).hom (x ⊗ₜ[ULift.{0} ℤ] m)) =
    (mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))).hom ((gsUnitsLocalMor.{0} S ιs v).hom x ⊗ₜ[ULift.{0} ℤ]
      (ULift.up m.down : Rep.res (gsFinFamily S ιs v).toMonoidHom (intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))))
  exact (congrArg (gsUnitsLocalMor.{0} S ιs v).hom (gsPairingK_tmul S x m)).trans
    ((map_zsmul (gsUnitsLocalMor.{0} S ιs v).hom m.down x).trans
      (mulIntRight_tmul (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) _ m.down).symm)

variable [Fintype S] (n ℓ k : ℕ) [NeZero n] (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

set_option maxHeartbeats 1600000 in
omit [Fintype S] in
include hℓ hnk hS in

theorem exists_gsUnitsData_cup_bock (t : sInvariantSubgroup (F := K.1) ℚ̄ S)
    (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    ∃ W : cocycles (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2,
      (∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) *
          ((t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^ bockInt (zmodCocycleHom z) g h)⁻¹ ∈ sUnitsMax K.1 ℚ̄ S) ∧
      compactCup (gsFinFamily S ιs) (gsPairingU S)
          (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
          (show 1 + 2 = 2 + 1 from rfl) (gsUnitsData S ιs (Additive.ofMul t, 0))
          ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom
            (cohomologyπ _ 1 z)) =
        (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
          (fun v => (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
            (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 W)) := by
  have hb := exists_cocycle_δ_bockSeq (NeZero.ne n) z
  obtain ⟨x₁, hx₁π, hx₁v⟩ := hb
  let c : cocycles (galSUnitsMax K.1 ℚ̄ S) 1 :=
    (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).cyclesMk (sInvCochain S t) 2 (by simp) (d_sInvCochain S t)
  have hc : cocycleι _ 1 c = sInvCochain S t := (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).i_cyclesMk _ _ _ _
  have hnz : n • cohomologyπ (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1 z = 0 :=
    nsmul_cohomology_eq_zero _ (fun a => ULift.ext _ _ (by
      change n • a.down = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])) 1 _
  have hb' : n • cohomologyπ _ 2 x₁ = 0 :=
    (congrArg (n • ·) hx₁π).trans (nsmul_apply_eq_zero_of
      (δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom n hnz)
  have h0 : cupPairing (gsPairingU S) (show 1 + 2 = 2 + 1 from rfl) (cohomologyπ _ 1 c) (cohomologyπ _ 2 x₁) = 0 := by
    refine eq_zero_of_h3_sUnits K S ℓ hℓ hS _ k ?_
    rw [← hnk]
    exact nsmul_apply_eq_zero_of (cupPairing (gsPairingU S) (show 1 + 2 = 2 + 1 from rfl) (cohomologyπ _ 1 c)) n hb'
  have hz := exists_d_eq_cupPairingCochains (gsPairingU S) (show 1 + 2 = 2 + 1 from rfl) c x₁ h0
  have hz₀' := hz.choose_spec.trans (congrArg (fun a => cupPairingCochains (gsPairingU S)
    (show 1 + 2 = 2 + 1 from rfl) a (cocycleι _ 2 x₁)) hc)
  have hX := iCycles_dataCycle (gsFinFamily S ιs) (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))
    (fun v : S => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsUnitsLocalMor.{0} S ιs)
    (sInvCochain S (Additive.toMul ((Additive.ofMul t, 0) : GsUnitsDatum S).1))
    (fun v => dataLocalUnit S ιs (Additive.toMul ((Additive.ofMul t, 0) : GsUnitsDatum S).1) v
      (((Additive.ofMul t, 0) : GsUnitsDatum S).2 v))
    (d_sInvCochain S _) (fun v σ => dataLocalUnit_compat S ιs (Additive.toMul ((Additive.ofMul t, 0) : GsUnitsDatum S).1)
      ((Additive.ofMul t, 0) : GsUnitsDatum S).2 v σ)
  have key := exists_compactCup_const (U := galSUnitsMax K.1 ℚ̄ S)
    (X := galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) (B := intRepTriv (galUnramifiedOutside K.1 ℚ̄ S))
    (gsFinFamily S ιs) (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))
    (gsPairingU S) (gsPairingK S) (gsPairingU_sUnitsToUnits S) (fun v : S => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsUnitsLocalMor.{0} S ιs)
    (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingK_gsUnitsLocalMor S ιs)
    (gsPairingU_hμ S ιs) _ (Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) (sInvCochain S t)
    (congrArg Prod.fst hX) _ (congrArg Prod.snd hX)
    (fun v => (congrArg (· + sInvLocalHom S ιs v (Additive.ofMul t)) (map_zero (localUnitsAlgHom S v))).trans
      (zero_add _))
    (cochainsMap_sUnitsToUnits_sInvCochain S t) x₁ hz.choose hz₀'
  refine ⟨key.choose, fun g h => ?_, ?_⟩
  · have e1 := (congrFun key.choose_spec.1 ![g, h]).trans (cochainOf_constCupSub _ _ _ _ _ _)
    have e2 := gsPairingK_tmul S (Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ))
      (cochainOf _ (cocycleι _ 2 x₁) ![g, h])
    have e3 := sUnitsToUnits_hom_apply S (maxUnramifiedOutside K.1 ℚ̄ S) (cochainOf _ hz.choose ![g, h])
    exact toMul_mem_of_eq (sUnitsMax K.1 ℚ̄ S) _ _ _ _
      (e1.trans (congrArg₂ (· - ·) (e2.trans (congrArg (· • Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ))
        (hx₁v g h))) e3))
      (Additive.toMul (cochainOf _ hz.choose ![g, h]) : sUnitsMax K.1 ℚ̄ S).2
  · exact (congrArg _ hx₁π.symm).trans key.choose_spec.2

end Concrete

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section General

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {H : ι → Type} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)] [∀ v, IsTopologicalGroup (H v)]
  (φ : ∀ v, H v →ₜ* G) {U X : Rep.{0} k G} [IsDiscreteRep U] (j : U ⟶ X)
  (Ωᵥ : ∀ v, Rep.{0} k (H v)) [∀ v, IsDiscreteRep (Ωᵥ v)] (l : ∀ v, Rep.res (φ v).toMonoidHom X ⟶ Ωᵥ v)

theorem exists_dataCycle_eq
    (c : (compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).cycles 1) :
    ∃ (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v) (hx : ((cochainsComplex U).d 1 2).hom x = 0)
      (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v),
      c = dataCycle φ j Ωᵥ l x y hx hy := by
  let q : (cochainsComplex U).X 1 × (piComplex fun v => cochainsComplex (Ωᵥ v)).X 0 :=
    ((compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).iCycles 1).hom c
  have hd : (mappingCoconeNatD (localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v) 1).hom
      q = 0 :=
    hom_apply_hom_apply_of_comp_eq
      ((compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).iCycles_d 1 2) c
  have h2 := (mappingCoconeNatD_apply _ 1 q.1 q.2).symm.trans hd
  let y : ∀ v, Ωᵥ v := fun v => cochainOf (Ωᵥ v) (q.2 v) Fin.elim0
  have hyy : q.2 = piConst Ωᵥ y := funext fun v => cochainOf_injective (funext fun σ => by
    rw [Subsingleton.elim σ Fin.elim0]
    rfl)
  have hx : ((cochainsComplex U).d 1 2).hom q.1 = 0 := congrArg Prod.fst h2
  have hsnd := congrArg Prod.snd h2
  have hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U q.1 ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (y v) - y v := fun v σ => by
    have e := congrArg (fun w => cochainOf (Ωᵥ v) (w v) ![σ]) hsnd
    simp only at e
    rw [shiftNegOneD_succ_apply, shiftNegOneSucc_apply, hyy] at e
    change cochainOf (Ωᵥ v) ((((localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v).f 1).hom q.1) v
      + -(((piComplex fun v => cochainsComplex (Ωᵥ v)).d 0 1).hom (piConst Ωᵥ y)) v) ![σ] = 0 at e
    rw [cochainOf_add, cochainOf_neg', Pi.add_apply, Pi.neg_apply, piComplex_d_hom_apply, piConst_apply,
      cochainOf_d_constCochain, cochainOf_localRes_f_apply, add_neg_eq_zero] at e
    refine Eq.trans ?_ e
    have hh : (⇑(φ v).toMonoidHom ∘ ![σ]) = ![(φ v).toMonoidHom σ] := by
      funext i
      fin_cases i
      rfl
    rw [hh]
    rfl
  refine ⟨q.1, y, hx, hy, ?_⟩
  apply (ModuleCat.mono_iff_injective ((compactCochains φ U Ωᵥ _).iCycles 1)).1 inferInstance
  rw [iCycles_dataCycle]
  exact Prod.ext rfl hyy

theorem exists_coboundary_of_subsingleton [IsDiscreteRep X] (hX : Subsingleton (cohomology X 1))
    (x : (cochainsComplex U).X 1) (hx : ((cochainsComplex U).d 1 2).hom x = 0) :
    ∃ T : X, ∀ σ : G, j.hom (cochainOf U x ![σ]) = X.ρ σ T - T := by
  have hx' : ((cochainsComplex X).d 1 (1 + 1)).hom (((cochainsMap j).f 1).hom x) = 0 :=
    (hom_apply_hom_apply_eq_of_comp_eq ((cochainsMap j).comm 1 2) x).trans (by rw [hx, map_zero])
  obtain ⟨z, hz⟩ := exists_iCycles_eq_of_d_eq_zero _ 1 _ hx'
  have h0 : ((cochainsComplex X).homologyπ (0 + 1)).hom z = 0 := Subsingleton.elim (α := cohomology X 1) _ _
  obtain ⟨w, hw⟩ := (homologyπ_succ_eq_zero_iff _ 0 z).1 h0
  refine ⟨cochainOf X w Fin.elim0, fun σ => ?_⟩
  have e : cochainOf X (((cochainsComplex X).d 0 (0 + 1)).hom w) ![σ] =
      cochainOf X (((cochainsMap j).f 1).hom x) ![σ] := congrArg (fun c => cochainOf X c ![σ]) (hw.trans hz)
  rw [cochainOf_cochainsMap_f] at e
  refine e.symm.trans ?_
  have hw0 : w = constCochain X (cochainOf X w Fin.elim0) :=
    cochainOf_injective (funext fun τ => by rw [Subsingleton.elim τ Fin.elim0]; rfl)
  rw [hw0, cochainOf_d_constCochain]
  rfl

theorem homologyπ_dataCycle_of_boundary (α : U) (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v)
    (hx : ((cochainsComplex U).d 1 2).hom x = 0)
    (hy : ∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v)
    (hxα : ∀ σ : G, cochainOf U x ![σ] = U.ρ σ α - α) (hyα : ∀ v, y v = (l v).hom (j.hom α)) :
    ((compactCochains φ U Ωᵥ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v)).homologyπ 1).hom
      (dataCycle φ j Ωᵥ l x y hx hy) = 0 := by
  refine (homologyπ_succ_eq_zero_iff _ 0 (dataCycle φ j Ωᵥ l x y hx hy)).2
    ⟨((constCochain U α, PUnit.unit) : (cochainsComplex U).X 0 ×
      shiftNegOneX (piComplex fun v => cochainsComplex (Ωᵥ v)) 0), ?_⟩
  rw [iCycles_dataCycle]
  refine (mappingCoconeNatD_apply _ 0 (constCochain U α) PUnit.unit).trans (Prod.ext ?_ ?_)
  · apply cochainOf_injective
    funext σ
    rw [cochainOf_d_constCochain]
    change _ = cochainOf U x σ
    have hσ : σ = ![σ 0] := by
      funext i
      fin_cases i
      rfl
    rw [hσ, hxα]
    rfl
  · change (((localRes φ U Ωᵥ fun v => (Rep.resFunctor (φ v).toMonoidHom).map j ≫ l v).f 0).hom
      (constCochain U α) : (piComplex fun v => cochainsComplex (Ωᵥ v)).X 0) + 0 = piConst Ωᵥ y
    rw [add_zero]
    funext v
    rw [piConst_apply]
    apply cochainOf_injective
    funext h
    rw [cochainOf_localRes_f_apply, cochainOf_constCochain, cochainOf_constCochain, hyα]
    rfl

theorem dataHom_surjective {D : Type} [AddCommGroup D] (xOf : D →+ (cochainsComplex U).X 1) (yOf : D →+ (∀ v, Ωᵥ v))
    (hx : ∀ d, ((cochainsComplex U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d v (σ : H v), (l v).hom (j.hom (cochainOf U (xOf d) ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (yOf d v) - yOf d v)
    (hd : ∀ (x : (cochainsComplex U).X 1) (y : ∀ v, Ωᵥ v), ((cochainsComplex U).d 1 2).hom x = 0 →
      (∀ v (σ : H v), (l v).hom (j.hom (cochainOf U x ![(φ v).toMonoidHom σ])) = (Ωᵥ v).ρ σ (y v) - y v) →
        ∃ d, xOf d = x ∧ yOf d = y) :
    Function.Surjective (dataHom φ j Ωᵥ l xOf yOf hx hy) := by
  intro h
  obtain ⟨c, rfl⟩ := homologyπ_surjective _ 1 h
  obtain ⟨x, y, hx', hy', rfl⟩ := exists_dataCycle_eq φ j Ωᵥ l c
  obtain ⟨d, hxd, hyd⟩ := hd x y hx' hy'
  exact ⟨d, (dataHom_apply φ j Ωᵥ l xOf yOf hx hy d).trans
    (congrArg _ (dataCycle_congr φ j Ωᵥ l hxd hyd _ _ _ _))⟩

theorem dataHom_eq_zero_of_boundary {D : Type} [AddCommGroup D] (xOf : D →+ (cochainsComplex U).X 1)
    (yOf : D →+ (∀ v, Ωᵥ v)) (hx : ∀ d, ((cochainsComplex U).d 1 2).hom (xOf d) = 0)
    (hy : ∀ d v (σ : H v), (l v).hom (j.hom (cochainOf U (xOf d) ![(φ v).toMonoidHom σ])) =
      (Ωᵥ v).ρ σ (yOf d v) - yOf d v) (d : D) (α : U)
    (hxα : ∀ σ : G, cochainOf U (xOf d) ![σ] = U.ρ σ α - α) (hyα : ∀ v, yOf d v = (l v).hom (j.hom α)) :
    dataHom φ j Ωᵥ l xOf yOf hx hy d = 0 :=
  (dataHom_apply φ j Ωᵥ l xOf yOf hx hy d).trans
    (homologyπ_dataCycle_of_boundary φ j Ωᵥ l α _ _ _ _ hxα hyα)

end General

section Concrete

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

theorem ρ_sub_eq_of_sub_eq {F : Type} [Monoid F] (B : Rep.{0} (ULift.{0} ℤ) F) (σ : F) {y m : B}
    (e : B.ρ σ m - m = B.ρ σ y - y) : B.ρ σ (y - m) = y - m := by
  rw [map_sub]
  exact sub_eq_sub_iff_sub_eq_sub.mp e.symm

theorem toMul_mem_sInvariantSubgroup (T : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
    (x : (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).X 1)
    (hT : ∀ σ, (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom (cochainOf _ x ![σ]) =
      (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ T - T) :
    Additive.toMul T ∈ sInvariantSubgroup (F := K.1) ℚ̄ S := fun σ => by
  have h' : galUnitsHom K.1 _ σ (Additive.toMul T) * (Additive.toMul T)⁻¹ =
      ((Additive.toMul (cochainOf _ x ![σ]) : sUnitsOf S (maxUnramifiedOutside K.1 ℚ̄ S)) :
        (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) := (congrArg Additive.toMul (hT σ)).symm
  rw [h']
  exact (Additive.toMul (cochainOf _ x ![σ])).2

theorem sInvCochain_eq_of (t : sInvariantSubgroup (F := K.1) ℚ̄ S) (x : (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).X 1)
    (hT : ∀ σ, (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom (cochainOf _ x ![σ]) =
      (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ (Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) -
        Additive.ofMul (t : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) :
    sInvCochain S t = x := cochainOf_injective (funext fun σ => by
  have hσ : σ = ![σ 0] := by
    funext i
    fin_cases i
    rfl
  rw [hσ]
  exact sUnitsToUnits_injective S (maxUnramifiedOutside K.1 ℚ̄ S) ((sUnitsToUnits_sInvRatio S t (σ 0)).trans
    (hT (σ 0)).symm))

theorem exists_unitsToInvariants_eq_local (v : HeightOneSpectrum (𝓞 K.1))
    (y : galUnits.{0, 0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))
    (hy : y ∈ (galUnits.{0, 0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).ρ.invariants) :
    ∃ a, (unitsToInvariants.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) a).1 = y :=
  (unitsToInvariants_surjective _ _ ⟨y, hy⟩).imp fun _ ha => congrArg Subtype.val ha

theorem localUnitsAlgHom_eq_unitsToInvariants (v : S)
    (a : Additive ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) :
    localUnitsAlgHom S v a = (unitsToInvariants.{0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) a).1 :=
  congrArg Additive.ofMul (Units.ext rfl)

theorem exists_localUnitsAlgHom_eq (v : S) (m y : galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (h : ∀ σ, (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).ρ σ m - m =
      (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).ρ σ y - y) :
    ∃ a : Additive ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ, localUnitsAlgHom S v a = y - m := by
  have hinv : y - m ∈ (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))).ρ.invariants :=
    (Representation.mem_invariants _ _).2 fun σ => ρ_sub_eq_of_sub_eq (galUnits.{0, 0}
      ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) σ (h σ)
  exact (exists_unitsToInvariants_eq_local (K := K) (v : HeightOneSpectrum (𝓞 K.1)) (y - m) hinv).imp
    fun a ha => (localUnitsAlgHom_eq_unitsToInvariants S v a).trans ha

theorem exists_units_coboundary (x : (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).X 1)
    (hx : ((cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).d 1 2).hom x = 0) :
    ∃ T : galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S), ∀ σ,
      (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom (cochainOf _ x ![σ]) =
        (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ T - T :=
  exists_coboundary_of_subsingleton (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S))
    (subsingleton_cohomology_one_galUnits (K := K.1) (L := maxUnramifiedOutside K.1 ℚ̄ S)) x hx

theorem exists_gsUnitsDatum (x : (cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).X 1)
    (y : ∀ v : S, galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (hx : ((cochainsComplex (galSUnitsMax K.1 ℚ̄ S)).d 1 2).hom x = 0)
    (hy : ∀ (v : S) (σ : Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) /
      (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)),
      (gsUnitsLocalMor.{0} S ιs v).hom ((sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)).hom
        (cochainOf _ x ![(gsFinFamily S ιs v).toMonoidHom σ])) = (galUnits.{0, 0} _ _).ρ σ (y v) - y v) :
    ∃ d : GsUnitsDatum S, (sInvCochainHom S).comp (AddMonoidHom.fst _ _) d = x ∧ dataLocalHom S ιs d = y := by
  refine (exists_units_coboundary S x hx).elim fun T hT => ?_
  let t : sInvariantSubgroup (F := K.1) ℚ̄ S := Subtype.mk (Additive.toMul T) (toMul_mem_sInvariantSubgroup S T x hT)
  have ha : ∀ v : S, ∃ a, localUnitsAlgHom S v a = y v - sInvLocalHom S ιs v (Additive.ofMul t) := fun v =>
    exists_localUnitsAlgHom_eq S v _ (y v) fun σ => (hom_res_sub _ (gsUnitsLocalMor.{0} S ιs v) σ T).symm.trans
      ((congrArg (gsUnitsLocalMor.{0} S ιs v).hom (hT _)).symm.trans (hy v σ))
  exact ⟨(Additive.ofMul t, fun v => Classical.choose (ha v)), sInvCochain_eq_of S t x hT,
    funext fun v => (congrArg (· + sInvLocalHom S ιs v (Additive.ofMul t)) (Classical.choose_spec (ha v))).trans
      (sub_add_cancel _ _)⟩

theorem gsUnitsData_surjective : Function.Surjective (gsUnitsData S ιs) :=
  dataHom_surjective _ _ _ _ _ _ _ _ fun x y hx hy => exists_gsUnitsDatum S ιs x y hx hy

def sInvOfUnit (x : (K.1)ˣ) : sInvariantSubgroup (F := K.1) ℚ̄ S :=
  ⟨_, map_algebraMap_mem_sInvariantSubgroup (Ω := ℚ̄) S x⟩

theorem galUnits_ρ_sInvOfUnit (x : (K.1)ˣ) (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ
        (Additive.ofMul ((sInvOfUnit S x : sInvariantSubgroup (F := K.1) ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) =
      Additive.ofMul ((sInvOfUnit S x : sInvariantSubgroup (F := K.1) ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :=
  congrArg Additive.ofMul (Units.ext (σ.commutes _))

theorem gsUnitsLocalMor_sInvOfUnit (x : (K.1)ˣ) (v : S) :
    (gsUnitsLocalMor.{0} S ιs v).hom
        (Additive.ofMul ((sInvOfUnit S x : sInvariantSubgroup (F := K.1) ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) =
      localUnitsAlgHom S v (Additive.ofMul (finiteProj (v : HeightOneSpectrum (𝓞 K.1)) (diagonal K.1 x))) :=
  congrArg Additive.ofMul (Units.ext (((ιs v).commutes (x : K.1)).trans
    (IsScalarTower.algebraMap_apply K.1 ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (x : K.1))))

theorem hom_sub_comm {F : Type} [Monoid F] {A B : Rep.{0} (ULift.{0} ℤ) F} (f : A ⟶ B) (g : F) (a : A) :
    f.hom (A.ρ g a - a) = B.ρ g (f.hom a) - f.hom a := by
  rw [map_sub]
  congr 1
  exact Rep.hom_comm_apply f g a

section IdeleClass

variable [Finite S]

def gsUnitsPresentationData :
    GsUnitsDatum S →+ Additive ((∀ w : S, ((w : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) ×
      Multiplicative (sDivisor S)) :=
  AddMonoidHom.mk' (fun d => Additive.ofMul (fun w => Additive.toMul (d.2 w),
      Multiplicative.ofAdd (-divAbove S d.1))) fun d d' =>
    congrArg Additive.ofMul (Prod.ext rfl (congrArg Multiplicative.ofAdd
      ((congrArg Neg.neg (map_add (divAbove S) d.1 d'.1)).trans (neg_add _ _))))

def gsUnitsClass : GsUnitsDatum S →+ Additive (SIdeleClassGroup S) :=
  (MonoidHom.toAdditive (sPresentation S)).comp (gsUnitsPresentationData S)

theorem gsUnitsClass_apply (d : GsUnitsDatum S) :
    gsUnitsClass S d = Additive.ofMul (sPresentation S (fun w => Additive.toMul (d.2 w),
      Multiplicative.ofAdd (-divAbove S d.1))) :=
  rfl

omit [Finite S] in

theorem mul_sInvOfUnit_mem_sUnitsMax (t : Additive (sInvariantSubgroup (F := K.1) ℚ̄ S)) (x : (K.1)ˣ)
    (h : divS S (Additive.ofMul x) = -divAbove S t) :
    ((Additive.toMul (t + Additive.ofMul (sInvOfUnit S x)) : sInvariantSubgroup (F := K.1) ℚ̄ S) :
      (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ∈ sUnitsMax K.1 ℚ̄ S :=
  mem_sUnitsMax_of_divAbove_eq_zero S (((map_add (divAbove S) _ _).trans
    (congrArg (divAbove S t + ·) ((divAbove_algebraMap S x).trans h))).trans (add_neg_cancel _))

theorem gsUnitsData_eq_zero_of_gsUnitsClass_eq_zero (d : GsUnitsDatum S) (h : gsUnitsClass S d = 0) :
    gsUnitsData S ιs d = 0 := by
  have h2 : ((fun w => Additive.toMul (d.2 w), Multiplicative.ofAdd (-divAbove S d.1)) :
      (∀ w : S, ((w : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) × Multiplicative (sDivisor S)) ∈
      (principalPresentation S).range := by
    rw [← ker_sPresentation]
    exact congrArg Additive.toMul h
  refine h2.elim fun x hx => ?_
  have hx1 : ∀ w : S, finiteProj (w : HeightOneSpectrum (𝓞 K.1)) (diagonal K.1 x) = Additive.toMul (d.2 w) :=
    fun w => congrFun (congrArg Prod.fst hx) w
  have hx2 : divS S (Additive.ofMul x) = -divAbove S d.1 := congrArg Multiplicative.toAdd (congrArg Prod.snd hx)
  have hu := mul_sInvOfUnit_mem_sUnitsMax S d.1 x hx2
  refine dataHom_eq_zero_of_boundary _ _ _ _ _ _ _ _ d (Additive.ofMul ⟨_, hu⟩) (fun σ => ?_) (fun v => ?_)
  · refine sUnitsToUnits_injective S (maxUnramifiedOutside K.1 ℚ̄ S) ((sUnitsToUnits_sInvRatio S _ σ).trans ?_)
    refine Eq.trans ?_ (hom_sub_comm _ σ _).symm
    exact (ρ_add_sub_of_invariant _ σ (galUnits_ρ_sInvOfUnit S x σ)).symm.trans
      (congrArg (fun z => (galUnits.{0, 0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S)).ρ σ z - z) (add_comm _ _))
  · refine Eq.trans ?_ (map_add (gsUnitsLocalMor.{0} S ιs v).hom _ _).symm
    exact (congrArg (· + _) ((congrArg (localUnitsAlgHom S v) (congrArg Additive.ofMul (hx1 v))).symm.trans
      (gsUnitsLocalMor_sInvOfUnit S ιs x v).symm)).trans (add_comm _ _)

theorem exists_coprime_gsUnitsClass_eq (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (x : Additive (SIdeleClassGroup S)) :
    ∃ m : ℕ, m.Coprime ℓ ∧ ∃ d : GsUnitsDatum S, gsUnitsClass S d = m • x := by
  refine (sPresentation_surjective S (Additive.toMul x)).elim fun p hp => ?_
  have ho : addOrderOf (sPicMk S (Multiplicative.toAdd p.2)) ≠ 0 :=
    (isOfFinAddOrder_of_finite _).addOrderOf_pos.ne'
  refine (Nat.exists_eq_pow_mul_and_not_dvd ho ℓ hℓ.ne_one).elim fun j hj => hj.elim fun m hm => ?_
  have hc : sPicMk S (ℓ ^ j • (m • Multiplicative.toAdd p.2)) = 0 := by
    rw [map_nsmul, map_nsmul, smul_smul, ← hm.2]
    exact addOrderOf_nsmul_eq_zero _
  refine ((sPicMk_eq_zero_iff S _).1 hc).elim fun a ha => ?_
  have hNS : ∀ v ∉ S, (((ℓ ^ j : ℕ) : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv hmem => hv (hS v (by
    rw [Nat.cast_pow] at hmem
    exact v.isPrime.mem_of_pow_mem j hmem))
  refine (exists_divAbove_eq (Ω := ℚ̄) S (pow_ne_zero j hℓ.ne_zero) hNS _ a ha).elim fun y hy => ?_
  refine ⟨m, (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hm.1),
    (-Additive.ofMul y, fun w => m • Additive.ofMul (p.1 w)), ?_⟩
  rw [gsUnitsClass_apply]
  have hpair : ((fun w => Additive.toMul (m • Additive.ofMul (p.1 w))),
      Multiplicative.ofAdd (-divAbove S (-Additive.ofMul y))) = p ^ m := by
    refine Prod.ext (funext fun w => ?_) ?_
    · exact toMul_nsmul _ _
    · change Multiplicative.ofAdd (-divAbove S (-Additive.ofMul y)) = p.2 ^ m
      have e : -divAbove S (-Additive.ofMul y) = m • Multiplicative.toAdd p.2 := by
        rw [map_neg (divAbove S), neg_neg, hy]
      rw [e, ofAdd_nsmul]
      rfl
  rw [hpair, map_pow, ofMul_pow, hp]
  rfl

end IdeleClass

end Concrete

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]

theorem pow_notMem_asIdeal_of_forall (ℓ k : ℕ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    ∀ v ∉ S, (((ℓ ^ k : ℕ) : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv h => by
  rw [Nat.cast_pow] at h
  exact hv (hS v (v.isPrime.mem_of_pow_mem k h))

variable (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

include hnS in

theorem nsmul_gsRootsCompact (m : ℕ) (w : gsRootsCompact S ιs n m) : n • w = 0 := by
  obtain ⟨w', rfl⟩ := (bijective_gsRootsComparison S ιs n hnS m).2 w
  rw [← map_nsmul, nsmul_compactCohomologyRes_eq_zero (gsFinFamily S ιs) (nsmul_gsRoots S n) m w', map_zero]

abbrev gsRootsToUnitsCompact (m : ℕ) : gsRootsCompact S ιs n m ⟶ gsUnitsCompact S ιs m :=
  compactCohomologyMap (gsFinFamily S ιs) (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f
    (fun v => (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f)
    (fun v => (gsKummerLocalMap S ιs n v).comm₁₂) m

theorem surjective_gsKummerCompactδ (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hodd : Odd ℓ ∨ IsTotallyComplex K.1) :
    Function.Surjective (gsKummerCompactδ S ιs n hnS 1).hom := by
  intro w
  have h0 : (gsRootsToUnitsCompact S ιs n (1 + 1)).hom w = 0 := by
    refine eq_zero_of_gsUnitsCompact_two S ιs ℓ hℓ hS hodd _ k ?_
    rw [← hnk, ← map_nsmul, nsmul_gsRootsCompact S ιs n hnS, map_zero]
  exact (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact₁ (gsFinFamily S ιs) (gsKummerLocalMap S ιs n) (gsKummer_shortExact S n hnS)
      (localKummer_shortExact S n) 1) h0

theorem gsKummerCompactδ_eq_zero_iff (h : gsUnitsCompact S ιs 1) :
    (gsKummerCompactδ S ιs n hnS 1).hom h = 0 ↔ ∃ h', h = n • h' := by
  constructor
  · intro hh
    obtain ⟨h', hh'⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
      (compactCohomology_exact₃ (gsFinFamily S ιs) (gsKummerLocalMap S ιs n) (gsKummer_shortExact S n hnS)
        (localKummer_shortExact S n) 1) hh
    refine ⟨h', hh'.symm.trans ?_⟩
    exact DFunLike.congr_fun (congrArg (fun F => F.hom) (compactCohomologyMap_nsmul_id (gsFinFamily S ιs)
      (a := gsSUnitsLocalMor S ιs) n (fun v => (gsKummerLocalMap S ιs n v).comm₂₃) 1)) h'
  · rintro ⟨h', rfl⟩
    rw [map_nsmul, nsmul_gsRootsCompact S ιs n hnS]

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh GroundTheory.Global.IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

omit [NeZero n] in
theorem linearMap_apply_add_apply {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N →ₗ[R] P) (a b : M) (c : N) :
    f (a + b) c = f a c + f b c := by
  rw [map_add, LinearMap.add_apply]

set_option maxHeartbeats 1600000 in

theorem gsRootsToUnitsCompact_comparison_cup (h : gsUnitsCompact S ιs 1)
    (x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
      (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
        (show 2 + 1 = 3 from rfl) ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom h))
        x)) =
      compactCup (gsFinFamily S ιs) (gsPairingμ S n) (gsPairingμᵥ S ιs n) (gsPairingμ_hμ S ιs n)
        (show 1 + 1 + 1 = 2 + 1 from rfl) ((gsKummerCompactδ S ιs n hnS 1).hom h) x := by
  have ea := gsRootsComparison_compactCupRes S ιs n
    ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom h)) x
  have ea' : (gsRootsComparison S ιs n 2).hom ((gsRootsComparisonIso S ιs n hnS 2).inv.hom
      ((gsKummerCompactδ S ιs n hnS 1).hom h)) = (gsKummerCompactδ S ιs n hnS 1).hom h :=
    hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).inv_hom_id _
  have eb := compactCohomologyMap_compactCup (gsFinFamily S ιs) (A := gsRoots S n)
    (B := zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (C := gsRoots S n) (C' := galSUnitsMax K.1 ℚ̄ S)
    (Aᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (Cᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (C'ᵥ := fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (a := gsRootsOmegaMor S ιs n) (c := gsRootsOmegaMor S ιs n) (c' := gsSUnitsLocalMor S ιs)
    (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f
    (fun v => (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f)
    (fun v => (gsKummerLocalMap S ιs n v).comm₁₂) (gsPairingμ_hμ S ιs n) (show 1 + 1 + 1 = 2 + 1 from rfl)
    ((gsKummerCompactδ S ιs n hnS 1).hom h) x
  exact (congrArg (gsRootsToUnitsCompact S ιs n 3).hom (ea.trans (congrArg (fun w =>
    compactCup (gsFinFamily S ιs) (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
      (show 2 + 1 = 3 from rfl) w x) ea'))).trans eb

set_option maxHeartbeats 1600000 in

theorem gsRootsToUnitsCompact_cup_eq (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    ∃ W : cocycles (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2,
      (∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) *
        (((Additive.toMul d.1 : sInvariantSubgroup (F := K.1) ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^
          bockInt (zmodCocycleHom z) g h)⁻¹ ∈ sUnitsMax K.1 ℚ̄ S) ∧
      (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
        (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
          (show 2 + 1 = 3 from rfl)
          ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom (gsUnitsData S ιs d)))
          (cohomologyπ _ 1 z))) =
        (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
          (fun v => (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
              (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 W) +
            cupPairing (mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (show 0 + 2 = 2 from rfl)
              ((H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
              ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom
                ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom
                  (cohomologyπ _ 1 z)))) := by
  have ex := exists_gsUnitsData_cup_bock S ιs n ℓ k hℓ hnk hS (Additive.toMul d.1) z
  refine ⟨ex.choose, ex.choose_spec.1, ?_⟩
  have hd : gsUnitsData S ιs d = gsUnitsData S ιs (Additive.ofMul (Additive.toMul d.1), 0) +
      gsUnitsData S ιs (0, d.2) :=
    (congrArg (gsUnitsData S ιs) (Prod.ext (add_zero _).symm (zero_add _).symm)).trans (map_add _ _ _)
  have eloc := compactCup_localToCompact (gsFinFamily S ιs) (gsPairingU S)
    (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
    (show 0 + 2 = 2 from rfl) (show 0 + 1 + 2 = 2 + 1 from rfl)
    (fun v => (H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
    ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z))
  refine (gsRootsToUnitsCompact_comparison_cup S ιs n hnS (gsUnitsData S ιs d) (cohomologyπ _ 1 z)).trans
    ((gsKummerCompactδ_cup S ιs n hnS (gsUnitsData S ιs d) (cohomologyπ _ 1 z)).trans ?_)
  refine (congrArg (fun w => compactCup (gsFinFamily S ιs) (gsPairingU S)
      (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
      (show 1 + (1 + 1) = 2 + 1 from rfl) w
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))
    hd).trans ((linearMap_apply_add_apply _ _ _ _).trans ?_)
  refine (congrArg₂ (· + ·) ex.choose_spec.2 ((congrArg (fun w => compactCup (gsFinFamily S ιs) (gsPairingU S)
      (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
      (show 1 + (1 + 1) = 2 + 1 from rfl) w
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))
    (gsUnitsData_zero_local S ιs d.2)).trans eloc)).trans ?_
  exact (map_add _ _ _).symm

section Idele

variable [Fintype S] (hodd : Odd n ∨ IsTotallyComplex K.1)

omit [NeZero n] in
theorem prod_ofFinite_eq {M : Type*} [CommMonoid M] (f : S → M) :
    (letI := Fintype.ofFinite S; ∏ w : S, f w) = ∏ w : S, f w := by
  congr
  exact Subsingleton.elim _ _

omit [NeZero n] in

theorem sPresentation_fst (a : ∀ w : S, ((w : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) :
    sPresentation S (a, 1) = ∏ w : S, SIdeleClassGroup.mk S (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (a w)) := by
  rw [sPresentation_apply, toAdd_one, map_zero, toMul_zero, mul_one, placesIdele_apply, map_prod]
  exact prod_ofFinite_eq S _

set_option maxHeartbeats 1600000 in

theorem zmodToQZ_charEquiv_gsUnitsClass
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) (d : GsUnitsDatum S) :
    zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ (Additive.toMul (gsUnitsClass S d)))) =
      ∑ v : S, zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
        (SIdeleClassGroup.mk S (finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 v)))))) -
      divChar S hodd χ (divAbove S d.1) := by
  have e1 : Additive.toMul (gsUnitsClass S d) =
      sPresentation S (fun w => Additive.toMul (d.2 w), 1) *
        sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1)) :=
    (congrArg Additive.toMul (gsUnitsClass_apply S d)).trans
      ((congrArg (sPresentation S) (Prod.ext (mul_one _).symm (one_mul _).symm)).trans (map_mul _ _ _))
  set ψ := charEquiv ℚ̄ (Set.toFinite S) hodd χ with hψ
  have e2 : ψ (Additive.toMul (gsUnitsClass S d)) =
      (∏ w : S, ψ (SIdeleClassGroup.mk S (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w))))) *
        ψ (sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1))) :=
    (congrArg ψ e1).trans ((map_mul ψ _ _).trans (congrArg (· * _)
      ((congrArg ψ (sPresentation_fst S _)).trans (map_prod ψ _ _))))
  have e3 : zmodToQZ n (Multiplicative.toAdd (ψ (sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1))))) =
      -divChar S hodd χ (divAbove S d.1) :=
    (divChar_apply S hodd χ (-divAbove S d.1)).symm.trans (map_neg _ _)
  have e4 : zmodToQZ n (Multiplicative.toAdd (∏ w : S, ψ (SIdeleClassGroup.mk S
      (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w)))))) =
      ∑ w : S, zmodToQZ n (Multiplicative.toAdd (ψ (SIdeleClassGroup.mk S
        (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w)))))) :=
    (congrArg (zmodToQZ n) (toAdd_prod _ _)).trans (map_sum (zmodToQZ n) _ _)
  exact (congrArg (fun u => zmodToQZ n (Multiplicative.toAdd u)) e2).trans
    ((congrArg (zmodToQZ n) (toAdd_mul _ _)).trans ((map_add (zmodToQZ n) _ _).trans
      ((congrArg₂ (· + ·) e4 e3).trans (sub_eq_add_neg _ _).symm)))

end Idele

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh GroundTheory.Global.IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

omit [NeZero n] in
theorem nsmul_zmodToQZ (x : ZMod n) : n • zmodToQZ n x = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

def gsCupClass (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 :=
  compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl)
    ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom (gsUnitsData S ιs d)))
    (cohomologyπ _ 1 z)

def gsLocalUnitsImage (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) (v : S) :
    cohomology (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) 2 :=
  (cohomologyMap (gsRootsOmegaMor S ιs n v ≫ rootsOfUnityToUnits _ _ n) 2).hom (ξ v)

set_option maxHeartbeats 1600000 in

theorem zmodToQZ_gsCompactInv_localToCompact_eq_localInvU (hodd : Odd n ∨ IsTotallyComplex K.1)
    (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    zmodToQZ n (gsCompactInv S ιs n hodd h3
      ((localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom ξ)) =
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalUnitsImage S ιs n ξ v) :=
  (congrArg (zmodToQZ n) ((gsCompactInv_localToCompact S ιs n hodd h3 ξ).trans (gsSumInvRoots_apply S ιs n ξ))).trans
    ((map_sum (zmodToQZ n) _ _).trans
      (Finset.sum_congr rfl fun v _ => zmodToQZ_gsLocalInvRoots_eq_localInvU S ιs n v (ξ v)))

omit [Fintype S] in
set_option maxHeartbeats 1600000 in

theorem gsRootsToUnitsCompact_comparison_localToCompact
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
      ((localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom ξ)) =
      (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
        (gsLocalUnitsImage S ιs n ξ) := by
  have hg : ∀ v, 𝟙 (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v =
      (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (𝟙 (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v :=
    fun _ => Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  have e1 := hom_apply_hom_apply_eq_of_comp_eq (localToCompact_compactCohomologyMap (gsFinFamily S ιs)
    (A := gsRoots S n) (B := gsRoots S n) (Aᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
    (Bᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (a := fun _ => 𝟙 _) (b := gsRootsOmegaMor S ιs n)
    (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n) hg 2) ξ
  have e2 := hom_apply_hom_apply_eq_of_comp_eq (localToCompact_compactCohomologyMap (gsFinFamily S ιs)
    (A := gsRoots S n) (B := galSUnitsMax K.1 ℚ̄ S) (Aᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (Bᵥ := fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (a := gsRootsOmegaMor S ιs n) (b := gsSUnitsLocalMor S ιs)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f
    (fun v => (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f)
    (fun v => (gsKummerLocalMap S ιs n v).comm₁₂) 2) (fun v => (cohomologyMap (gsRootsOmegaMor S ιs n v) 2).hom (ξ v))
  refine (congrArg (gsRootsToUnitsCompact S ιs n 3).hom e1).trans (e2.trans ?_)
  refine congrArg (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (gsSUnitsLocalMor S ιs) 2).hom (funext fun v => ?_)
  exact (hom_apply_hom_apply_of_comp_eq (cohomologyMap_comp _ _ 2).symm (ξ v))

def gsLocalCup (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) (v : S) :
    cohomology (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) 2 :=
  cupPairing (mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (show 0 + 2 = 2 from rfl)
    ((H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
    ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))

omit [Fintype S] [NeZero n] in
theorem sub_sub_eq_neg_sub_add {M : Type*} [AddCommGroup M] (a b c : M) : b - (a - c) = -(a - (b + c)) := by
  abel

omit [Fintype S] [NeZero n] in
theorem sum_map_eq_sum_map_sub_add {ι : Type*} (s : Finset ι) {M : ι → Type*} [∀ v, AddCommGroup (M v)] {N : Type*}
    [AddCommGroup N] (F : ∀ v, M v →+ N) (a b : ∀ v, M v) :
    ∑ v ∈ s, F v (a v) = ∑ v ∈ s, F v (a v - b v) + ∑ v ∈ s, F v (b v) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by rw [map_sub, sub_add_cancel]

omit [Fintype S] [NeZero n] in
theorem nsmul_sum_map_sub {ι : Type*} (s : Finset ι) {M : ι → Type*} [∀ v, AddCommGroup (M v)] {N : Type*}
    [AddCommGroup N] (F : ∀ v, M v →+ N) (a b : ∀ v, M v) (ha : ∀ v, n • F v (a v) = 0)
    (hb : ∀ v, n • F v (b v) = 0) : n • ∑ v ∈ s, F v (a v - b v) = 0 := by
  rw [Finset.smul_sum]
  exact Finset.sum_eq_zero fun v _ => by rw [map_sub, smul_sub, ha, hb, sub_zero]

set_option maxHeartbeats 4000000 in

theorem zmodToQZ_gsCompactInv_gsCupClass (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (hχ : ∀ g, Multiplicative.toAdd (χ g) = zmodCocycleHom z g) :
    zmodToQZ n (gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS d z)) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ (Additive.toMul (gsUnitsClass S d)))) := by
  have hsurj := localToCompact_two_surjective S ιs n h3 (gsCupClass S ιs n hnS d z)
  have hT := (congrArg (fun w => zmodToQZ n (gsCompactInv S ιs n hodd h3 w)) hsurj.choose_spec).symm.trans
    (zmodToQZ_gsCompactInv_localToCompact_eq_localInvU S ιs n hodd h3 hsurj.choose)
  have L1 := gsRootsToUnitsCompact_cup_eq S ιs n hnS ℓ k hℓ hnk hS d z
  have hL2 := (congrArg (fun w => (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom w))
    hsurj.choose_spec).symm.trans (gsRootsToUnitsCompact_comparison_localToCompact S ιs n hsurj.choose)
  have h0 : (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
      (gsLocalUnitsImage S ιs n hsurj.choose - fun v =>
        (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
          (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 L1.choose) + gsLocalCup S ιs n d z v) = 0 := by
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (hL2.symm.trans L1.choose_spec.2))
  have hex := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact_local (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) _ (gsSUnitsLocalMor S ιs) 2) h0
  have hy : ∀ v : S, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
      (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 L1.choose) -
        (gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) =
      (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom (-hex.choose) := fun v =>
    (sub_sub_eq_neg_sub_add _ _ _).trans ((congrArg Neg.neg (congrFun hex.choose_spec v).symm).trans
      (map_neg ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom) hex.choose).symm)
  have hloc : ∀ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalCup S ιs n d z v) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
        (SIdeleClassGroup.mk S (finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 v)))))) :=
    fun v => localInvU_cupPairing_δ_bockSeq S ιs hodd v (Additive.toMul (d.2 v)) z χ hχ
  have hβ : n • ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1))
      (gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) = 0 :=
    nsmul_sum_map_sub n Finset.univ (fun v : S => localInvU (v : HeightOneSpectrum (𝓞 K.1)))
      (gsLocalUnitsImage S ιs n hsurj.choose) (gsLocalCup S ιs n d z)
      (fun v => (congrArg (n • ·) (zmodToQZ_gsLocalInvRoots_eq_localInvU S ιs n v (hsurj.choose v)).symm).trans
        (nsmul_zmodToQZ n _))
      (fun v => (congrArg (n • ·) (hloc v)).trans (nsmul_zmodToQZ n _))
  have hT1 := sum_localInvU_eq_neg_divChar S ιs hodd (Additive.toMul d.1) z χ hχ L1.choose L1.choose_spec.1
    (fun v => gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) (-hex.choose) hy hβ
  have hsum : ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalUnitsImage S ιs n hsurj.choose v) =
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1))
        (gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) +
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalCup S ιs n d z v) :=
    sum_map_eq_sum_map_sub_add Finset.univ (fun v : S => localInvU (v : HeightOneSpectrum (𝓞 K.1)))
      (gsLocalUnitsImage S ιs n hsurj.choose) (gsLocalCup S ιs n d z)
  exact hT.trans (hsum.trans ((congrArg₂ (· + ·) hT1 (Finset.sum_congr rfl fun v _ => hloc v)).trans
    ((neg_add_eq_sub _ _).trans (zmodToQZ_charEquiv_gsUnitsClass S n hodd χ d).symm)))

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]

omit [Fintype S] [NeZero n] in
theorem zmodCocycleHom_one (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    zmodCocycleHom z 1 = 0 := by
  have h := zmodCocycleHom_mul z 1 1
  rw [mul_one] at h
  exact (add_eq_left.1 h.symm)

omit [Fintype S] in

def gsCharOfCocycle (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)) where
  toFun g := Multiplicative.ofAdd (zmodCocycleHom z g)
  map_one' := by rw [zmodCocycleHom_one]; rfl
  map_mul' g h := by rw [zmodCocycleHom_mul]; rfl
  continuous_toFun := ((isLocallyConstant_zmodCocycleHom z).comp Multiplicative.ofAdd).continuous

omit [Fintype S] [NeZero n] in
theorem toAdd_gsCharOfCocycle (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (g : galUnramifiedOutside K.1 ℚ̄ S) : Multiplicative.toAdd (gsCharOfCocycle S n z g) = zmodCocycleHom z g :=
  rfl

omit [Fintype S] [NeZero n] in

theorem eq_zero_of_gsCharOfCocycle_eq_one (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (hz : gsCharOfCocycle S n z = 1) : z = 0 := by
  apply cocycles_ext
  funext v
  have hv : v = ![v 0] := by funext i; fin_cases i; rfl
  have e : zmodCocycleHom z (v 0) = 0 := congrArg Multiplicative.toAdd (DFunLike.congr_fun hz (v 0))
  rw [hv]
  apply ULift.ext
  exact e.trans (congrArg (fun w => (cochainOf (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) w ![v 0]).down)
    (map_zero (cocycleι (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1))).symm

omit [Fintype S] [NeZero n] in

theorem exists_gsCharOfCocycle_eq
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) :
    ∃ z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (gsCharOfCocycle S n z : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) = χ := by
  have hf : IsLocallyConstant fun g => (ULift.up (Multiplicative.toAdd (χ g)) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) :=
    ((IsLocallyConstant.iff_continuous (fun g : galUnramifiedOutside K.1 ℚ̄ S => χ g)).2 χ.continuous).comp
      fun x : Multiplicative (ZMod n) => (ULift.up (Multiplicative.toAdd x) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)
  have hmul : ∀ g h : galUnramifiedOutside K.1 ℚ̄ S,
      (ULift.up (Multiplicative.toAdd (χ (g * h))) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) =
        ULift.up (Multiplicative.toAdd (χ g)) + ULift.up (Multiplicative.toAdd (χ h)) := fun g h => by
    apply ULift.ext
    change Multiplicative.toAdd (χ (g * h)) = Multiplicative.toAdd (χ g) + Multiplicative.toAdd (χ h)
    rw [map_mul, toAdd_mul]
  refine ⟨cocyclesOneOfHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (fun _ _ => rfl) _ hf hmul, ?_⟩
  ext g
  apply Multiplicative.toAdd.injective
  rw [toAdd_gsCharOfCocycle]
  exact congrArg ULift.down (cochainOf_cocyclesOneOfHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)
    (fun _ _ => rfl) _ hf hmul ![g])

variable (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

omit [Fintype S] [NeZero n] in
include hnk hS in
theorem hnS_of_hS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv => by
  subst hnk
  exact pow_notMem_asIdeal_of_forall S ℓ k hS v hv

include hℓ hnk hS in

theorem gsCompactInv_gsCupClass (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (d : GsUnitsDatum S)
    (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS d z) =
      Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n z)
        (Additive.toMul (gsUnitsClass S d))) :=
  zmodToQZ_injective (n := n) (zmodToQZ_gsCompactInv_gsCupClass S ιs n hnS ℓ k hℓ hnk hS hodd h3 d z
    (gsCharOfCocycle S n z) (fun _ => rfl))

omit [Fintype S] [NeZero n] in

theorem eq_zero_of_coprime_nsmul_zmod (hnk : n = ℓ ^ k) {m : ℕ} (hm : m.Coprime ℓ) {u : ZMod n}
    (h : m • u = 0) : u = 0 := by
  have hmn : m.Coprime n := hnk ▸ hm.pow_right k
  rw [nsmul_eq_mul] at h
  exact (ZMod.unitOfCoprime m hmn).isUnit.mul_right_eq_zero.1 h

set_option maxHeartbeats 1600000 in
include hℓ hnk hS in

theorem gsCompactInv_ker_left (x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (hx : ∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) :
    x = 0 := by
  have hnS := hnS_of_hS S n ℓ k hnk hS
  have hz := cohomologyπ_surjective (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1 x
  by_contra hne
  have hχ : gsCharOfCocycle S n hz.choose ≠ 1 := fun h => hne (hz.choose_spec.symm.trans
    ((congrArg (cohomologyπ _ 1) (eq_zero_of_gsCharOfCocycle_eq_one S n _ h)).trans (map_zero _)))
  have hψ : charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) ≠ 1 :=
    fun h => hχ ((MulEquiv.map_eq_one_iff _).1 h)
  have ha : ∃ a, charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) a ≠ 1 :=
    not_forall.1 fun h => hψ (MonoidHom.ext h)
  have hm := exists_coprime_gsUnitsClass_eq S ℓ hℓ hS (Additive.ofMul ha.choose)
  have hd := hm.choose_spec.2
  have h1 : gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS hd.choose hz.choose) = 0 :=
    (congrArg (fun w => gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
      (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl)
      ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom
        (gsUnitsData S ιs hd.choose))) w)) hz.choose_spec).trans (hx _)
  have h2 := (gsCompactInv_gsCupClass S ιs n ℓ k hℓ hnk hS hodd h3 hnS hd.choose hz.choose).symm.trans h1
  have h4 : Additive.toMul (gsUnitsClass S hd.choose) = ha.choose ^ hm.choose :=
    (congrArg Additive.toMul hd.choose_spec).trans (toMul_nsmul _ _)
  have h5 : hm.choose • Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose)
      ha.choose) = 0 :=
    (toAdd_pow _ _).symm.trans ((congrArg Multiplicative.toAdd (map_pow _ _ _)).symm.trans
      ((congrArg (fun u => Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) u))
        h4).symm.trans h2))
  exact ha.choose_spec (Multiplicative.toAdd.injective
    (eq_zero_of_coprime_nsmul_zmod n ℓ k hnk hm.choose_spec.1 h5))

theorem exists_nsmul_eq_of_forall_zmod {A : Type*} [AddCommGroup A] (a : A)
    (h : ∀ f : A →+ ZMod n, f a = 0) : ∃ b, n • b = a := by
  by_contra hne
  set N := (nsmulAddMonoidHom (α := A) n).range
  have hq : (QuotientAddGroup.mk' N a) ≠ 0 := fun h0 =>
    hne ((QuotientAddGroup.eq_zero_iff a).1 h0 |>.elim fun b hb => ⟨b, hb⟩)
  have htors : ∀ q : A ⧸ N, n • q = 0 := fun q =>
    QuotientAddGroup.induction_on q fun x => by
      rw [← QuotientAddGroup.mk_nsmul]
      exact (QuotientAddGroup.eq_zero_iff _).2 ⟨x, rfl⟩
  obtain ⟨f, hf⟩ := zmod_exists_apply_ne_zero htors hq
  exact hf (h (f.comp (QuotientAddGroup.mk' N)))

set_option maxHeartbeats 4000000 in
include hℓ hnk hS in

theorem gsCompactInv_ker_right (y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2)
    (hy : ∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) :
    y = 0 := by
  have hnS := hnS_of_hS S n ℓ k hnk hS
  by_cases hk : k = 0
  · have hn1 : n = 1 := by rw [hnk, hk, pow_zero]
    have e := nsmul_compactCohomologyRes_eq_zero (gsFinFamily S ιs) (nsmul_gsRoots S n) 2 y
    subst hn1
    exact (one_smul _ _).symm.trans e
  have hoddℓ : Odd ℓ ∨ IsTotallyComplex K.1 :=
    hodd.imp (fun h => Nat.not_even_iff_odd.1 fun he => Nat.not_even_iff_odd.2 (hnk ▸ h) (Nat.even_pow.2 ⟨he, hk⟩)) id
  obtain ⟨h, hh⟩ := surjective_gsKummerCompactδ S ιs n hnS ℓ k hℓ hnk hS hoddℓ ((gsRootsComparison S ιs n 2).hom y)
  obtain ⟨d, hd⟩ := gsUnitsData_surjective S ιs h
  have hyeq : y = (gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom
      (gsUnitsData S ιs d)) :=
    (hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).hom_inv_id y).symm.trans
      (congrArg (gsRootsComparisonIso S ιs n hnS 2).inv.hom
        (hh.symm.trans (congrArg (gsKummerCompactδ S ιs n hnS 1).hom hd.symm)))

  have hall : ∀ f : Additive (SIdeleClassGroup S) →+ ZMod n, f (gsUnitsClass S d) = 0 := by
    intro f
    obtain ⟨z, hz⟩ := exists_gsCharOfCocycle_eq S n
      ((charEquiv ℚ̄ (Set.toFinite S) hodd).symm (AddMonoidHom.toMultiplicative f))
    have e1 := gsCompactInv_gsCupClass S ιs n ℓ k hℓ hnk hS hodd h3 hnS d z
    have e2 : gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS d z) = 0 :=
      (congrArg (fun w => gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) w
        (cohomologyπ _ 1 z))) hyeq).symm.trans (hy _)
    have e3 : charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n z) = AddMonoidHom.toMultiplicative f :=
      (congrArg (charEquiv ℚ̄ (Set.toFinite S) hodd) hz).trans (MulEquiv.apply_symm_apply _ _)
    exact (congrArg (fun ψ => Multiplicative.toAdd (ψ (Additive.toMul (gsUnitsClass S d)))) e3).symm.trans
      (e1.symm.trans e2)
  obtain ⟨b, hb⟩ := exists_nsmul_eq_of_forall_zmod n (A := Additive (SIdeleClassGroup S)) _ hall
  obtain ⟨m, hm, d', hd'⟩ := exists_coprime_gsUnitsClass_eq S ℓ hℓ hS b
  have hc0 : gsUnitsClass S (m • d - n • d') = 0 := by
    rw [map_sub, map_nsmul, map_nsmul, ← hb, hd']
    exact sub_eq_zero_of_eq ((smul_smul m n b).trans ((congrArg (· • b) (mul_comm m n)).trans (smul_smul n m b).symm))
  have hd0 := gsUnitsData_eq_zero_of_gsUnitsClass_eq_zero S ιs _ hc0
  rw [map_sub, map_nsmul, map_nsmul, sub_eq_zero, hd] at hd0
  have hw1 : m • (gsRootsComparison S ιs n 2).hom y = 0 := by
    rw [← hh, ← map_nsmul, hd0, map_nsmul, nsmul_gsRootsCompact S ιs n hnS]
  have hw2 : ℓ ^ k • (gsRootsComparison S ιs n 2).hom y = 0 := by
    rw [← hnk]
    exact nsmul_gsRootsCompact S ιs n hnS 2 _
  have hw := eq_zero_of_coprime_nsmul_eq_zero hm hw1 hw2
  exact (hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).hom_inv_id y).symm.trans
    ((congrArg (gsRootsComparisonIso S ιs n hnS 2).inv.hom hw).trans (map_zero _))

end

end GroundTheory.ProfCoh
end
