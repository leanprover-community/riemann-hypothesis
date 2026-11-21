import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialCharacterFiniteCommGroup
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
import BuildAid.ForwardExisting

section
section
open scoped TensorProduct
open TensorProduct Coalgebra WithConv

noncomputable section

namespace GlobalTheory
namespace TwistedGroupLike

variable {K H : Type} [Field K] [CommRing H] [Bialgebra K H]

def counitLeft : H ⊗[K] H →ₐ[K] H :=
  (Algebra.TensorProduct.lid K H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom K H) (AlgHom.id K H))

@[simp] theorem counitLeft_tmul (a b : H) : counitLeft (a ⊗ₜ[K] b) = counit (R := K) a • b := by
  simp [counitLeft]

theorem counitLeft_eq_lid (y : H ⊗[K] H) :
    counitLeft y = TensorProduct.lid K H (LinearMap.rTensor H (counit (R := K)) y) := by
  induction y with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | tmul a b => simp

theorem counitLeft_comul (x : H) : counitLeft (comul (R := K) x) = x := by
  rw [counitLeft_eq_lid, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

def IsCocycle (c : H ⊗[K] H) : Prop :=
  c ⊗ₜ[K] (1 : H) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) c =
    (Algebra.TensorProduct.assoc K K K H H H).symm
      ((1 : H) ⊗ₜ[K] c * Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) c)

theorem counitLeft_assoc_symm_tmul (a : H) (y : H ⊗[K] H) :
    Algebra.TensorProduct.map counitLeft (AlgHom.id K H)
      ((Algebra.TensorProduct.assoc K K K H H H).symm (a ⊗ₜ[K] y)) = counit (R := K) a • y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, smul_add, hy, hz]
  | tmul b d => simp [TensorProduct.smul_tmul']

theorem counitLeft_map_comul (y : H ⊗[K] H) :
    Algebra.TensorProduct.map counitLeft (AlgHom.id K H)
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) y) = y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a b => simp [counitLeft_comul]

theorem counitLeft_assoc_symm_map_comul (y : H ⊗[K] H) :
    Algebra.TensorProduct.map counitLeft (AlgHom.id K H)
      ((Algebra.TensorProduct.assoc K K K H H H).symm
        (Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) y)) =
      comul (R := K) (counitLeft y) := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, counitLeft_assoc_symm_tmul, counitLeft_tmul, map_smul]
    rfl

theorem counitLeft_eq_smul_one (c : H ⊗[K] H) (hu : IsUnit c) (hc : IsCocycle c) :
    counitLeft c = counit (R := K) (counitLeft c) • (1 : H) := by
  have h := congrArg (Algebra.TensorProduct.map counitLeft (AlgHom.id K H)) hc
  rw [map_mul, map_mul, map_mul, counitLeft_map_comul, counitLeft_assoc_symm_map_comul,
    counitLeft_assoc_symm_tmul, Bialgebra.counit_one, one_smul, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, mul_comm] at h
  have h5 : counitLeft c ⊗ₜ[K] (1 : H) = comul (R := K) (counitLeft c) := hu.mul_left_cancel h
  have h6 := congrArg counitLeft h5
  rw [counitLeft_tmul, counitLeft_comul] at h6
  exact h6.symm

def comulTw (c : H ⊗[K] H) : H →ₗ[K] H ⊗[K] H := LinearMap.mulLeft K c ∘ₗ comul

theorem comulTw_apply (c : H ⊗[K] H) (x : H) : comulTw c x = c * comul (R := K) x := rfl

theorem rTensor_comulTw (c y : H ⊗[K] H) :
    (comulTw c).rTensor H y =
      c ⊗ₜ[K] (1 : H) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, mul_add, hy, hz]
  | tmul a b => simp [comulTw_apply, Algebra.TensorProduct.tmul_mul_tmul]

theorem lTensor_comulTw (c y : H ⊗[K] H) :
    (comulTw c).lTensor H y =
      (1 : H) ⊗ₜ[K] c * Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, mul_add, hy, hz]
  | tmul a b => simp [comulTw_apply, Algebra.TensorProduct.tmul_mul_tmul]

theorem assoc_eq (z : (H ⊗[K] H) ⊗[K] H) :
    TensorProduct.assoc K H H H z = Algebra.TensorProduct.assoc K K K H H H z := rfl

theorem map_comul_id (y : H ⊗[K] H) :
    Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) y =
      (comul (R := K) (A := H)).rTensor H y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a b => simp

theorem map_id_comul (y : H ⊗[K] H) :
    Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) y =
      (comul (R := K) (A := H)).lTensor H y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a b => simp

theorem comulTw_coassoc (c : H ⊗[K] H) (hc : IsCocycle c) (x : H) :
    TensorProduct.assoc K H H H ((comulTw c).rTensor H (comulTw c x)) =
      (comulTw c).lTensor H (comulTw c x) := by
  rw [rTensor_comulTw, lTensor_comulTw, comulTw_apply, assoc_eq,
    map_mul (Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H)),
    map_mul (Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H)),
    ← mul_assoc, ← mul_assoc, hc, map_mul (Algebra.TensorProduct.assoc K K K H H H),
    AlgEquiv.apply_symm_apply]
  rw [map_comul_id (comul x), map_id_comul (comul x), ← assoc_eq, Coalgebra.coassoc_apply]

def kappa (c : H ⊗[K] H) : K := counit (R := K) (counitLeft c)

theorem kappa_ne_zero (c : H ⊗[K] H) (hu : IsUnit c) : kappa c ≠ 0 := by
  have := hu.map ((Bialgebra.counitAlgHom K H).comp counitLeft)
  exact this.ne_zero

theorem comm_eq (y : H ⊗[K] H) : TensorProduct.comm K H H y = Algebra.TensorProduct.comm K H H y :=
  rfl

theorem comm_comulTw [Coalgebra.IsCocomm K H] (c : H ⊗[K] H)
    (hs : Algebra.TensorProduct.comm K H H c = c) (x : H) :
    TensorProduct.comm K H H (comulTw c x) = comulTw c x := by
  rw [comulTw_apply, comm_eq, map_mul, hs, ← comm_eq, Coalgebra.comm_comul]

theorem lid_rTensor_smul_counit (c : H ⊗[K] H) (y : H ⊗[K] H) :
    TensorProduct.lid K H (((kappa c)⁻¹ • counit (R := K) (A := H)).rTensor H y) =
      (kappa c)⁻¹ • counitLeft y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul a b => simp [smul_smul]

theorem rid_lTensor_smul_counit (c : H ⊗[K] H) (y : H ⊗[K] H) :
    TensorProduct.rid K H (((kappa c)⁻¹ • counit (R := K) (A := H)).lTensor H y) =
      (kappa c)⁻¹ • counitLeft (TensorProduct.comm K H H y) := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul a b => simp [smul_smul]

theorem counitLeft_comulTw (c : H ⊗[K] H) (hu : IsUnit c) (hc : IsCocycle c) (x : H) :
    (kappa c)⁻¹ • counitLeft (comulTw c x) = x := by
  rw [comulTw_apply, map_mul, counitLeft_comul, counitLeft_eq_smul_one c hu hc, smul_mul_assoc,
    one_mul, ← kappa, smul_smul, inv_mul_cancel₀ (kappa_ne_zero c hu), one_smul]

theorem rTensor_counit_comulTw (c : H ⊗[K] H) (hu : IsUnit c) (hc : IsCocycle c) (x : H) :
    ((kappa c)⁻¹ • counit (R := K) (A := H)).rTensor H (comulTw c x) = 1 ⊗ₜ[K] x := by
  apply (TensorProduct.lid K H).injective
  rw [lid_rTensor_smul_counit, counitLeft_comulTw c hu hc, TensorProduct.lid_tmul, one_smul]

theorem lTensor_counit_comulTw [Coalgebra.IsCocomm K H] (c : H ⊗[K] H) (hu : IsUnit c)
    (hc : IsCocycle c) (hs : Algebra.TensorProduct.comm K H H c = c) (x : H) :
    ((kappa c)⁻¹ • counit (R := K) (A := H)).lTensor H (comulTw c x) = x ⊗ₜ[K] (1 : K) := by
  apply (TensorProduct.rid K H).injective
  rw [rid_lTensor_smul_counit, comm_comulTw c hs, counitLeft_comulTw c hu hc,
    TensorProduct.rid_tmul, one_smul]

variable (K H) in

def Twisted (_c : H ⊗[K] H) : Type := H

instance (c : H ⊗[K] H) : AddCommGroup (Twisted K H c) := inferInstanceAs (AddCommGroup H)
instance (c : H ⊗[K] H) : Module K (Twisted K H c) := inferInstanceAs (Module K H)
instance (c : H ⊗[K] H) [Module.Finite K H] : Module.Finite K (Twisted K H c) :=
  inferInstanceAs (Module.Finite K H)

def twistedCoalgebra [Coalgebra.IsCocomm K H] (c : H ⊗[K] H) (hu : IsUnit c) (hc : IsCocycle c)
    (hs : Algebra.TensorProduct.comm K H H c = c) : Coalgebra K (Twisted K H c) where
  comul := comulTw (K := K) (H := H) c
  counit := (kappa c)⁻¹ • counit (R := K) (A := H)
  coassoc := LinearMap.ext fun x => comulTw_coassoc c hc x
  rTensor_counit_comp_comul := LinearMap.ext fun x => rTensor_counit_comulTw c hu hc x
  lTensor_counit_comp_comul := LinearMap.ext fun x => lTensor_counit_comulTw c hu hc hs x

end TwistedGroupLike

open TwistedGroupLike in

theorem exists_twisted_groupLike : ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H]
    [Bialgebra K H] [Coalgebra.IsCocomm K H] [Module.Finite K H] (c : H ⊗[K] H), IsUnit c →
    c ⊗ₜ[K] (1 : H) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) c =
      (Algebra.TensorProduct.assoc K K K H H H).symm
        ((1 : H) ⊗ₜ[K] c * Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) c) →
    Algebra.TensorProduct.comm K H H c = c →
    ∃ u : H, u ≠ 0 ∧ c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u := by
  intro K H _ _ _ _ _ _ c hu hc hs
  letI := twistedCoalgebra c hu hc hs
  haveI : Coalgebra.IsCocomm K (Twisted K H c) :=
    ⟨LinearMap.ext fun x => (LinearMap.comp_apply _ _ _).trans (comm_comulTw c hs x)⟩
  let A := CartierDual K (Twisted K H c)
  have h1 : (1 : A).ofConv (show Twisted K H c from (1 : H)) = (kappa c)⁻¹ := by
    rw [LinearMap.convOne_apply]
    show (kappa c)⁻¹ • counit (R := K) (1 : H) = _
    simp
  haveI : Nontrivial A := ⟨⟨1, 0, fun h => by
    have := h1
    rw [h] at this
    exact (inv_ne_zero (kappa_ne_zero c hu)) this.symm⟩⟩
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field M
  let χ : A →ₐ[K] K := (IsAlgClosed.lift : (A ⧸ M) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)
  let u : Twisted K H c := (Module.evalEquiv K (Twisted K H c)).symm
    (χ.toLinearMap ∘ₗ (CartierDual.toDual K (Twisted K H c)).symm.toLinearMap)
  have hu' : ∀ φ : A, φ.ofConv u = χ φ := by
    intro φ
    have h := (Module.evalEquiv K (Twisted K H c)).apply_symm_apply
        (χ.toLinearMap ∘ₗ (CartierDual.toDual K (Twisted K H c)).symm.toLinearMap)
    exact LinearMap.congr_fun h φ.ofConv
  have hg : IsGroupLikeElem K u := (CartierDual.isGroupLikeElem_iff_mul u).2
    ⟨by rw [hu', map_one], fun φ ψ => by rw [hu', hu', hu', map_mul]⟩
  have h2 : comulTw c u = u ⊗ₜ[K] u := hg.comul_eq_tmul_self
  refine ⟨u, ?_, h2⟩
  intro h0
  have h3 : (counit (R := K) (A := Twisted K H c)) u = 0 := by
    rw [show u = (0 : Twisted K H c) from h0]
    exact map_zero _
  rw [hg.counit_eq_one] at h3
  exact one_ne_zero h3

end GlobalTheory
end
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_groupLike' : ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H] [Bialgebra K H] [Coalgebra.IsCocomm K H] [Module.Finite K H] (c : H ⊗[K] H), IsUnit c → c ⊗ₜ[K] (1 : H) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) c = (Algebra.TensorProduct.assoc K K K H H H).symm ((1 : H) ⊗ₜ[K] c * Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) c) → Algebra.TensorProduct.comm K H H c = c → ∃ u : H, u ≠ 0 ∧ c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u := by
  atlas_forward_decl GlobalTheory.exists_twisted_groupLike
end

section
section
open scoped TensorProduct

namespace GlobalTheory

open TensorProduct in

theorem isUnit_of_unit_mul_comul_eq_tmul_self (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H]
    (c : H ⊗[K] H) (hc : IsUnit c) (u : H) (hu : u ≠ 0)
    (h : c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u) : IsUnit u := by

  let φ : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lid K H).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom K H) (AlgHom.id K H))
  have hφΔ : φ (Coalgebra.comul (R := K) u) = u := by
    have e := congrArg (TensorProduct.lid K H) (Coalgebra.rTensor_counit_comul (R := K) u)
    rw [TensorProduct.lid_tmul, one_smul] at e
    exact e
  have hφuu : φ (u ⊗ₜ[K] u) = Coalgebra.counit (R := K) u • u := by
    simp [φ]
  have hε : Coalgebra.counit (R := K) u ≠ 0 := by
    intro h0
    have e := congrArg φ h
    rw [map_mul, hφΔ, hφuu, h0, zero_smul] at e
    exact hu ((hc.map φ).mul_right_eq_zero.mp e)

  let ψ : H ⊗[K] H →ₐ[K] H :=
    Algebra.TensorProduct.lift (AlgHom.id K H) (HopfAlgebra.antipodeAlgHom K H)
      (fun _ _ => Commute.all _ _)
  have hψΔ : ψ (Coalgebra.comul (R := K) u) = algebraMap K H (Coalgebra.counit (R := K) u) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul_apply (R := K) u]
    induction Coalgebra.comul (R := K) u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ψ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hψuu : ψ (u ⊗ₜ[K] u) = u * HopfAlgebra.antipode K u := by
    simp [ψ]
  have e := congrArg ψ h
  rw [map_mul, hψΔ, hψuu] at e
  have hU : IsUnit (u * HopfAlgebra.antipode K u) := by
    rw [← e]
    exact (hc.map ψ).mul ((isUnit_iff_ne_zero.mpr hε).map (algebraMap K H))
  exact isUnit_of_mul_isUnit_left hU

end GlobalTheory
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul : ∀ (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H] (c : H ⊗[K] H), IsUnit c → ∀ u : H, u ≠ 0 → c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u → IsUnit u := by
  atlas_forward_decl GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.CharKer
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.SymCob
open TensorProduct

def pt (K : Type) [CommRing K] {B A : Type} [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (φ : B →ₐ[K] A) :
    (Spec (CommRingCat.of A)).asOver (Sp K) ⟶ (Spec (CommRingCat.of B)).asOver (Sp K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact φ.comp_algebraMap)

theorem pt_sharp (K : Type) [CommRing K] {B A : Type} [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (φ : B →ₐ[K] A) (b : B) :
    (pt K φ).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (φ b) := by
  have hn := congr(($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom))).hom b)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  exact hn.symm

theorem specInv_injective (R : CommRingCat) : Function.Injective (Scheme.ΓSpecIso R).inv.hom := by
  intro x y h
  have := congrArg (Scheme.ΓSpecIso R).hom.hom h
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
    CommRingCat.id_apply] at this

theorem secMap_surj (K : Type) [CommRing K] (B D : Type) [CommRing B] [CommRing D] [Algebra K B] [Algebra K D] :
    ∃ Ψ : Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left, ⊤) →+*
      B ⊗[K] D, ∀ x, GlobalTheory.CharExists.secMap K B D (Ψ x) = x := by
  let e : ((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left ≅
      Spec (CommRingCat.of (B ⊗[K] D)) := pullbackSpecIso' K B D
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (B ⊗[K] D))).hom.hom.comp e.inv.appTop.hom, fun x => ?_⟩
  change e.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom ((Scheme.ΓSpecIso _).hom.hom (e.inv.appTop.hom x))) = x
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply]
  change (e.hom ≫ e.inv).appTop.hom x = x
  rw [e.hom_inv_id]; rfl

theorem key (K : Type) [CommRing K] (B A : Type) [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (Y : Over (Sp K)) (f h : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) (φ ψ : B →ₐ[K] A)
    (j : A →+* Γ(Y.left, ⊤))
    (hf : ∀ b, f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (φ b))
    (hh : ∀ b, h.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (ψ b))
    (z : B ⊗[K] B) :
    (lift f h).left.appTop.hom (GlobalTheory.CharExists.secMap K B B z) =
      j (Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b d => rw [GlobalTheory.CharExists.secMap_lift, hf, hh, Algebra.TensorProduct.lift_tmul, map_mul]

theorem mulpt (K : Type) [CommRing K] (B A : Type) [CommRing B] [HopfAlgebra K B] [CommRing A] [Algebra K A]
    (Y : Over (Sp K)) (f h : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) (φ ψ : B →ₐ[K] A)
    (j : A →+* Γ(Y.left, ⊤))
    (hf : ∀ b, f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (φ b))
    (hh : ∀ b, h.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (ψ b)) (b : B) :
    (f * h).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      j (((Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom K B)) b) := by
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := K) (Coalgebra.comul (R := K) b)
  rw [GlobalTheory.CharExists.mulsharp K B Y f h b S (fun i => i.1) (fun i => i.2) hS, hS, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.lift_tmul, map_mul, hf, hh]

theorem tensor_assoc_comul_placement_eq (K B : Type) [CommRing K] [CommRing B] [Bialgebra K B] :
    Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : B ⊗[K] B →ₐ[K] (B ⊗[K] B) ⊗[K] B).comp
        (Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B))
      (((Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.includeRight : B ⊗[K] B →ₐ[K] B ⊗[K] (B ⊗[K] B))).comp
        (Bialgebra.comulAlgHom K B)) (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B)) := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, Bialgebra.comulAlgHom_apply, AlgHom.coe_coe]
  have hab : a ⊗ₜ[K] Coalgebra.comul (R := K) b =
      (a ⊗ₜ[K] (1 : B ⊗[K] B)) * ((1 : B) ⊗ₜ[K] Coalgebra.comul (R := K) b) := by simp
  rw [hab, map_mul]
  simp [Algebra.TensorProduct.one_def]

theorem over_comp_appTop {S : Scheme.{0}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) (v : Γ(Z.left, ⊤)) :
    (f ≫ g).left.appTop.hom v = f.left.appTop.hom (g.left.appTop.hom v) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop]; rfl

set_option maxHeartbeats 1600000 in

theorem exists_coboundary : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → ∀ c : Γ((N ⊗ N).left, ⊤)ˣ, (∀ (T : Over (Sp K)) (x y z : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c = GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c) → (∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c = GlobalTheory.CharKer.pullTop (lift y x).left c) → ∃ u : Γ(N.left, ⊤)ˣ, ∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (x * y).left u = GlobalTheory.CharKer.pullTop x.left u * GlobalTheory.CharKer.pullTop y.left u := by
  intro K _ _ N _ _ hf c hcoc hsym
  obtain ⟨B, _, _, hcc, hfin, e, he⟩ := GlobalTheory.CharExists.pres K N hf
  obtain ⟨Ψ, hΨ⟩ := secMap_surj K B B
  obtain ⟨cG, hcG⟩ : ∃ cG : Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of B)).asOver (Sp K)).left, ⊤)ˣ,
      cG = pullTop (e.hom ⊗ₘ e.hom).left c := ⟨_, rfl⟩
  have hcB : GlobalTheory.CharExists.secMap K B B (Ψ cG) = cG := hΨ _
  have hcBu : IsUnit (Ψ cG) := cG.isUnit.map Ψ
  have hpull : ∀ (T : Over (Sp K)) (x y : T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)),
      pullTop (lift (x ≫ e.hom) (y ≫ e.hom)).left c = pullTop (lift x y).left cG := by
    intro T x y
    have : lift (x ≫ e.hom) (y ≫ e.hom) = lift x y ≫ (e.hom ⊗ₘ e.hom) := by
      rw [lift_map]
    rw [this, Over.comp_left, GlobalTheory.CharExists.pullTop_comp, hcG]
  have hmul : ∀ (T : Over (Sp K)) (x y : T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)),
      (x ≫ e.hom) * (y ≫ e.hom) = (x * y) ≫ e.hom := by
    intro T x y
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

  let iL : B →ₐ[K] B ⊗[K] B := Algebra.TensorProduct.includeLeft
  let iR : B →ₐ[K] B ⊗[K] B := Algebra.TensorProduct.includeRight
  have hsymB : Algebra.TensorProduct.comm K B B (Ψ cG) = Ψ cG := by
    have h := congrArg Units.val (hsym _ (pt K iL ≫ e.hom) (pt K iR ≫ e.hom))
    rw [hpull, hpull] at h
    simp only [pullTop, Units.coe_map, MonoidHom.coe_coe] at h
    rw [← hcB, key K B _ _ _ _ iL iR _ (pt_sharp K iL) (pt_sharp K iR),
      key K B _ _ _ _ iR iL _ (pt_sharp K iR) (pt_sharp K iL)] at h
    have h' := specInv_injective _ h
    have e1 : Algebra.TensorProduct.lift iL iR (fun _ _ => Commute.all _ _) = AlgHom.id K (B ⊗[K] B) :=
      Algebra.TensorProduct.ext' fun a b => by simp [iL, iR]
    have e2 : Algebra.TensorProduct.lift iR iL (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.comm K B B).toAlgHom :=
      Algebra.TensorProduct.ext' fun a b => by simp [iL, iR]
    rw [e1, e2] at h'
    exact h'.symm

  let ι₁ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeLeft.comp iL
  let ι₂ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeLeft.comp iR
  let ι₃ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeRight
  have hcocB : Ψ cG ⊗ₜ[K] (1 : B) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K B) (AlgHom.id K B) (Ψ cG) =
      (Algebra.TensorProduct.assoc K K K B B B).symm ((1 : B) ⊗ₜ[K] Ψ cG *
        Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B) (Ψ cG)) := by
    have h := congrArg Units.val (hcoc _ (pt K ι₁ ≫ e.hom) (pt K ι₂ ≫ e.hom) (pt K ι₃ ≫ e.hom))
    simp only [hmul, hpull] at h
    simp only [Units.val_mul, pullTop, Units.coe_map, MonoidHom.coe_coe] at h
    have k₁ := key K B _ _ (pt K ι₁) (pt K ι₂) ι₁ ι₂ _ (pt_sharp K ι₁) (pt_sharp K ι₂) (Ψ cG)
    have k₂ := key K B _ _ (pt K ι₁ * pt K ι₂) (pt K ι₃) _ ι₃ _
      (mulpt K B _ _ (pt K ι₁) (pt K ι₂) ι₁ ι₂ _ (pt_sharp K ι₁) (pt_sharp K ι₂)) (pt_sharp K ι₃) (Ψ cG)
    have k₃ := key K B _ _ (pt K ι₂) (pt K ι₃) ι₂ ι₃ _ (pt_sharp K ι₂) (pt_sharp K ι₃) (Ψ cG)
    have k₄ := key K B _ _ (pt K ι₁) (pt K ι₂ * pt K ι₃) ι₁ _ _ (pt_sharp K ι₁)
      (mulpt K B _ _ (pt K ι₂) (pt K ι₃) ι₂ ι₃ _ (pt_sharp K ι₂) (pt_sharp K ι₃)) (Ψ cG)
    rw [hcB] at k₁ k₂ k₃ k₄
    simp only [k₁, k₂, k₃, k₄] at h
    have h' := specInv_injective _ (((map_mul _ _ _).trans h).trans (map_mul _ _ _).symm)
    have E1 : Algebra.TensorProduct.lift ι₁ ι₂ (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.includeLeft : B ⊗[K] B →ₐ[K] (B ⊗[K] B) ⊗[K] B) :=
      Algebra.TensorProduct.ext' fun a b => by simp [ι₁, ι₂, iL, iR]
    have E3 : Algebra.TensorProduct.lift ι₂ ι₃ (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.includeRight : B ⊗[K] B →ₐ[K] B ⊗[K] (B ⊗[K] B)) :=
      Algebra.TensorProduct.ext' fun a b => by simp [ι₂, ι₃, iL, iR]
    have E2 : Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift ι₁ ι₂ (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) ι₃ (fun _ _ => Commute.all _ _) =
        Algebra.TensorProduct.map (Bialgebra.comulAlgHom K B) (AlgHom.id K B) := by
      rw [E1]
      exact Algebra.TensorProduct.ext' fun a b => by simp [ι₃]
    have E4 : Algebra.TensorProduct.lift ι₁ ((Algebra.TensorProduct.lift ι₂ ι₃ (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B)) := by
      rw [E3]
      exact tensor_assoc_comul_placement_eq K B
    rw [E2, E4, E1, E3] at h'
    simpa [map_mul] using h'
  obtain ⟨u₀, hu₀, hcu⟩ := (GlobalTheory.T.exists_twisted_groupLike') K B (Ψ cG) hcBu hcocB hsymB
  have hu := (GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul) K B (Ψ cG) hcBu u₀ hu₀ hcu
  obtain ⟨w, hw⟩ : ∃ w : Γ(((Spec (CommRingCat.of B)).asOver (Sp K)).left, ⊤)ˣ,
      w = Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom hu.unit := ⟨_, rfl⟩
  have hcu' : Ψ cG * Coalgebra.comul (R := K) (hu.unit : B) = (hu.unit : B) ⊗ₜ[K] (hu.unit : B) := by
    rw [IsUnit.unit_spec]; exact hcu
  refine ⟨pullTop e.inv.left w, fun T x y => ?_⟩
  have hc : pullTop (lift x y).left c = pullTop (lift (x ≫ e.inv) (y ≫ e.inv)).left cG := by
    have h := hpull T (x ≫ e.inv) (y ≫ e.inv)
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at h
    exact h
  have hxy : (x * y) ≫ e.inv = (x ≫ e.inv) * (y ≫ e.inv) := by
    have h := hmul T (x ≫ e.inv) (y ≫ e.inv)
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at h
    simp only [h, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hval : ∀ z : T ⟶ N, ((pullTop z.left (pullTop e.inv.left w) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) =
      (z ≫ e.inv).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (hu.unit : B)) := by
    intro z
    rw [hw]
    exact (over_comp_appTop z e.inv _).symm
  letI : Algebra K Γ(T.left, ⊤) :=
    (T.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let sh : (T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) → (B →ₐ[K] Γ(T.left, ⊤)) := fun f =>
    { toRingHom := f.left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
      commutes' := fun k => GlobalTheory.CharExists.algsharp K B T f k }
  have kc := key K B _ T (x ≫ e.inv) (y ≫ e.inv) (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (RingHom.id _)
    (fun _ => rfl) (fun _ => rfl) (Ψ cG)
  have km := mulpt K B _ T (x ≫ e.inv) (y ≫ e.inv) (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (RingHom.id _)
    (fun _ => rfl) (fun _ => rfl) (hu.unit : B)
  rw [hcB] at kc
  have fin : (Algebra.TensorProduct.lift (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (fun _ _ => Commute.all _ _)) (Ψ cG) *
      ((Algebra.TensorProduct.lift (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) (hu.unit : B) = sh (x ≫ e.inv) (hu.unit : B) * sh (y ≫ e.inv) (hu.unit : B) := by
    rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, ← map_mul, hcu', Algebra.TensorProduct.lift_tmul]
  simp only [hc]
  ext
  simp only [Units.val_mul, hval]
  simp only [hxy]
  simp only [pullTop, Units.coe_map, MonoidHom.coe_coe]
  simp only [kc, km, RingHom.id_apply]
  exact fin
end GlobalTheory.SymCob
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricTwoCocycle_finiteCommGroupScheme_coboundary : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → ∀ c : Γ((N ⊗ N).left, ⊤)ˣ, (∀ (T : Over (Sp K)) (x y z : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c = GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c) → (∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c = GlobalTheory.CharKer.pullTop (lift y x).left c) → ∃ u : Γ(N.left, ⊤)ˣ, ∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (x * y).left u = GlobalTheory.CharKer.pullTop x.left u * GlobalTheory.CharKer.pullTop y.left u := by
  atlas_forward_decl GlobalTheory.SymCob.exists_coboundary
end
