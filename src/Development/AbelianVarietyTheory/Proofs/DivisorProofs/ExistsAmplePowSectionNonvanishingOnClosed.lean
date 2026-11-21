import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLoci
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpen
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicPiIsOfFinOrder
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem ringChar_residueField_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    ringChar (X.residueField x) = ringChar (Y.residueField (f x)) := by
  haveI := (RingHom.charP_iff_charP (f.residueFieldMap x).hom (ringChar (Y.residueField (f x)))).1
    (ringChar.charP _)
  exact ringChar.eq _ _

theorem closeds_finite_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (T : Closeds X), (∀ ℓ : ℕ, ((T : Set X) ∩ fib X ℓ).Finite) →
    IsAffine (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧
      Module.Finite ℤ Γ((Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) := by
  intro k _ X _ p D hX T hT
  set I := Scheme.IdealSheafData.vanishingIdeal T with hI
  have hr : Set.range I.subschemeι = (T : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  set q := I.subschemeι ≫ p ≫ spMap (Int.castRingHom k) with hq
  have : IsProper q := by rw [hq]; infer_instance
  have : LocallyQuasiFinite q := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
    have hfin := hT (ringChar ((Sp ℤ).residueField y))
    refine Set.Finite.of_finite_image (f := I.subschemeι) (hfin.subset ?_)
      (I.subschemeι.isClosedEmbedding.injective.injOn)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hr.le ⟨z, rfl⟩, ?_⟩
    show ringChar _ = _
    rw [ringChar_residueField_eq (p ≫ spMap (Int.castRingHom k)) (I.subschemeι z)]
    have e : (p ≫ spMap (Int.castRingHom k)) (I.subschemeι z) = y := by
      rw [← hz, hq]; rfl
    rw [e]
  have : IsFinite q := IsFinite.of_isProper_of_locallyQuasiFinite q
  have hA : IsAffine I.subscheme := isAffine_of_isAffineHom q
  refine ⟨hA, ?_⟩
  have hf : (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).Finite :=
    q.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2)
  rw [RingHom.ext_int (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom)
    (algebraMap ℤ Γ(I.subscheme, ⊤)), RingHom.finite_algebraMap] at hf
  exact hf

end GlobalTheory.HSAmp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedSubset_finiteFibres_isAffine_finite_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (T : Closeds X), (∀ ℓ : ℕ, ((T : Set X) ∩ fib X ℓ).Finite) → IsAffine (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧ Module.Finite ℤ Γ((Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) := by
  atlas_forward_decl GlobalTheory.HSAmp.closeds_finite_int
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

noncomputable section
namespace GlobalTheory.SerreOnto
open CategoryTheory.Limits

variable {X T : Scheme.{0}} (i : T ⟶ X)

def unitToPush : GlobalTheory.LB.unitMod X ⟶ (Scheme.Modules.pushforward i).obj (GlobalTheory.LB.unitMod T) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

theorem toPushforward_comp (M : LB X) :
    GlobalTheory.LB.toPushforward M i ≫ ((Scheme.Modules.pushforward i).map (Twist.unitTwistIso (M.pull i)).inv ≫
      (Twist.projIso M i (GlobalTheory.LB.unitMod T)).hom) =
      (Twist.unitTwistIso M).inv ≫ Twist.map M (unitToPush i) := by
  apply Twist.hom_ext
  intro V s j
  change resG T (Twist.le_pull_inf i V j)
      ((i.appLE _ _ (GlobalTheory.LB.pull_inf_le i V (fun _ => j))).hom (GlobalTheory.LB.coord s j)) =
    (i.app _).hom (GlobalTheory.LB.coord s j)
  rw [GlobalTheory.LB.resG_appLE, ← Scheme.Hom.appLE_eq_app]

def kernelIso (M : LB X) (hM : M.IsLB) :
    kernel (GlobalTheory.LB.toPushforward M i) ≅ twist (kernel (unitToPush i)) M :=
  haveI := Twist.preservesFiniteLimits_twistFunctor hM
  kernel.mapIso _ _ (Twist.unitTwistIso M).symm
    ((Scheme.Modules.pushforward i).mapIso (Twist.unitTwistIso (M.pull i)).symm ≪≫
      Twist.projIso M i _) (toPushforward_comp i M) ≪≫
    (PreservesKernel.iso (twistFunctor M) (unitToPush i)).symm

end GlobalTheory.SerreOnto

open CategoryTheory.Limits in

theorem GlobalTheory.surjective_toPushforward_app_top_lbPow : ∀ (k : Type) [CommRing k] [IsNoetherianRing k]
    (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : LB X), IsAmpleLB L →
    ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i], ∀ᶠ N in atTop,
      Function.Surjective ((GlobalTheory.LB.toPushforward (lbPow L N) i).app ⊤) := by
  intro k _ _ X p hp L hL T i _
  letI : Algebra k Γ(X, ⊤) := (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have hf : ∀ r, algebraMap k Γ(X, ⊤) r = p.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom r) :=
    fun _ => rfl
  haveI := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : QCoh.IsFiniteQC (kernel (GlobalTheory.SerreOnto.unitToPush i)) :=
    QCoh.IsFiniteQC.of_mono (kernel.ι (GlobalTheory.SerreOnto.unitToPush i))
  filter_upwards [hL.eventually_subsingleton_coh_twist hf (kernel (GlobalTheory.SerreOnto.unitToPush i))]
    with N hN
  have hM : (lbPow L N).IsLB := isLB_lbPow hL.isLB N
  haveI := GlobalTheory.PinchLift.epi_toPushforward_of_closedImm i hM
  let φ := GlobalTheory.LB.toPushforward (lbPow L N) i
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (S.exact_of_f_is_kernel (kernelIsKernel φ)) inferInstance inferInstance
  refine cohOn.app_surjective hS ⊤ ?_
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ 1 (GlobalTheory.SerreOnto.kernelIso i _ hM)).toEquiv.subsingleton_congr.2
    (hN 1 one_pos)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_surjective_toPushforward_ampleLineBundle_pow : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i], ∀ᶠ N in atTop, Function.Surjective ((GlobalTheory.LB.toPushforward (lbPow L N) i).app ⊤) := by
  atlas_forward_decl GlobalTheory.surjective_toPushforward_app_top_lbPow
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward : ∀ (X T : Scheme.{0}) (i : T ⟶ X) (M : LB X), M.IsLB → Function.Surjective ((GlobalTheory.LB.toPushforward M i).app ⊤) → ∀ σ : (M.pull i).Sec, ∃ u : M.Sec, GlobalTheory.secPull u i = σ := by
  intro X T i M _ hs σ
  obtain ⟨u', hu'⟩ := hs ((LB.globalEquiv (M.pull i)).symm σ)
  refine ⟨LB.globalEquiv M u', ?_⟩
  apply LB.f_injective
  funext j
  have key := LB.globalEquiv_pullSec_f i (LB.globalEquiv M u') j
  rw [← LB.globalEquiv_symm_apply, LinearEquiv.symm_apply_apply, ← LB.toPushforward_app, hu',
    LinearEquiv.apply_symm_apply] at key
  rw [key]
  exact chartSec_f _ _ _
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sectionPullback_of_surjective_toPushforward : ∀ (X T : Scheme.{0}) (i : T ⟶ X) (M : LB X), M.IsLB → Function.Surjective ((GlobalTheory.LB.toPushforward M i).app ⊤) → ∀ σ : (M.pull i).Sec, ∃ u : M.Sec, GlobalTheory.secPull u i = σ := by
  atlas_forward_decl GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LiftAmple

def chartPullPullPow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull i) (lbPow (L.pull i) n) (𝟙 T) where
  idx J := J
  le J y hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    let K : PUnit → (L.pull i).ι := J
    let K' : PUnit → (L.pull i).ι := J'
    have h₁ : i y ∈ L.U (J PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ)
    have h₂ : i y ∈ L.U (J' PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ')
    have k₁ : (𝟙 T) y ∈ powChart (L.pull i) K := mem_powChart.2 (mem_pull.2 h₁)
    have k₂ : (𝟙 T) y ∈ powChart (L.pull i) K' := mem_powChart.2 (mem_pull.2 h₂)
    refine (gm_pull_g (lbPow L n) i (𝟙 T) y J J' hJ hJ').trans ?_
    refine (gm_lbPow_g n (𝟙 T ≫ i) y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.2 h₁)
      (mem_powChart.2 h₂)).trans ?_
    refine Eq.trans ?_ (gm_lbPow_g (L := L.pull i) n (𝟙 T) y K K' k₁ k₂).symm
    rw [gm_pull_g L i (𝟙 T) y (K PUnit.unit) (K' PUnit.unit) (mem_powChart.1 k₁) (mem_powChart.1 k₂)]

theorem exists_sec_pull_pow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) (σ : (lbPow (L.pull i) n).Sec) :
    ∃ σ' : ((lbPow L n).pull i).Sec, nonzeroLocus σ' = nonzeroLocus σ :=
  ⟨chartSec (chartPullPullPow L i n) σ, nonzeroLocus_chartSec_id _ σ fun _ J hJ =>
    ⟨J, mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hJ)))⟩⟩

end GlobalTheory.LiftAmple

namespace GlobalTheory.LiftAmple

theorem exists_sec_nonzero_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ →
    ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p D hX L hL T i _ n s hn hs
  haveI : Module.Finite ℤ k := hX.finite
  haveI : IsNoetherian ℤ k := inferInstance
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (GlobalTheory.T.eventually_surjective_toPushforward_ampleLineBundle_pow k X p hX.isProjOver L hL T i)
  have hN : N₀ ≤ n * (N₀ + 1) := by nlinarith
  obtain ⟨σ', hσ'⟩ := exists_sec_pull_pow L i (n * (N₀ + 1)) (secPow s (N₀ + 1))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionPullback_of_surjective_toPushforward X T i (lbPow L (n * (N₀ + 1))) (isLB_lbPow hL.isLB _) (hN₀ _ hN) σ'
  refine ⟨n * (N₀ + 1), u, by nlinarith, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ nonzeroLocus (GlobalTheory.secPull u i) := by
    rw [hu, hσ', nonzeroLocus_secPow s (Nat.le_add_left 1 N₀), hs]; trivial
  rw [nonzeroLocus_secPull] at hz
  exact hz

end GlobalTheory.LiftAmple
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_power_lift_of_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ) (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ → ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  atlas_forward_decl GlobalTheory.LiftAmple.exists_sec_nonzero_on_closed
end

section
section
namespace GlobalTheory

open CommRing

theorem natCast_mul_mem_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    (n : ℕ) (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range)
    (I : (Submodule B B')ˣ) (x : B') : (n : B') * x ∈ (I : Submodule B B') := by
  have h1 : (1 : B') ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B') := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Submodule.one_le.mp le_rfl
  have key : ∀ y ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B'),
      ((n : B') * x) * y ∈ (I : Submodule B B') := by
    intro y hy
    refine Submodule.mul_induction_on hy (fun j _ i hi => ?_) (fun y z hy hz => ?_)
    · obtain ⟨b, hb⟩ := hn (x * j)
      have : (n : B') * x * (j * i) = b • i := by
        rw [Algebra.smul_def, hb]; ring
      rw [this]; exact Submodule.smul_mem _ b hi
    · rw [mul_add]; exact Submodule.add_mem _ hy hz
  simpa using key 1 h1

theorem finite_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    [Module.Finite ℤ B'] (n : ℕ) (hn0 : n ≠ 0)
    (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range) :
    Finite (Submodule B B')ˣ := by
  set C : Submodule ℤ B' := (Ideal.span {(n : ℤ)}) • (⊤ : Submodule ℤ B') with hCdef
  haveI : NeZero n := ⟨hn0⟩
  haveI : Finite (ℤ ⧸ Ideal.span {(n : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod n).symm.toEquiv
  haveI : Finite (B' ⧸ C) := Submodule.finite_quotient_smul _ Module.Finite.fg_top
  haveI : Finite (Submodule ℤ (B' ⧸ C)) :=
    Finite.of_injective (fun N => (N : Set (B' ⧸ C))) SetLike.coe_injective
  have hC : ∀ I : (Submodule B B')ˣ, C ≤ (I : Submodule B B').restrictScalars ℤ := by
    intro I
    refine Submodule.smul_le.mpr fun r hr x _ => ?_
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have : (k * n : ℤ) • x = (n : B') * (k • x) := by
      rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring
    rw [Submodule.restrictScalars_mem, this]
    exact natCast_mul_mem_units_submodule n hn I _
  let f : (Submodule B B')ˣ → Submodule ℤ (B' ⧸ C) := fun I =>
    Submodule.map C.mkQ ((I : Submodule B B').restrictScalars ℤ)
  refine Finite.of_injective f fun I J h => ?_
  have hIJ : (I : Submodule B B').restrictScalars ℤ = (J : Submodule B B').restrictScalars ℤ := by
    have := congrArg (Submodule.comap C.mkQ) h
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.mpr (hC I), sup_eq_right.mpr (hC J)] at this
  exact Units.ext (Submodule.restrictScalars_injective ℤ _ _ hIJ)

theorem isOfFinOrder_of_isOfFinOrder_mapRingHom : ∀ (B B' : Type) [CommRing B] [CommRing B']
    [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 →
    (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B,
    IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by
  intro B B' _ _ _ φ n hφ hn0 hn M hM
  letI : Algebra B B' := φ.toAlgebra
  haveI : FaithfulSMul B B' := (faithfulSMul_iff_algebraMap_injective B B').mpr hφ
  haveI := finite_units_submodule (B := B) (B' := B') n hn0 (fun b' => hn b')
  obtain ⟨k, hk, hpow⟩ := hM.exists_pow_eq_one
  have e : CommRing.Pic.mapRingHom φ = CommRing.Pic.mapAlgebra B B' :=
    CommRing.Pic.mapRingHom_algebraMap
  have hmem : M ^ k ∈ CommRing.relPic B B' := by
    rw [CommRing.relPic, MonoidHom.mem_ker, map_pow, ← e]; exact hpow
  rw [← Submodule.range_unitsToPic] at hmem
  obtain ⟨I, hI⟩ := hmem
  have hfo : IsOfFinOrder (M ^ k) := by
    rw [← hI]; exact (Submodule.unitsToPic B B').isOfFinOrder (isOfFinOrder_of_finite I)
  obtain ⟨m, hm, hm1⟩ := hfo.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul]; exact hm1⟩

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 → (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B, IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by
  atlas_forward_decl GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom
end

section
section
set_option autoImplicit false
open NumberField

namespace GlobalTheory.PicDom

theorem exists_int_mem_span {B : Type} [CommRing B] [IsDomain B] [Algebra.IsIntegral ℤ B] {d : B} (hd : d ≠ 0) :
    ∃ a : ℤ, a ≠ 0 ∧ (a : B) ∈ Ideal.span {d} := by
  have h := Ideal.comap_ne_bot_of_integral_mem hd (Ideal.mem_span_singleton_self d)
    (Algebra.IsIntegral.isIntegral (R := ℤ) d)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨a, ha0, by simpa using ha⟩

theorem isOfFinOrder_of_not_charZero (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (hc : ¬ CharZero B) (M : CommRing.Pic B) : IsOfFinOrder M := by
  have hp : ringChar B ≠ 0 := by
    intro h
    apply hc
    have : CharP B 0 := h ▸ ringChar.charP B
    exact CharP.charP_to_charZero B
  have hfin : Finite B := Module.finite_of_fg_torsion B fun x =>
    ⟨⟨(ringChar B : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, by
      change ((ringChar B : ℤ)) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, ringChar.Nat.cast_ringChar, zero_mul]⟩
  exact isOfFinOrder_of_finite M

variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]

theorem finiteDimensional_of_isFractionRing (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [CharZero K] :
    FiniteDimensional ℚ K := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
  have key : ∀ y : B, algebraMap B K y ∈
      Submodule.span ℚ (algebraMap B K '' (s : Set B)) := fun y => by
    have hy : y ∈ Submodule.span ℤ (s : Set B) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_zsmul]; exact zsmul_mem hx a
  classical
  refine Module.finite_def.2 ⟨s.image (algebraMap B K), ?_⟩
  rw [Finset.coe_image, eq_top_iff]
  intro x _
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨a, ha0, ha⟩ := exists_int_mem_span hd0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
  have hdK : algebraMap B K d ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha0
  have : algebraMap B K b / algebraMap B K d =
      ((a : ℚ)⁻¹) • algebraMap B K (c * b) := by
    rw [Rat.smul_def, map_mul, Rat.cast_inv, Rat.cast_intCast]
    have h2 : (a : K) = algebraMap B K c * algebraMap B K d := by
      rw [← map_mul, hc, map_intCast]
    have hcK : algebraMap B K c ≠ 0 := by
      intro h; apply haK; rw [h2, h, zero_mul]
    rw [h2]
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ (key _)

end GlobalTheory.PicDom

namespace GlobalTheory.PicDom

variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]

theorem isOfFinOrder_of_numberField (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [NumberField K]
    (M : CommRing.Pic B) : IsOfFinOrder M := by
  let φ : B →+* 𝓞 K :=
    { toFun := fun b => ⟨algebraMap B K b, (Algebra.IsIntegral.isIntegral (R := ℤ) b).algebraMap⟩
      map_zero' := by ext; simp only [RingOfIntegers.map_mk, map_zero]
      map_one' := by ext; simp only [RingOfIntegers.map_mk, map_one]
      map_add' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_add]; rfl
      map_mul' := fun x y => by ext; simp only [RingOfIntegers.map_mk, map_mul]; rfl }
  have hφ : ∀ b, ((φ b : 𝓞 K) : K) = algebraMap B K b := fun b => rfl
  have hinj : Function.Injective φ := fun x y h => IsFractionRing.injective B K (by
    rw [← hφ, ← hφ, h])

  have hmul : ∀ ω : 𝓞 K, ∃ a : ℤ, a ≠ 0 ∧ (a : 𝓞 K) * ω ∈ φ.range := fun ω => by
    obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := B) (ω : K)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    obtain ⟨a, ha0, ha⟩ := exists_int_mem_span hd0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    have hdK : algebraMap B K d ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]
    refine ⟨a, ha0, c * b, ?_⟩
    apply RingOfIntegers.ext
    rw [hφ, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_intCast, ← RingOfIntegers.coe_eq_algebraMap, ← hbd]
    have h2 : (a : K) = algebraMap B K c * algebraMap B K d := by
      rw [← map_mul, hc, map_intCast]
    rw [h2, mul_assoc]
    congr 1
    exact (mul_div_cancel₀ _ hdK).symm
  classical
  choose a ha0 ha using hmul
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℤ) (M := 𝓞 K)
  set N : ℤ := ∏ ω ∈ t, a ω
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun ω _ => ha0 ω
  have hNmem : ∀ x : 𝓞 K, (N : 𝓞 K) * x ∈ φ.range := fun x => by
    have hx : x ∈ Submodule.span ℤ (t : Set (𝓞 K)) := ht ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem ω hω =>
      show ((∏ ω ∈ t, a ω : ℤ) : 𝓞 K) * ω ∈ φ.range
      rw [← Finset.mul_prod_erase t a (Finset.mem_coe.1 hω), Int.cast_mul, mul_comm (a ω : 𝓞 K), mul_assoc]
      exact mul_mem (intCast_mem _ _) (ha ω)
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact zsmul_mem hx k
  have hn0 : N.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hN0
  have hcond : ∀ x : 𝓞 K, ((N.natAbs : ℕ) : 𝓞 K) * x ∈ φ.range := fun x => by
    rcases Int.natAbs_eq N with h | h
    · have := hNmem x
      rwa [h, Int.cast_natCast] at this
    · have := neg_mem (hNmem x)
      rwa [h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this
  haveI : Finite (CommRing.Pic (𝓞 K)) := Finite.of_equiv _ (ClassGroup.equivPic (𝓞 K)).toEquiv
  exact GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B (𝓞 K) φ N.natAbs hinj hn0 hcond M (isOfFinOrder_of_finite _)

theorem isOfFinOrder_of_charZero (M : CommRing.Pic B) : IsOfFinOrder M := by
  haveI : CharZero (FractionRing B) := IsFractionRing.charZero_of_isFractionRing B
  haveI : FiniteDimensional ℚ (FractionRing B) := finiteDimensional_of_isFractionRing B (FractionRing B)
  haveI : NumberField (FractionRing B) := ⟨⟩
  exact isOfFinOrder_of_numberField B (FractionRing B) M

end GlobalTheory.PicDom

theorem GlobalTheory.pic_isOfFinOrder_of_finite_int : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (M : CommRing.Pic B), IsOfFinOrder M := by
  intro B _ _ _ M
  by_cases hc : CharZero B
  · exact GlobalTheory.PicDom.isOfFinOrder_of_charZero B M
  · exact GlobalTheory.PicDom.isOfFinOrder_of_not_charZero B hc M
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_isOfFinOrder_of_finite_int' : ∀ (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  atlas_forward_decl GlobalTheory.pic_isOfFinOrder_of_finite_int
end

section
section
namespace GlobalTheory.CokerMinimalPrimes

theorem exists_nat_mem_sup (B : Type) [CommRing B] [Module.Finite ℤ B]
    {P Q : Ideal B} (hP : P ∈ minimalPrimes B) (hQ : Q ∈ minimalPrimes B) (hPQ : P ≠ Q) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : B) ∈ P ⊔ Q := by
  have hQm : Minimal (fun q : Ideal B => q.IsPrime ∧ ⊥ ≤ q) Q := hQ
  have hPm : Minimal (fun q : Ideal B => q.IsPrime ∧ ⊥ ≤ q) P := hP
  have hnle : ¬ P ≤ Q := fun h => hPQ (hQm.eq_of_le hPm.1 h)
  haveI : Q.IsPrime := hQm.1.1
  obtain ⟨p, hpP, hpQ⟩ := Set.not_subset.mp hnle
  have hx : Ideal.Quotient.mk Q p ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hxI : Ideal.Quotient.mk Q p ∈ Ideal.map (Ideal.Quotient.mk Q) P :=
    Ideal.mem_map_of_mem _ hpP
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) hx hxI
    (Algebra.IsIntegral.isIntegral _)
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, eq_intCast, ← map_intCast (Ideal.Quotient.mk Q),
    Ideal.mem_quotient_iff_mem_sup] at hk
  refine ⟨k.natAbs, by simpa using hk0, ?_⟩
  rcases Int.natAbs_eq k with h | h
  · rw [h, Int.cast_natCast] at hk; exact hk
  · rw [h, Int.cast_neg, Int.cast_natCast] at hk; simpa using (P ⊔ Q).neg_mem hk

theorem exists_pow_mul_mem_range {B : Type} [CommRing B] {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : ι → Ideal B) (m : B) (hm : ∀ i j, i ≠ j → m ∈ I i ⊔ I j)
    (b' : (i : ι) → B ⧸ I i) :
    ∃ a : B, ∀ i, Ideal.Quotient.mk (I i) a
      = (Ideal.Quotient.mk (I i) m) ^ (Fintype.card ι - 1) * b' i := by

  have hq : ∀ i j, ∃ q : B, i ≠ j → q ∈ I j ∧ m - q ∈ I i := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hm i j hij)
    exact ⟨z, fun _ => ⟨hz, by rw [← hyz]; simpa using hy⟩⟩
  choose q hq using hq
  let e : ι → B := fun i => ∏ j ∈ Finset.univ.erase i, q i j
  have he_mem : ∀ i j, i ≠ j → e i ∈ I j := by
    intro i j hij
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (q i) (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    change ∏ j ∈ Finset.univ.erase i, q i j ∈ I j
    rw [hc]
    exact Ideal.mul_mem_right _ _ (hq i j hij).1
  have he_mod : ∀ i, Ideal.Quotient.mk (I i) (e i)
      = (Ideal.Quotient.mk (I i) m) ^ (Fintype.card ι - 1) := by
    intro i
    simp only [e, map_prod]
    rw [Finset.prod_congr rfl (g := fun _ => Ideal.Quotient.mk (I i) m), Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    exact (Ideal.Quotient.eq.mpr (hq i j hij).2).symm
  choose c hc using fun i => Ideal.Quotient.mk_surjective (I := I i) (b' i)
  refine ⟨∑ i, e i * c i, fun i => ?_⟩
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_mul, he_mod, hc]
  · intro j _ hji
    rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (he_mem j i hji), zero_mul]
  · intro h; exact (h (Finset.mem_univ i)).elim

theorem exists_nat_mul_mem_range_pi_quotient_minimalPrimes : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧
    ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)),
      (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈
        (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by
  intro B _ _
  classical
  haveI : IsNoetherian ℤ B := isNoetherian_of_isNoetherianRing_of_finite ℤ B
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  letI : Fintype (minimalPrimes B) := Fintype.ofFinite _
  have hpair : ∀ P Q : minimalPrimes B, ∃ m : ℕ, m ≠ 0 ∧ (P ≠ Q → (m : B) ∈ (P : Ideal B) ⊔ Q) := by
    intro P Q
    by_cases h : P = Q
    · exact ⟨1, one_ne_zero, fun h' => (h' h).elim⟩
    obtain ⟨m, hm0, hm⟩ := exists_nat_mem_sup B P.2 Q.2 (fun e => h (Subtype.ext e))
    exact ⟨m, hm0, fun _ => hm⟩
  choose f hf0 hf using hpair
  let m : ℕ := ∏ p : minimalPrimes B × minimalPrimes B, f p.1 p.2
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hf0 p.1 p.2
  have hm : ∀ P Q : minimalPrimes B, P ≠ Q → (m : B) ∈ (P : Ideal B) ⊔ Q := by
    intro P Q hPQ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : minimalPrimes B × minimalPrimes B => f p.1 p.2)
      (Finset.mem_univ (P, Q))
    change ((∏ p : minimalPrimes B × minimalPrimes B, f p.1 p.2 : ℕ) : B) ∈ _
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hf P Q hPQ)
  refine ⟨m ^ (Fintype.card (minimalPrimes B) - 1), pow_ne_zero _ hm0, fun b' => ?_⟩
  obtain ⟨a, ha⟩ := exists_pow_mul_mem_range (fun P : minimalPrimes B => (P : Ideal B)) (m : B) hm b'
  refine ⟨a, funext fun P => ?_⟩
  change Ideal.Quotient.mk (P : Ideal B) a = _
  rw [ha P, Pi.mul_apply, Pi.natCast_apply, map_natCast]
  push_cast
  rfl

end GlobalTheory.CokerMinimalPrimes
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧ ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)), (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈ (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by
  atlas_forward_decl GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_pi_isOfFinOrder' : ∀ (ι : Type) [Finite ι] (R : ι → Type) [∀ i, CommRing (R i)], (∀ i (M : CommRing.Pic (R i)), IsOfFinOrder M) → ∀ M : CommRing.Pic ((i : ι) → R i), IsOfFinOrder M := by
  first | exact @GlobalTheory.pic_pi_isOfFinOrder | exact GlobalTheory.pic_pi_isOfFinOrder | (intros; apply GlobalTheory.pic_pi_isOfFinOrder <;> assumption)
end

section
section
namespace GlobalTheory.PicReducedTors

theorem pic_isOfFinOrder : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B),
    IsOfFinOrder M := by
  intro B _ _ _ M
  haveI : IsNoetherian ℤ B := inferInstance
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let φ := Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)
  haveI : Module.Finite ℤ ((P : minimalPrimes B) → B ⧸ (P : Ideal B)) := inferInstance
  obtain ⟨n, hn, hmul⟩ := GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' B
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hrad : b ∈ (⊥ : Ideal B).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      have := congrFun hb ⟨P, hP⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact this
    obtain ⟨k, hk⟩ := hrad
    exact IsReduced.eq_zero b ⟨k, by simpa using hk⟩
  refine GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B _ φ n hinj hn hmul M ?_
  refine GlobalTheory.T.pic_pi_isOfFinOrder' _ _ (fun P N => ?_) _
  haveI : (P : Ideal B).IsPrime := P.2.1.1
  exact GlobalTheory.T.pic_isOfFinOrder_of_finite_int' _ N

end GlobalTheory.PicReducedTors
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_pic_of_isReduced_finite_int : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  atlas_forward_decl GlobalTheory.PicReducedTors.pic_isOfFinOrder
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

noncomputable section

namespace GlobalTheory.SecTensor

open TensorProduct

theorem isLocalizedModule_mulTensor {R M N B : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [CommRing B] [Algebra R B] (r : R) [IsLocalization.Away r B]
    (c : M →ₗ[R] B) (d : N →ₗ[R] B) [IsLocalizedModule.Away r c] [IsLocalizedModule.Away r d] :
    IsLocalizedModule.Away r (TensorProduct.lift ((LinearMap.mul R B).compl₁₂ c d)) := by
  have hc : IsBaseChange B c := (isLocalizedModule_iff_isBaseChange (.powers r) B c).1 inferInstance
  have hd : IsBaseChange B d := (isLocalizedModule_iff_isBaseChange (.powers r) B d).1 inferInstance
  show IsLocalizedModule (.powers r) _
  rw [isLocalizedModule_iff_isBaseChange (.powers r) B]
  have h1 := isBaseChange_tensorProduct_map (R := R) (P := N) B hc
  have h2 := h1.comp (IsBaseChange.ofEquiv hd.equiv)
  have heq : TensorProduct.lift ((LinearMap.mul R B).compl₁₂ c d) =
      (hd.equiv.toLinearMap.restrictScalars R) ∘ₗ
        (AlgebraTensorModule.map c (LinearMap.id (R := R) (M := N))).restrictScalars R := by
    ext m n
    simp [IsBaseChange.equiv_tmul]
  rw [heq]
  exact h2

theorem bijective_of_mulTensor {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (μ : M ⊗[R] N →ₗ[R] P)
    (s : Set R) (hs : Ideal.span s = ⊤) (B : s → Type*) [∀ r, CommRing (B r)]
    [∀ r, Algebra R (B r)] [∀ r : s, IsLocalization.Away r.1 (B r)]
    (c : ∀ r, M →ₗ[R] B r) (d : ∀ r, N →ₗ[R] B r) (e : ∀ r, P →ₗ[R] B r)
    [∀ r : s, IsLocalizedModule.Away r.1 (c r)] [∀ r : s, IsLocalizedModule.Away r.1 (d r)]
    [∀ r : s, IsLocalizedModule.Away r.1 (e r)]
    (h : ∀ r m n, e r (μ (m ⊗ₜ n)) = c r m * d r n) : Function.Bijective μ := by
  have (r : s) := isLocalizedModule_mulTensor r.1 (c r) (d r)
  refine bijective_of_isLocalized_span s hs (fun r => B r)
    (fun r => TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (fun r => B r) e μ
    fun r => ?_
  have : IsLocalizedModule.map (.powers r.1)
      (TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (e r) μ = LinearMap.id := by
    apply IsLocalizedModule.linearMap_ext (.powers r.1)
      (TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (e r)
    rw [IsLocalizedModule.map_comp]
    ext m n
    simp [h]
  rw [this]
  exact Function.bijective_id

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

variable {T : Scheme.{0}}

def mulFun (A B : LB T) (s : LB.Sec A) (t : LB.Sec B) (p : A.ι × B.ι) :
    Γ(T, A.U p.1 ⊓ B.U p.2) :=
  resG T (inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ A.U p.1) (s.f p.1) *
    resG T (inf_le_right : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2) (t.f p.2)

def mulSec (A B : LB T) (s : LB.Sec A) (t : LB.Sec B) : LB.Sec (CechPic.tens A B) where
  f := mulFun A B s t
  compat := fun (p q : A.ι × B.ι) => by
    unfold CechPic.tens
    change resG T _ (_ * _) = _ * resG T _ (_ * _)
    simp only [map_mul, resG_resG]
    rw [sec_rel s p.1 q.1 (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)),
      sec_rel t p.2 q.2 (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))]
    simp only [Units.val_mul, val_res, resG_resG]
    ring

def mulBil (A B : LB T) :
    LB.Sec A →ₗ[Γ(T, ⊤)] LB.Sec B →ₗ[Γ(T, ⊤)] LB.Sec (CechPic.tens A B) :=
  LinearMap.mk₂ Γ(T, ⊤) (mulSec A B)
    (fun s s' t => f_injective (show mulFun A B (s + s') t = mulFun A B s t + mulFun A B s' t from
      funext fun p => by simp only [mulFun, add_f, map_add, add_mul, Pi.add_apply]))
    (fun a s t => f_injective (show mulFun A B (a • s) t =
      fun (p : A.ι × B.ι) => resG T (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) a * mulFun A B s t p
      from funext fun p => by simp only [mulFun, smul_f, map_mul, resG_resG]; ring))
    (fun s t t' => f_injective (show mulFun A B s (t + t') = mulFun A B s t + mulFun A B s t' from
      funext fun p => by simp only [mulFun, add_f, map_add, mul_add, Pi.add_apply]))
    (fun a s t => f_injective (show mulFun A B s (a • t) =
      fun (p : A.ι × B.ι) => resG T (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) a * mulFun A B s t p
      from funext fun p => by simp only [mulFun, smul_f, map_mul, resG_resG]; ring))

def chartLoc (L : LB T) (r : Γ(T, ⊤)) (i : L.ι) (h : T.basicOpen r ≤ L.U i) :
    LB.Sec L →ₗ[Γ(T, ⊤)] Γ(T, T.basicOpen r) where
  toFun s := resG T h (s.f i)
  map_add' s t := by simp only [add_f, map_add]
  map_smul' a s := by
    simp only [smul_f, map_mul, resG_resG, RingHom.id_apply, Algebra.smul_def]
    rfl

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

variable {T : Scheme.{0}}

def chartEquivTop (L : LB T) (hL : L.IsLB) (r : Γ(T, ⊤)) (i : L.ι) (h : T.basicOpen r ≤ L.U i) :
    AbLaw.SecOn L (T.basicOpen r) ≃ₗ[Γ(T, ⊤)] Γ(T, T.basicOpen r) :=
  { chartEquiv hL i h with
    map_smul' := fun a s => by
      rw [AbLaw.SecOn.smul_basicOpen_def]
      exact ((chartEquiv hL i h).map_smul _ s).trans (Algebra.smul_def a _).symm }

theorem isLocalizedModule_chartLoc [IsAffine T] (L : LB T) (hL : L.IsLB) (r : Γ(T, ⊤)) (i : L.ι)
    (h : T.basicOpen r ≤ L.U i) : IsLocalizedModule.Away r (chartLoc L r i h) := by
  haveI := AbLaw.SecOn.isLocalizedModule_resBasicOpen hL (isAffineOpen_top T) r
  haveI := IsLocalizedModule.of_linearEquiv (S := .powers r) (f := AbLaw.SecOn.resBasicOpen L r)
    (chartEquivTop L hL r i h)
  haveI := IsLocalizedModule.of_linearEquiv_right (S := .powers r)
    (f := (chartEquivTop L hL r i h).toLinearMap ∘ₗ AbLaw.SecOn.resBasicOpen L r)
    (globalEquiv L).symm
  have e : chartLoc L r i h = ((chartEquivTop L hL r i h).toLinearMap ∘ₗ
      AbLaw.SecOn.resBasicOpen L r) ∘ₗ (globalEquiv L).symm.toLinearMap := by
    ext s
    change resG T h (s.f i) = chartEquiv hL i h (AbLaw.SecOn.restrict L _ (ofSec s ⊤))
    rw [chartEquiv_apply, AbLaw.SecOn.restrict_eq_map, coord_map, coord_ofSec, resG_resG, resG_resG]
  rw [e]
  infer_instance

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

theorem tensorSecEquiv : ∀ (T : Scheme.{0}) [IsAffine T] (A B : LB T), A.IsLB → B.IsLB →
    Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)]
      LB.Sec (GlobalTheory.CechPic.tens A B)) := by
  intro T _ A B hA hB
  let s : Set Γ(T, ⊤) := {f | ∃ i j, T.basicOpen f ≤ A.U i ⊓ B.U j}
  have hs : Ideal.span s = ⊤ := by
    rw [← (isAffineOpen_top T).self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hA.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hB.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨f, hf, hxf⟩ := (isAffineOpen_top T).exists_basicOpen_le (V := A.U i ⊓ B.U j) ⟨x, hi, hj⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, j, hf⟩, hxf⟩
  have (r : s) := (isAffineOpen_top T).isLocalization_basicOpen r.1
  let i (r : s) : A.ι := r.2.choose
  let j (r : s) : B.ι := r.2.choose_spec.choose
  have hij (r : s) : T.basicOpen r.1 ≤ A.U (i r) ⊓ B.U (j r) := r.2.choose_spec.choose_spec
  have (r : s) := isLocalizedModule_chartLoc A hA r.1 (i r) ((hij r).trans inf_le_left)
  have (r : s) := isLocalizedModule_chartLoc B hB r.1 (j r) ((hij r).trans inf_le_right)
  have (r : s) := isLocalizedModule_chartLoc (CechPic.tens A B) (CechPic.isLB_tens hA hB) r.1
    ((i r, j r) : A.ι × B.ι) (hij r)
  refine ⟨LinearEquiv.ofBijective (TensorProduct.lift (mulBil A B))
    (bijective_of_mulTensor _ s hs (fun r => Γ(T, T.basicOpen r.1))
      (fun r => chartLoc A r.1 (i r) ((hij r).trans inf_le_left))
      (fun r => chartLoc B r.1 (j r) ((hij r).trans inf_le_right))
      (fun r => chartLoc (CechPic.tens A B) r.1 ((i r, j r) : A.ι × B.ι) (hij r))
      fun r m n => ?_)⟩
  rw [TensorProduct.lift.tmul]
  change resG T (hij r) (mulFun A B m n (i r, j r)) = _ * _
  simp only [mulFun, map_mul, resG_resG]
  rfl

end GlobalTheory.SecTensor
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_tensor_lineBundle_globalSections_equiv : ∀ (T : Scheme.{0}) [IsAffine T] (A B : LB T), A.IsLB → B.IsLB → Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)] LB.Sec (GlobalTheory.CechPic.tens A B)) := by
  atlas_forward_decl GlobalTheory.SecTensor.tensorSecEquiv
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowNowhereZero

theorem tensSec (T : Scheme.{0}) [IsAffine T] (A B : LB T) (hA : A.IsLB) (hB : B.IsLB) :
    Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)] LB.Sec (CechPic.tens A B)) :=
  GlobalTheory.T.nonempty_tensor_lineBundle_globalSections_equiv T A B hA hB

variable {T : Scheme.{0}}

def tp (L : LB T) (k : ℕ) : LB T :=
  Nat.rec (LB.triv T) (fun _ M => CechPic.tens L M) k

theorem isLB_tp {L : LB T} (hL : L.IsLB) : ∀ k, (tp L k).IsLB
  | 0 => LB.isLB_triv T
  | k + 1 => CechPic.isLB_tens hL (isLB_tp hL k)

theorem cls_tp {L : LB T} (hL : L.IsLB) : ∀ k, CechPic.cls (tp L k) (isLB_tp hL k) = k • CechPic.cls L hL
  | 0 => by simp only [zero_smul]; rfl
  | k + 1 => by
    rw [succ_nsmul']
    change CechPic.cls (CechPic.tens L (tp L k)) (CechPic.isLB_tens hL (isLB_tp hL k)) = _
    rw [CechPic.cls_tens hL (isLB_tp hL k), cls_tp hL k]

theorem mk_tp [IsAffine T] {L : LB T} (hL : L.IsLB) : ∀ k,
    @CommRing.Pic.mk Γ(T, ⊤) (LB.Sec (tp L k)) _ _ _ (LB.invertible_sec_top (isLB_tp hL k)) =
      (@CommRing.Pic.mk Γ(T, ⊤) (LB.Sec L) _ _ _ (LB.invertible_sec_top hL)) ^ k
  | 0 => by
    have := LB.invertible_sec_top (isLB_tp hL 0)
    rw [pow_zero, CommRing.Pic.mk_eq_one_iff_free, ← LB.exists_isGen_iff_free_top (isLB_tp hL 0),
      ← CechPic.cls_eq_zero_iff (isLB_tp hL 0)]
    rfl
  | k + 1 => by
    have := LB.invertible_sec_top hL
    have := LB.invertible_sec_top (isLB_tp hL k)
    have : Module.Invertible Γ(T, ⊤) (LB.Sec (CechPic.tens L (tp L k))) :=
      LB.invertible_sec_top (CechPic.isLB_tens hL (isLB_tp hL k))
    obtain ⟨e⟩ := tensSec T L (tp L k) hL (isLB_tp hL k)
    rw [pow_succ', ← mk_tp hL k, ← CommRing.Pic.mk_tensor]
    exact (CommRing.Pic.mk_eq_mk_iff.2 ⟨e⟩).symm

theorem main : ∀ (T : Scheme.{0}) [IsAffine T] [AlgebraicGeometry.IsReduced T], Module.Finite ℤ Γ(T, ⊤) →
    ∀ L : LB T, L.IsLB → ∃ (n : ℕ) (s : (lbPow L n).Sec), 1 ≤ n ∧ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ := by
  intro T _ _ hfin L hL
  have := LB.invertible_sec_top hL
  obtain ⟨n, hn, hpow⟩ := (GlobalTheory.T.isOfFinOrder_pic_of_isReduced_finite_int Γ(T, ⊤) (CommRing.Pic.mk Γ(T, ⊤) (LB.Sec L))).exists_pow_eq_one
  have hk := isLB_tp hL n
  have := LB.invertible_sec_top hk
  have h1 : CechPic.cls (tp L n) hk = 0 := by
    rw [CechPic.cls_eq_zero_iff hk, LB.exists_isGen_iff_free_top hk, ← CommRing.Pic.mk_eq_one_iff_free, mk_tp hL n,
      hpow]
  have hP : (lbPow L n).IsLB := LB.isLB_linComb hL _ _
  have h2 : CechPic.cls (lbPow L n) hP = 0 := by rw [CechPic.cls_lbPow hL n hP, ← cls_tp hL n, h1]
  obtain ⟨t, ht⟩ := (CechPic.cls_eq_zero_iff hP).1 h2
  refine ⟨n, DVR.genSec t ht, hn, top_unique fun x _ => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hP.cover.ge (Opens.mem_top x))
  refine Opens.mem_iSup.2 ⟨i, ?_⟩
  change x ∈ T.basicOpen ((t.s i : Γ(T, (lbPow L n).U i)))
  rw [Scheme.basicOpen_of_isUnit _ (t.s i).isUnit]
  exact hi

end GlobalTheory.PowNowhereZero
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nowhereZero_section_lineBundle_pow_finite_int : ∀ (T : Scheme.{0}) [IsAffine T] [AlgebraicGeometry.IsReduced T], Module.Finite ℤ Γ(T, ⊤) → ∀ L : LB T, L.IsLB → ∃ (n : ℕ) (s : (lbPow L n).Sec), 1 ≤ n ∧ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ := by
  atlas_forward_decl GlobalTheory.PowNowhereZero.main
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_pow_section_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ T : Set X, IsClosed T → (∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, T ⊆ NV P e 0 f := by
  intro k _ X _ p D hX P hA T hT hfin
  let Z : Closeds X := ⟨T, hT⟩
  obtain ⟨hAff, hFin⟩ := GlobalTheory.T.closedSubset_finiteFibres_isAffine_finite_int k X p D hX Z hfin
  haveI := hAff
  haveI := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  let i := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  obtain ⟨n, s, hn, hs⟩ := GlobalTheory.T.exists_nowhereZero_section_lineBundle_pow_finite_int _ hFin (P.L.B.pull i) (LB.isLB_pull hA.isLB i)
  obtain ⟨N, u, hN, hu⟩ := GlobalTheory.T.exists_ample_power_lift_of_nonvanishing_on_closed k X p D hX P.L.B hA _ i n s hn hs
  obtain ⟨f, hf, hfu⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P N).1 u
  refine ⟨N, hN, f, hf, ?_⟩
  rw [hfu]
  intro x hx
  apply hu
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hx

end GlobalTheory.HSAmp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_pow_section_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ T : Set X, IsClosed T → (∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, T ⊆ NV P e 0 f := by
  atlas_forward_decl GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed
end
