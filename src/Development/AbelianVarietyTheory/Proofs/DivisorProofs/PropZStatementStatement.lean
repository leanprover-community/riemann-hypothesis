import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationConstantOfPowerEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_constant_of_power_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (D : LB Z), D.IsLB →
  ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
  ∀ (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen), 1 ≤ M → gen.IsGen → PowEq f ϖ hϖ D sig M n gen →
  ValConst f ϖ D sig M n := by
  first | exact @GlobalTheory.ValConstOfPowEq.valConst_of_powEq | exact GlobalTheory.ValConstOfPowEq.valConst_of_powEq | (intros; apply GlobalTheory.ValConstOfPowEq.valConst_of_powEq <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericRatSec

open ReciprocityTheory.ChartRestriction.G.DVR (res_res' pullU_res res_pullU_eq)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

abbrev unifOn {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O)) (ϖ : O) : Γ(Z, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)

theorem isOpenImmersion_genericι {ϖ : O} (hϖ : Irreducible ϖ) {Z : Scheme.{0}}
    (f : Z ⟶ Spec (.of O)) : IsOpenImmersion (genericι f) := by
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.isOpenImmersion_frac hϖ
  exact inferInstanceAs (IsOpenImmersion (pullback.fst f (Spec.map _)))

theorem opensRange_genericι {ϖ : O} (hϖ : Irreducible ϖ) {Z : Scheme.{0}}
    (f : Z ⟶ Spec (.of O)) :
    haveI := isOpenImmersion_genericι hϖ f
    (genericι f).opensRange = Z.basicOpen (unifOn f ϖ) := by
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.isOpenImmersion_frac hϖ
  change (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))).opensRange = _
  rw [Scheme.Hom.opensRange_pullbackFst,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.opensRange_frac hϖ, Scheme.preimage_basicOpen_top]

theorem gen_mem_basicOpen {ϖ : O} (hϖ : Irreducible ϖ) {Z : Scheme.{0}} [IsIntegral Z]
    (f : Z ⟶ Spec (.of O)) [Flat f] : genericPoint Z ∈ Z.basicOpen (unifOn f ϖ) := by
  set x := genericPoint Z
  set r' := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ with hr'def
  have hr' : r' ≠ 0 := by
    intro h0
    apply hϖ.ne_zero
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom h0
    rwa [hr'def, Iso.inv_hom_id_apply, map_zero] at this
  set g := (Spec (.of O)).presheaf.germ ⊤ (f.base x) trivial r' with hgdef
  have hg : g ≠ 0 := fun h0 =>
    hr' (germ_injective_of_isIntegral (Spec (.of O)) (U := ⊤) (f.base x) trivial
      (h0.trans (map_zero _).symm))
  letI := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat _ (Z.presheaf.stalk x) := Flat.stalkMap f x
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Z.presheaf.stalk x)
    (mem_nonZeroDivisors_of_ne_zero hg)
  rw [Scheme.mem_basicOpen_top]
  have h1 : (f.stalkMap x).hom g = Z.presheaf.germ ⊤ x trivial (unifOn f ϖ) :=
    Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial r'
  rw [← h1]
  refine (isUnit_iff_ne_zero (G₀ := Z.functionField)).2 (fun h0 => ?_)
  have e : g • (1 : Z.presheaf.stalk x) = g • 0 := by
    rw [smul_zero, Algebra.smul_def, mul_one]; exact h0
  exact one_ne_zero (α := Z.functionField) (hreg e)

section Main

theorem res_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (u : Γ(X, U)ˣ) : res h u = u := by
  ext
  simp [res]

theorem res_injective {X : Scheme.{0}} {A B : X.Opens} (h : A ≤ B) (h' : B ≤ A) :
    Function.Injective (res h) := fun a b e => by
  have := congrArg (res h') e
  rwa [res_res', res_res', res_self, res_self] at this

variable {ϖ : O} {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O))

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem preimage_le (D : LB Z) (i : D.ι) (W : Z.Opens) (hW : W ≤ D.U i) :
    genericι f ⁻¹ᵁ W ≤ (D.pull (genericι f)).U (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hW hy

theorem fnOf_res [IsIntegral Z] {U V : Z.Opens} (e : V ≤ U) (h : genericPoint Z ∈ V) (u : Γ(Z, U)ˣ) :
    fnOf V h (res e u : Γ(Z, V)) = fnOf U (e h) u :=
  Z.presheaf.germ_res_apply (homOfLE e) _ h _

variable (hϖ : Irreducible ϖ)
include hϖ

theorem exists_pre (W : Z.Opens) (hW : W ≤ Z.basicOpen (unifOn f ϖ))
    (u : Γ(genericFibre f, genericι f ⁻¹ᵁ W)ˣ) : ∃ a : Γ(Z, W)ˣ, pullU (genericι f) W a = u := by
  haveI := isOpenImmersion_genericι hϖ f
  haveI := Scheme.Hom.isIso_app (genericι f) W (hW.trans (opensRange_genericι hϖ f).ge)
  let e := RingEquiv.ofBijective ((genericι f).app W).hom (ConcreteCategory.bijective_of_isIso _)
  refine ⟨Units.map e.symm.toMonoidHom u, Units.ext ?_⟩
  show ((genericι f).app W).hom (e.symm u) = u
  exact e.apply_symm_apply _

theorem app_injective (W : Z.Opens) (hW : W ≤ Z.basicOpen (unifOn f ϖ)) :
    Function.Injective ((genericι f).app W).hom := by
  haveI := isOpenImmersion_genericι hϖ f
  haveI := Scheme.Hom.isIso_app (genericι f) W (hW.trans (opensRange_genericι hϖ f).ge)
  exact (ConcreteCategory.bijective_of_isIso _).1

theorem pullU_injective (W : Z.Opens) (hW : W ≤ Z.basicOpen (unifOn f ϖ)) :
    Function.Injective (pullU (genericι f) W) := fun _ _ h =>
  Units.ext (app_injective f hϖ W hW (congrArg Units.val h))

def locU (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι) :
    Γ(Z, D.U i ⊓ Z.basicOpen (unifOn f ϖ))ˣ :=
  (exists_pre f hϖ _ inf_le_right
    (res (preimage_le f D i _ inf_le_left) (sig.s (fun _ => i)))).choose

theorem pullU_locU (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι) :
    pullU (genericι f) _ (locU f hϖ D sig i) =
      res (preimage_le f D i _ inf_le_left) (sig.s (fun _ => i)) :=
  (exists_pre f hϖ _ inf_le_right _).choose_spec

theorem pullU_res_locU (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι) (W : Z.Opens)
    (hW : W ≤ D.U i ⊓ Z.basicOpen (unifOn f ϖ)) :
    pullU (genericι f) W (res hW (locU f hϖ D sig i)) =
      res (preimage_le f D i W (hW.trans inf_le_left)) (sig.s (fun _ => i)) := by
  rw [pullU_res, pullU_locU, res_res']

variable [IsIntegral Z]

open Classical in

def tau (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι) : Z.functionFieldˣ :=
  if h : genericPoint Z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ) then
    Units.map (fnOf _ h).toMonoidHom (locU f hϖ D sig i) else 1

theorem val_tau (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι)
    (h : genericPoint Z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ)) :
    (tau f hϖ D sig i : Z.functionField) = fnOf _ h (locU f hϖ D sig i) := by
  rw [tau, dif_pos h]; rfl

theorem isRatSec_tau [Flat f] (D : LB Z) (sig : (D.pull (genericι f)).Gen) (hsig : sig.IsGen) :
    IsRatSec D (tau f hϖ D sig) := by
  intro i j h
  have hV := gen_mem_basicOpen hϖ f
  set V := Z.basicOpen (unifOn f ϖ) with hVdef
  have hi : genericPoint Z ∈ D.U i ⊓ V := ⟨h.1, hV⟩
  have hj : genericPoint Z ∈ D.U j ⊓ V := ⟨h.2, hV⟩
  have hW : genericPoint Z ∈ D.U i ⊓ D.U j ⊓ V := ⟨h, hV⟩
  have claim : res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        D.U i ⊓ D.U j ⊓ V ≤ D.U i ⊓ V) (locU f hϖ D sig i) =
      res (inf_le_left : D.U i ⊓ D.U j ⊓ V ≤ D.U i ⊓ D.U j) (D.g i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        D.U i ⊓ D.U j ⊓ V ≤ D.U j ⊓ V) (locU f hϖ D sig j) := by
    apply pullU_injective f hϖ _ inf_le_right
    rw [map_mul, pullU_res_locU, pullU_res_locU, pullU_res]
    have e := congrArg (res (fun _ hy => ⟨(preimage_le f D i _ (inf_le_left.trans inf_le_left)) hy,
        (preimage_le f D j _ (inf_le_left.trans inf_le_right)) hy⟩ :
        genericι f ⁻¹ᵁ (D.U i ⊓ D.U j ⊓ V) ≤
          (D.pull (genericι f)).U (fun _ => i) ⊓ (D.pull (genericι f)).U (fun _ => j)))
      (hsig (fun _ => i) (fun _ => j))
    rw [map_mul] at e
    erw [res_res', res_res'] at e
    erw [e]
    congr 1
    show res _ (∏ _k : PUnit, (res _ (pullU (genericι f) _ (D.g i j))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    erw [res_res']
  have e := congrArg (fun u : Γ(Z, D.U i ⊓ D.U j ⊓ V)ˣ => fnOf _ hW (u : Γ(Z, _))) claim
  simp only [Units.val_mul, map_mul, fnOf_res] at e
  rw [val_tau f hϖ D sig i hi, val_tau f hϖ D sig j hj]
  exact e

theorem unitAt_tau (D : LB Z) (sig : (D.pull (genericι f)).Gen) (i : D.ι) (z : Z)
    (hz : z ∈ D.U i) (hz' : z ∈ Z.basicOpen (unifOn f ϖ)) :
    UnitAt z (tau f hϖ D sig i : Z.functionField) := by
  have h : genericPoint Z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ) := gen_mem (show z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ) from ⟨hz, hz'⟩)
  rw [val_tau f hϖ D sig i h]
  exact unitAt_fnOf (show z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ) from ⟨hz, hz'⟩) h _

end Main

section Pow

variable {ϖ : O} {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O)) (hϖ : Irreducible ϖ)

theorem val_constUnit :
    ((constUnit (genericStr f) (unifUnit ϖ hϖ) : Γ(genericFibre f, ⊤)ˣ) : Γ(genericFibre f, ⊤)) =
      (genericι f).appTop.hom (unifOn f ϖ) := by
  show (genericStr f).appTop.hom ((Scheme.ΓSpecIso (.of (FractionRing O))).inv.hom
    (algebraMap O (FractionRing O) ϖ)) = _
  have h1 : (Scheme.ΓSpecIso (.of (FractionRing O))).inv.hom (algebraMap O (FractionRing O) ϖ) =
      (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))).appTop.hom
        ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) :=
    congrArg (fun t => t.hom ϖ)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O (FractionRing O))))
  have h2 := congrArg (fun t => t.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ))
    (pullback.condition (f := f) (g := Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))
  rw [h1]
  exact h2.symm

include hϖ

theorem exists_unif (W : Z.Opens) (hWV : W ≤ Z.basicOpen (unifOn f ϖ))
    (hle : genericι f ⁻¹ᵁ W ≤ ⊤) [IsIntegral Z] :
    ∃ b : Γ(Z, W)ˣ, pullU (genericι f) W b = res hle (constUnit (genericStr f) (unifUnit ϖ hϖ)) ∧
      ∀ hW : genericPoint Z ∈ W, fnOf W hW b = fnOf ⊤ trivial (unifOn f ϖ) := by
  obtain ⟨b, hb⟩ := exists_pre f hϖ W hWV (res hle (constUnit (genericStr f) (unifUnit ϖ hϖ)))
  refine ⟨b, hb, fun hW => ?_⟩
  have e : (b : Γ(Z, W)) = (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (unifOn f ϖ) := by
    apply app_injective f hϖ W hWV
    refine (congrArg Units.val hb).trans ?_
    show ((genericFibre f).presheaf.map (homOfLE hle).op).hom
      ((constUnit (genericStr f) (unifUnit ϖ hϖ) : Γ(genericFibre f, ⊤)ˣ) : Γ(genericFibre f, ⊤)) = _
    rw [val_constUnit f hϖ]
    exact (congrArg (fun t => t.hom (unifOn f ϖ))
      (Scheme.Hom.naturality (genericι f) (homOfLE (le_top : W ≤ ⊤)).op)).symm
  rw [e]
  exact Z.presheaf.germ_res_apply (homOfLE le_top) _ hW _

theorem powEq_of [IsIntegral Z] (D : LB Z) (sig : (D.pull (genericι f)).Gen) (M : ℕ) (n : ℤ)
    (gen : (lbPow D M).Gen)
    (H : ∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
      fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (unifOn f ϖ) ^ n =
        (tau f hϖ D sig i : Z.functionField) ^ M) :
    PowEq f ϖ hϖ D sig M n gen := by
  intro j
  obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j PUnit.unit, funext fun _ => rfl⟩
  haveI := isOpenImmersion_genericι hϖ f
  have hle := preimage_le f D i (D.U i ⊓ Z.basicOpen (unifOn f ϖ)) inf_le_left
  have hle' : (D.pull (genericι f)).U (fun _ => i) ≤
      genericι f ⁻¹ᵁ (D.U i ⊓ Z.basicOpen (unifOn f ϖ)) := fun y hy =>
    ⟨Set.mem_iInter.1 hy PUnit.unit,
      (opensRange_genericι hϖ f).le (show (genericι f).base y ∈ (genericι f).opensRange from ⟨y, rfl⟩)⟩
  apply res_injective hle hle'
  show res hle ((sig.s (fun _ => i)) ^ M) = res hle ((res _ (constUnit (genericStr f) (unifUnit ϖ hϖ))) ^ n *
    res _ (pullU (genericι f) (D.U i) (gen.s i)))
  obtain ⟨b, hb, hbf⟩ := exists_unif f hϖ (D.U i ⊓ Z.basicOpen (unifOn f ϖ)) inf_le_right le_top
  erw [map_mul, map_pow, map_zpow, ← pullU_locU f hϖ D sig i, res_res', res_res', ← hb,
    res_pullU_eq (genericι f) (inf_le_left : D.U i ⊓ Z.basicOpen (unifOn f ϖ) ≤ D.U i) _ le_rfl,
    res_self, ← map_pow, ← map_zpow, ← map_mul]
  congr 1
  by_cases hW : genericPoint Z ∈ D.U i ⊓ Z.basicOpen (unifOn f ϖ)
  · apply Units.map_injective (f := (fnOf _ hW).toMonoidHom) (fnOf_injective _ hW)
    apply Units.ext
    simp only [map_pow, map_zpow, map_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [← val_tau f hϖ D sig i hW, hbf hW]
    erw [fnOf_res]
    rw [← H i hW.1, mul_comm]
    rfl
  · exact Units.ext (fn_ext fun h => (hW h).elim)

end Pow

theorem exists_ratSec : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Flat f → D.IsLB →
  ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
  ∃ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ ∧
    (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
      UnitAt z (τ i : Z.functionField)) ∧
    ∀ (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen),
      (∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
        fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n =
          (τ i : Z.functionField) ^ M) →
      PowEq f ϖ hϖ D sig M n gen := by
  intro O _ _ _ ϖ hϖ Z _ f D hf _ sig hsig
  refine ⟨tau f hϖ D sig, isRatSec_tau f hϖ D sig hsig, fun i z hz hz' => unitAt_tau f hϖ D sig i z hz hz',
    fun M n gen H => powEq_of f hϖ D sig M n gen H⟩

end GlobalTheory.GenericRatSec
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratSec_unit_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Flat f → D.IsLB →
  ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
  ∃ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ ∧
    (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
      UnitAt z (τ i : Z.functionField)) ∧
    ∀ (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen),
      (∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
        fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n =
          (τ i : Z.functionField) ^ M) →
      PowEq f ϖ hϖ D sig M n gen := by
  atlas_forward_decl GlobalTheory.GenericRatSec.exists_ratSec
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.FlatDVRFibre

theorem mem_basicOpen_unif_iff {O : Type} [CommRing O] {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O)) (ϖ : O) (z : Z) :
    z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ↔ ϖ ∉ (f z).asIdeal := by
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen _ _

theorem genericPoint_mem_and_exists_not_mem :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)), Flat f → Nonempty (specialFibre f) →
  genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ∧ ∃ z : Z, z ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) := by
  intro O _ _ _ ϖ hϖ Z _ f hf hne
  refine ⟨?_, ?_⟩
  · rw [mem_basicOpen_unif_iff]
    let e : Spec (.of O) := (⊥ : PrimeSpectrum O)
    have hη : e ⤳ f (genericPoint Z) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (bot_le (α := PrimeSpectrum O))
    obtain ⟨x', hx', hx''⟩ := Flat.generalizingMap f hη
    have hxe : x' = genericPoint Z :=
      (hx'.antisymm (genericPoint_specializes x')).eq
    rw [← hxe, hx'']
    change ϖ ∉ (⊥ : Ideal O)
    simpa using hϖ.ne_zero
  · obtain ⟨p⟩ := hne
    refine ⟨specialι f p, ?_⟩
    rw [mem_basicOpen_unif_iff, not_not]
    have h1 : f (specialι f p) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
        (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) p) := by
      let p' : ↑(pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) := p
      change f (pullback.fst f _ p') = _
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [h1]
    set q := pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) p
    change ϖ ∈ Ideal.comap (IsLocalRing.residue O) q.asIdeal
    haveI := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [hq, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
    exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit

end GlobalTheory.FlatDVRFibre
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_scheme_special_fibre_nonempty : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)), Flat f → Nonempty (specialFibre f) →
  genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ∧ ∃ z : Z, z ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) := by
  atlas_forward_decl GlobalTheory.FlatDVRFibre.genericPoint_mem_and_exists_not_mem
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.ExpChoice

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_zpow {z : X} {u : X.functionField} (h : UnitAt z u) (n : ℤ) : UnitAt z (u ^ n) := by
  have hp : ∀ k : ℕ, UnitAt z (u ^ k) := fun k => by
    induction k with
    | zero => simpa using unitAt_one z
    | succ k ih => rw [pow_succ]; exact ih.mul h
  rcases n with k | k
  · simpa using hp k
  · rw [zpow_negSucc]; exact (hp (k+1)).inv

section DVR

variable {z : X} [IsDiscreteValuationRing (X.presheaf.stalk z)]

theorem exists_unit_mul_zpow {ϖ : X.presheaf.stalk z} (hϖ : Irreducible ϖ) {f : X.functionField}
    (hf : f ≠ 0) : ∃ (k : ℤ) (u : X.functionField), UnitAt z u ∧
      f = u * algebraMap _ X.functionField ϖ ^ k := by
  have hinj := IsFractionRing.injective (X.presheaf.stalk z) X.functionField
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk z) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨na, ua, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨nb, ub, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hp : algebraMap _ X.functionField ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hub : algebraMap _ X.functionField (ub : X.presheaf.stalk z) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 ub.ne_zero
  refine ⟨(na : ℤ) - nb, algebraMap _ X.functionField (ua : X.presheaf.stalk z) /
    algebraMap _ X.functionField (ub : X.presheaf.stalk z), ?_, ?_⟩
  · rw [div_eq_mul_inv]
    exact UnitAt.mul ⟨_, ua.isUnit, rfl⟩ (UnitAt.inv ⟨_, ub.isUnit, rfl⟩)
  · rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow]
    field_simp

theorem regAt_unit_mul_zpow_iff {ϖ : X.presheaf.stalk z} (hϖ : Irreducible ϖ) {u : X.functionField}
    (hu : UnitAt z u) (k : ℤ) :
    RegAt z (u * algebraMap _ X.functionField ϖ ^ k) ↔ 0 ≤ k := by
  have hinj := IsFractionRing.injective (X.presheaf.stalk z) X.functionField
  have hp : algebraMap _ X.functionField ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  constructor
  · rintro ⟨a, ha⟩
    by_contra hk
    push_neg at hk
    obtain ⟨b, -, hbu⟩ := hu.inv
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = -k - 1 := ⟨(-k - 1).toNat, Int.toNat_of_nonneg (by omega)⟩
    have e : algebraMap _ X.functionField (ϖ * (b * a * ϖ ^ j)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_pow, hbu, ha, ← zpow_natCast, hj]
      have hu0 := hu.ne_zero
      calc algebraMap _ X.functionField ϖ * (u⁻¹ * (u * algebraMap _ X.functionField ϖ ^ k) *
            algebraMap _ X.functionField ϖ ^ (-k - 1))
          = algebraMap _ X.functionField ϖ ^ (1 + k + (-k - 1)) := by
            rw [zpow_add₀ hp, zpow_add₀ hp, zpow_one]
            field_simp
        _ = 1 := by rw [show 1 + k + (-k - 1) = 0 by ring, zpow_zero]
    rw [← map_one (algebraMap (X.presheaf.stalk z) X.functionField)] at e
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ (hinj e))
  · intro hk
    refine hu.regAt.mul ⟨ϖ ^ k.toNat, ?_⟩
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg hk]

end DVR

theorem finite_dvr_notMem [IsLocallyNoetherian X] [CompactSpace X] (π : Γ(X, ⊤))
    (hπ : genericPoint X ∈ X.basicOpen π) :
    {z : X | z ∉ X.basicOpen π ∧ IsDiscreteValuationRing (X.presheaf.stalk z)}.Finite := by
  have hπ0 : fnOf ⊤ trivial π ≠ 0 :=
    ((unitAt_fnOf_iff (show genericPoint X ∈ (⊤ : X.Opens) from trivial) trivial π).2 hπ).ne_zero
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, ((U : X.Opens) : Set X) := fun x _ => by
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => (U : X.Opens).isOpen) hcov
  have fin : ∀ U : X.affineOpens,
      ({z : X | z ∉ X.basicOpen π ∧ IsDiscreteValuationRing (X.presheaf.stalk z)} ∩
        ((U : X.Opens) : Set X)).Finite := by
    rintro ⟨U, hU⟩
    by_cases hne : Nonempty U
    swap
    · refine Set.finite_empty.subset fun z hz => hne ⟨⟨z, hz.2⟩⟩
    have hg : genericPoint X ∈ U := by
      obtain ⟨⟨x, hx⟩⟩ := hne
      exact gen_mem hx
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let a : Γ(X, U) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X (le_top : U ≤ ⊤) π
    have ha : a ≠ 0 := by
      intro h0
      apply hπ0
      rw [← fnOf_resG (le_top : U ≤ ⊤) hg π]
      exact (congrArg (fnOf U hg) h0).trans (map_zero _)
    have hba : X.basicOpen a = U ⊓ X.basicOpen π := X.basicOpen_res π (homOfLE (le_top : U ≤ ⊤)).op
    refine ((GlobalTheory.finite_height_eq_one_mem ha).image hU.fromSpec).subset ?_
    rintro z ⟨⟨hzπ, hdvr⟩, hzU⟩
    refine ⟨hU.primeIdealOf ⟨z, hzU⟩, ⟨?_, ?_⟩, hU.fromSpec_primeIdealOf ⟨z, hzU⟩⟩
    · let y : U := ⟨z, hzU⟩
      haveI : IsDiscreteValuationRing (X.presheaf.stalk (y : X)) := hdvr
      letI : Algebra Γ(X, U) (X.presheaf.stalk (y : X)) := X.presheaf.algebra_section_stalk y
      haveI := hU.isLocalization_stalk y
      have e := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf y).asIdeal
        (X.presheaf.stalk (y : X))
      rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at e
      exact_mod_cast e.symm
    · have hz' : hU.fromSpec (hU.primeIdealOf ⟨z, hzU⟩) ∉ X.basicOpen a := by
        rw [hU.fromSpec_primeIdealOf ⟨z, hzU⟩, hba]
        exact fun h => hzπ h.2
      have := mt (fun h => (hU.fromSpec_preimage_basicOpen a).ge h) hz'
      by_contra h
      exact this ((PrimeSpectrum.mem_basicOpen _ _).2 h)
  refine (t.finite_toSet.biUnion fun U _ => fin U).subset fun z hz => ?_
  obtain ⟨U, hU, hzU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
  exact Set.mem_biUnion hU ⟨hz, hzU⟩

theorem exists_dvr_notMem [IsLocallyNoetherian X]
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (π : Γ(X, ⊤))
    (hπ : genericPoint X ∈ X.basicOpen π) {z₀ : X} (hz₀ : z₀ ∉ X.basicOpen π) :
    ∃ z : X, z ∉ X.basicOpen π ∧ IsDiscreteValuationRing (X.presheaf.stalk z) := by
  have hπ0 : fnOf ⊤ trivial π ≠ 0 :=
    ((unitAt_fnOf_iff (show genericPoint X ∈ (⊤ : X.Opens) from trivial) trivial π).2 hπ).ne_zero
  obtain ⟨U, hU, hz₀U, -⟩ := exists_isAffineOpen_mem_and_subset (x := z₀) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨z₀, hz₀U⟩⟩
  have hg : genericPoint X ∈ U := gen_mem hz₀U
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : IsIntegrallyClosed Γ(X, U) := GlobalTheory.isIntegrallyClosed_sections_of_stalks hN hU
  let a : Γ(X, U) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X (le_top : U ≤ ⊤) π
  have ha : a ≠ 0 := by
    intro h0
    apply hπ0
    rw [← fnOf_resG (le_top : U ≤ ⊤) hg π]
    exact (congrArg (fnOf U hg) h0).trans (map_zero _)
  have hba : X.basicOpen a = U ⊓ X.basicOpen π := X.basicOpen_res π (homOfLE (le_top : U ≤ ⊤)).op
  have haq : a ∈ (hU.primeIdealOf ⟨z₀, hz₀U⟩).asIdeal := by
    have hz' : hU.fromSpec (hU.primeIdealOf ⟨z₀, hz₀U⟩) ∉ X.basicOpen a := by
      rw [hU.fromSpec_primeIdealOf ⟨z₀, hz₀U⟩, hba]
      exact fun h => hz₀ h.2
    have := mt (fun h => (hU.fromSpec_preimage_basicOpen a).ge h) hz'
    by_contra h
    exact this ((PrimeSpectrum.mem_basicOpen _ _).2 h)
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 haq)
  haveI : p.IsPrime := hp.1.1
  have hap : a ∈ p := (Ideal.span_singleton_le_iff_mem _).1 hp.1.2
  have h1 : p.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp) ?_
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    rintro rfl
    exact ha hap
  let P : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  have hz : hU.fromSpec P ∈ U := hU.range_fromSpec.le ⟨P, rfl⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec P)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hz⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec P)) p := hU.isLocalization_stalk' P hz
  refine ⟨hU.fromSpec P, fun h => ?_, GlobalTheory.isDiscreteValuationRing_of_height_eq_one p h1 _⟩
  have h2 : hU.fromSpec P ∈ X.basicOpen a := by rw [hba]; exact ⟨hz, h⟩
  have h3 := (hU.fromSpec_preimage_basicOpen a).le h2
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hap

theorem zpow_exponent_identity {K : Type} [Field K] {p : K} (hp : p ≠ 0) (u v : K) (m t n : ℤ) (M : ℕ) :
    (u * p ^ m) ^ n * ((v * p ^ t) ^ M)⁻¹ = (u ^ n * (v ^ (M : ℤ))⁻¹) * p ^ (m * n - t * M) := by
  rw [← zpow_natCast (v * p ^ t), zpow_sub₀ hp, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul,
    mul_inv, mul_comm t]
  ring

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem point_data {z : X} [IsDiscreteValuationRing (X.presheaf.stalk z)] (π : Γ(X, ⊤))
    (hπ0 : fnOf ⊤ trivial π ≠ 0) (hz : z ∉ X.basicOpen π) (L : LB X) (τ : L.ι → X.functionFieldˣ) (hL : L.IsLB)
    (hr : IsRatSec L τ) :
    ∃ (p : X.functionField) (m t : ℤ), p ≠ 0 ∧ 1 ≤ m ∧
      (∀ u, UnitAt z u → ∀ k : ℤ, RegAt z (u * p ^ k) ↔ 0 ≤ k) ∧
      (∃ u, UnitAt z u ∧ fnOf ⊤ trivial π = u * p ^ m) ∧
      ∀ i, z ∈ L.U i → ∃ v, UnitAt z v ∧ (τ i : X.functionField) = v * p ^ t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  have hp : algebraMap _ X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk z) X.functionField)).2 hϖ.ne_zero
  have hzt : z ∈ (⊤ : X.Opens) := trivial
  obtain ⟨m, u, hu, hm⟩ := exists_unit_mul_zpow hϖ hπ0
  obtain ⟨j, hj⟩ := exists_chart hL z
  obtain ⟨t, w, hw, ht⟩ := exists_unit_mul_zpow hϖ (τ j).ne_zero
  refine ⟨_, m, t, hp, ?_, fun u hu k => regAt_unit_mul_zpow_iff hϖ hu k, ⟨u, hu, hm⟩, ?_⟩
  · have h0 : 0 ≤ m := (regAt_unit_mul_zpow_iff hϖ hu m).1 (hm ▸ regAt_fnOf hzt trivial π)
    have h1 : m ≠ 0 := by
      rintro rfl
      rw [zpow_zero, mul_one] at hm
      exact hz ((unitAt_fnOf_iff hzt trivial π).1 (hm ▸ hu))
    omega
  · intro i hi
    have hij : z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
    refine ⟨fnOf _ (gen_mem hij) (L.g i j : Γ(X, L.U i ⊓ L.U j)) * w,
      (unitAt_fnOf hij _ _).mul hw, ?_⟩
    rw [hr i j (gen_mem hij), ht, mul_assoc]

end GlobalTheory.ExpChoice

open GlobalTheory.ExpChoice in

theorem GlobalTheory.ExpChoice.exists_exponents : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X],
  (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
  ∀ (π : Γ(X, ⊤)), genericPoint X ∈ X.basicOpen π → (∃ z : X, z ∉ X.basicOpen π) →
  ∀ (L : LB X) (τ : L.ι → X.functionFieldˣ), L.IsLB → IsRatSec L τ →
    (∀ (i : L.ι) (z : X), z ∈ L.U i → z ∈ X.basicOpen π → UnitAt z (τ i : X.functionField)) →
    ∃ (M : ℕ) (n : ℤ) (x₀ : X), 1 ≤ M ∧ x₀ ∉ X.basicOpen π ∧
      (∀ (i : L.ι) (z : X), z ∈ L.U i → IsDiscreteValuationRing (X.presheaf.stalk z) →
        RegAt z (fnOf ⊤ trivial π ^ n * ((τ i : X.functionField) ^ M)⁻¹)) ∧
      (∀ i : L.ι, x₀ ∈ L.U i → UnitAt x₀ (fnOf ⊤ trivial π ^ n * ((τ i : X.functionField) ^ M)⁻¹)) := by
  intro X _ _ _ hN π hπ ⟨z₀, hz₀⟩ L τ hL hr hτ
  have hπ0 : fnOf ⊤ trivial π ≠ 0 :=
    ((unitAt_fnOf_iff (show genericPoint X ∈ (⊤ : X.Opens) from trivial) trivial π).2 hπ).ne_zero
  set S : Set X := {z | z ∉ X.basicOpen π ∧ IsDiscreteValuationRing (X.presheaf.stalk z)} with hSdef
  have hS : S.Finite := finite_dvr_notMem π hπ
  have hne : S.Nonempty := exists_dvr_notMem hN π hπ hz₀
  have data : ∀ z ∈ S, ∃ (p : X.functionField) (m t : ℤ), p ≠ 0 ∧ 1 ≤ m ∧
      (∀ u, UnitAt z u → ∀ k : ℤ, RegAt z (u * p ^ k) ↔ 0 ≤ k) ∧
      (∃ u, UnitAt z u ∧ fnOf ⊤ trivial π = u * p ^ m) ∧
      ∀ i, z ∈ L.U i → ∃ v, UnitAt z v ∧ (τ i : X.functionField) = v * p ^ t := fun z hz => by
    haveI := hz.2
    exact point_data π hπ0 hz.1 L τ hL hr
  choose! p m t hp hm hreg hπrep hτrep using data
  obtain ⟨x₀, hx₀, hmax⟩ := Set.exists_max_image S (fun z => (t z : ℚ) / (m z)) hS hne
  have hM : (((m x₀).toNat : ℕ) : ℤ) = m x₀ := Int.toNat_of_nonneg (by linarith [hm x₀ hx₀])
  have key : ∀ z ∈ S, ∀ i, z ∈ L.U i → ∃ u, UnitAt z u ∧
      fnOf ⊤ trivial π ^ t x₀ * ((τ i : X.functionField) ^ (m x₀).toNat)⁻¹ =
        u * p z ^ (m z * t x₀ - t z * m x₀) := by
    intro z hz i hi
    obtain ⟨u, hu, e1⟩ := hπrep z hz
    obtain ⟨v, hv, e2⟩ := hτrep z hz i hi
    refine ⟨u ^ t x₀ * (v ^ ((m x₀).toNat : ℤ))⁻¹,
      (unitAt_zpow hu _).mul (unitAt_zpow hv _).inv, ?_⟩
    rw [e1, e2, zpow_exponent_identity (hp z hz), hM]
  refine ⟨(m x₀).toNat, t x₀, x₀, by have := hm x₀ hx₀; omega, hx₀.1, ?_, ?_⟩
  · intro i z hi hdvr
    by_cases hzb : z ∈ X.basicOpen π
    · have h1 := (unitAt_fnOf_iff (show z ∈ (⊤ : X.Opens) from trivial) trivial π).2 hzb
      have h2 := unitAt_zpow (hτ i z hi hzb) ((m x₀).toNat : ℤ)
      rw [zpow_natCast] at h2
      exact ((unitAt_zpow h1 _).mul h2.inv).regAt
    · have hz : z ∈ S := ⟨hzb, hdvr⟩
      obtain ⟨u, hu, e⟩ := key z hz i hi
      rw [e, hreg z hz u hu]
      have h := hmax z hz
      have hmz : (0 : ℚ) < m z := by exact_mod_cast (hm z hz)
      have hm0 : (0 : ℚ) < m x₀ := by exact_mod_cast (hm x₀ hx₀)
      rw [div_le_div_iff₀ hmz hm0] at h
      have h' : t z * m x₀ ≤ t x₀ * m z := by exact_mod_cast h
      linarith
  · intro i hi
    obtain ⟨u, hu, e⟩ := key x₀ hx₀ i hi
    rw [e, mul_comm (m x₀) (t x₀), sub_self, zpow_zero, mul_one]
    exact hu
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_power_section_special_fibre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X],
  (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
  ∀ (π : Γ(X, ⊤)), genericPoint X ∈ X.basicOpen π → (∃ z : X, z ∉ X.basicOpen π) →
  ∀ (L : LB X) (τ : L.ι → X.functionFieldˣ), L.IsLB → IsRatSec L τ →
    (∀ (i : L.ι) (z : X), z ∈ L.U i → z ∈ X.basicOpen π → UnitAt z (τ i : X.functionField)) →
    ∃ (M : ℕ) (n : ℤ) (x₀ : X), 1 ≤ M ∧ x₀ ∉ X.basicOpen π ∧
      (∀ (i : L.ι) (z : X), z ∈ L.U i → IsDiscreteValuationRing (X.presheaf.stalk z) →
        RegAt z (fnOf ⊤ trivial π ^ n * ((τ i : X.functionField) ^ M)⁻¹)) ∧
      (∀ i : L.ι, x₀ ∈ L.U i → UnitAt x₀ (fnOf ⊤ trivial π ^ n * ((τ i : X.functionField) ^ M)⁻¹)) := by
  atlas_forward_decl GlobalTheory.ExpChoice.exists_exponents
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_of_regular_at_codim_one : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
  (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
  ∀ (φ : X.functionField) (x : X),
    (∀ z : X, z ⤳ x → IsDiscreteValuationRing (X.presheaf.stalk z) → RegAt z φ) → RegAt x φ := by
  first | exact @GlobalTheory.Hartogs.regAt_of_forall_dvr | exact GlobalTheory.Hartogs.regAt_of_forall_dvr | (intros; apply GlobalTheory.Hartogs.regAt_of_forall_dvr <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_special_fibre_global_field : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)), IsProper f → ConnectedSpace (specialFibre f) →
  IsField Γ(reducedSpecialFibre f, ⊤) := by
  first | exact @GlobalTheory.RedFibreField.isField_reducedSpecialFibre | exact GlobalTheory.RedFibreField.isField_reducedSpecialFibre | (intros; apply GlobalTheory.RedFibreField.isField_reducedSpecialFibre <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory

theorem exists_reducedSpecialFibre_of_not_mem_basicOpen : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (z : Z),
  z ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → ∃ y : reducedSpecialFibre f, reducedSpecialι f y = z := by
  intro O _ _ _ ϖ hϖ Z f z hz
  have h1 : ϖ ∈ (f z).asIdeal := by
    have : z ∉ f ⁻¹ᵁ (Spec (.of O)).basicOpen ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) := by
      rwa [Scheme.preimage_basicOpen_top]
    have h2 : f z ∉ (Spec (.of O)).basicOpen ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) := this
    rw [basicOpen_eq_of_affine (R := CommRingCat.of O) ϖ] at h2
    by_contra h
    exact h2 ((PrimeSpectrum.mem_basicOpen _ _).2 h)
  have hmax : (f z).asIdeal = IsLocalRing.maximalIdeal O := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (f z).isPrime.ne_top
    · rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_le]
      simpa using h1
  let k := IsLocalRing.ResidueField O
  let pt : Spec (.of k) := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum k)
  have hpt : f z = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) pt := by
    apply PrimeSpectrum.ext
    rw [hmax]
    show IsLocalRing.maximalIdeal O = Ideal.comap (IsLocalRing.residue O) ⊥
    rw [← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) z pt hpt
  have hsupp : p ∈ Set.range (specialFibre f).nilradical.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
    trivial
  obtain ⟨y, hy⟩ := hsupp
  refine ⟨y, ?_⟩
  show (specialι f) ((specialFibre f).nilradical.subschemeι y) = z
  rw [hy]
  exact hp

end GlobalTheory
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_fibre_point : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (z : Z),
  z ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → ∃ y : reducedSpecialFibre f, reducedSpecialι f y = z := by
  atlas_forward_decl GlobalTheory.exists_reducedSpecialFibre_of_not_mem_basicOpen
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.DivGlue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG exists_chart)

theorem resG_app {Y Z : Scheme.{0}} (ι : Y ⟶ Z) {U U' : Z.Opens} (e : U' ≤ U) {V : Y.Opens}
    (h : V ≤ ι ⁻¹ᵁ U') (h' : V ≤ ι ⁻¹ᵁ U) (x : Γ(Z, U)) :
    resG Y h' ((ι.app U).hom x) = resG Y h ((ι.app U').hom (resG Z e x)) := by
  have h1 : ι.app U ≫ Y.presheaf.map (homOfLE h').op = ι.appLE U V h' := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have h2 : Z.presheaf.map (homOfLE e).op ≫ ι.app U' ≫ Y.presheaf.map (homOfLE h).op =
      ι.appLE U V h' := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact (congrArg (fun f => f.hom x) h1).trans (congrArg (fun f => f.hom x) h2).symm

theorem glue : ∀ (Y Z : Scheme.{0}) (ι : Y ⟶ Z) (D : LB Z), D.IsLB → ∀ t : (D.pull ι).Gen, t.IsGen →
  ∀ (M : ℕ) (a : ∀ i, Γ(Z, D.U i)),
  (∀ i j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (a i) * ((D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M =
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (a j)) →
  ∃ h : Γ(Y, ⊤), ∀ (i : D.ι) (y : Y) (hy : ι y ∈ D.U i), ∃ u : (Y.presheaf.stalk y)ˣ,
    (Y.presheaf.germ ⊤ y trivial).hom h = (ι.stalkMap y).hom ((Z.presheaf.germ (D.U i) (ι y) hy).hom (a i)) * (u : Y.presheaf.stalk y) := by
  intro Y Z ι D hD t ht M a ha
  let j : D.ι → (PUnit → D.ι) := fun i _ => i
  let W : D.ι → Y.Opens := fun i => (D.pull ι).U (j i)
  have hW : ∀ i, W i ≤ ι ⁻¹ᵁ D.U i := fun i => LB.wchart_le D _ (j i) PUnit.unit
  let b : ∀ i, Γ(Y, W i) := fun i =>
    resG Y (hW i) ((ι.app (D.U i)).hom (a i)) * ((t.s (j i) ^ M : Γ(Y, (D.pull ι).U (j i))ˣ) : Γ(Y, (D.pull ι).U (j i)))
  have cover : (⊤ : Y.Opens) ≤ iSup W := fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart hD (ι y)
    exact Opens.mem_iSup.2 ⟨i, Set.mem_iInter.2 fun _ => hi⟩
  obtain ⟨h, hh⟩ := GlobalTheory.LB.exists_fun_of_cover W (fun _ => le_top) cover b (by
    intro i i'
    have hV : W i ⊓ W i' ≤ ι ⁻¹ᵁ (D.U i ⊓ D.U i') := fun y hy => ⟨hW i hy.1, hW i' hy.2⟩
    have hA := congrArg (fun x => resG Y hV ((ι.app _).hom x)) (ha i i')
    simp only [map_mul, map_pow] at hA
    simp only [b, map_mul, GlobalTheory.LB.resG_resG]
    rw [← GlobalTheory.LB.val_res, ← GlobalTheory.LB.val_res, map_pow, map_pow, ht (j i) (j i'), mul_pow, Units.val_mul]
    have hG : (((D.pull ι).g (j i) (j i') : Γ(Y, W i ⊓ W i')ˣ) : Γ(Y, W i ⊓ W i')) =
        resG Y hV ((ι.app _).hom (D.g i i' : Γ(Z, D.U i ⊓ D.U i'))) := by
      show ((∏ _k : PUnit, (res hV (pullU ι _ (D.g i i'))) ^ (1 : ℤ) : Γ(Y, W i ⊓ W i')ˣ) :
        Γ(Y, W i ⊓ W i')) = _
      rw [Finset.univ_unique, Finset.prod_singleton, zpow_one]
      rfl
    rw [Units.val_pow_eq_pow_val, hG, resG_app ι inf_le_left hV, resG_app ι inf_le_right hV, ← hA]
    ring)
  refine ⟨h, fun i y hy => ?_⟩
  have hyW : y ∈ W i := Set.mem_iInter.2 fun _ => hy
  refine ⟨Units.map (Y.presheaf.germ (W i) y hyW).hom.toMonoidHom (t.s (j i) ^ M), ?_⟩
  rw [← Y.presheaf.germ_res_apply (homOfLE (le_top : W i ≤ ⊤)) y hyW h]
  change (Y.presheaf.germ (W i) y hyW).hom (resG Y le_top h) = _
  rw [hh i, map_mul]
  congr 1
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact Y.presheaf.germ_res_apply (homOfLE (hW i)) y hyW _

end GlobalTheory.DivGlue
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_section_unit_stalk : ∀ (Y Z : Scheme.{0}) (ι : Y ⟶ Z) (D : LB Z), D.IsLB → ∀ t : (D.pull ι).Gen, t.IsGen →
  ∀ (M : ℕ) (a : ∀ i, Γ(Z, D.U i)),
  (∀ i j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (a i) * ((D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M =
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (a j)) →
  ∃ h : Γ(Y, ⊤), ∀ (i : D.ι) (y : Y) (hy : ι y ∈ D.U i), ∃ u : (Y.presheaf.stalk y)ˣ,
    (Y.presheaf.germ ⊤ y trivial).hom h = (ι.stalkMap y).hom ((Z.presheaf.germ (D.U i) (ι y) hy).hom (a i)) * (u : Y.presheaf.stalk y) := by
  atlas_forward_decl GlobalTheory.DivGlue.glue
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.PropZCore

theorem unitAt_zpow {X : Scheme.{0}} [IsIntegral X] {x : X} {g : X.functionField} (h : UnitAt x g)
    (n : ℤ) : UnitAt x (g ^ n) := by
  have hp : ∀ m : ℕ, UnitAt x (g ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero]; exact unitAt_one x
    | succ m ih => rw [pow_succ]; exact ih.mul h
  rcases n with m | m
  · rw [Int.ofNat_eq_coe, zpow_natCast]; exact hp m
  · rw [zpow_negSucc]; exact (hp _).inv

theorem gen_of_exponent : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D → genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  IsField Γ(reducedSpecialFibre f, ⊤) →
  (∀ (φ : Z.functionField) (x : Z),
    (∀ z : Z, z ⤳ x → IsDiscreteValuationRing (Z.presheaf.stalk z) → RegAt z φ) → RegAt x φ) →
  ∀ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → UnitAt z (τ i : Z.functionField)) →
  ∀ (M : ℕ) (n : ℤ) (x₀ : Z), 1 ≤ M → x₀ ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → IsDiscreteValuationRing (Z.presheaf.stalk z) →
    RegAt z (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  (∀ i : D.ι, x₀ ∈ D.U i → UnitAt x₀ (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  ∃ gen : (lbPow D M).Gen, gen.IsGen ∧
    ∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
      fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n = (τ i : Z.functionField) ^ M := by
  have L1 := GlobalTheory.T.exists_reduced_fibre_point
  have L2 := GlobalTheory.T.exists_global_section_unit_stalk
  intro O _ _ _ ϖ hϖ Z _ f D hD hgen hfield hhart τ hτ hτu M n x₀ hM hx₀ hreg hunit
  set π := f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ) with hπ
  set P : Z.functionField := fnOf ⊤ trivial π with hP
  have hDLB : D.IsLB := hD.2.2.2.2.2.1
  obtain ⟨t, ht⟩ := hD.2.2.2.2.2.2
  obtain ⟨φ, hφ⟩ : ∃ φ : D.ι → Z.functionField, ∀ i, φ i = P ^ n * ((τ i : Z.functionField) ^ M)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hregU : ∀ i, ∀ z ∈ D.U i, RegAt z (φ i) := fun i z hz =>
    hhart _ z fun z' hz' hdvr => hφ i ▸ hreg i z' (hz'.mem_open (D.U i).isOpen hz) hdvr
  have ha : ∀ i, ∃ a : Γ(Z, D.U i), ∀ h, fnOf (D.U i) h a = φ i := by
    intro i
    by_cases h : genericPoint Z ∈ D.U i
    · obtain ⟨a, ha⟩ := exists_fnOf_eq h (hregU i)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose a ha using ha
  have hgne : ∀ i j (h : genericPoint Z ∈ D.U i ⊓ D.U j),
      fnOf _ h (D.g i j : Γ(Z, D.U i ⊓ D.U j)) ≠ 0 := fun i j h =>
    ((D.g i j).isUnit.map (fnOf _ h)).ne_zero
  have hφg : ∀ i j (h : genericPoint Z ∈ D.U i ⊓ D.U j),
      φ i * (fnOf _ h (D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M = φ j := by
    intro i j h
    have e := hτ i j h
    have h1 := hgne i j h
    rw [hφ, hφ, e, mul_pow, mul_inv, mul_comm (((fnOf _ h _) ^ M)⁻¹), mul_assoc, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ h1), mul_one]
  have key : ∀ i j (h : genericPoint Z ∈ D.U i ⊓ D.U j),
      (φ i)⁻¹ = (fnOf _ h (D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M * (φ j)⁻¹ := by
    intro i j h
    rw [← hφg i j h, mul_inv (φ i), mul_left_comm (_ ^ M) (φ i)⁻¹,
      mul_inv_cancel₀ (pow_ne_zero _ (hgne i j h)), mul_one]
  have hcompat : ∀ i j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (a i) *
      ((D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (a j) := by
    intro i j
    apply fn_ext
    intro h
    rw [map_mul, map_pow, fnOf_resG, fnOf_resG, ha, ha, hφg]
  obtain ⟨hh, hhu⟩ := L2 _ _ (reducedSpecialι f) D hDLB t ht M a hcompat
  have germUnit : ∀ i (z : Z) (hz : z ∈ D.U i), UnitAt z (φ i) ↔
      IsUnit ((Z.presheaf.germ (D.U i) z hz).hom (a i)) := by
    intro i z hz
    rw [← ha i (gen_mem hz), unitAt_fnOf_iff hz, Z.mem_basicOpen (a i) z hz]
  obtain ⟨i₀, hi₀⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hDLB x₀
  have hne : hh ≠ 0 := by
    intro h0
    obtain ⟨y₀, rfl⟩ := L1 O ϖ hϖ Z f x₀ hx₀
    obtain ⟨u, hu⟩ := hhu i₀ y₀ hi₀
    have h1 := ((germUnit i₀ _ hi₀).1 (hφ i₀ ▸ hunit i₀ hi₀)).map ((reducedSpecialι f).stalkMap y₀).hom
    have h2 := h1.mul u.isUnit
    rw [← hu, h0, map_zero] at h2
    exact not_isUnit_zero h2
  have hhunit : IsUnit hh := by
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
    exact IsUnit.of_mul_eq_one b hb
  have hspecial : ∀ i (z : Z) (hz : z ∈ D.U i), z ∉ Z.basicOpen π → UnitAt z (φ i) := by
    intro i z hz hzπ
    obtain ⟨y, rfl⟩ := L1 O ϖ hϖ Z f z hzπ
    obtain ⟨u, hu⟩ := hhu i y hz
    have h1 := hhunit.map ((reducedSpecialFibre f).presheaf.germ ⊤ y trivial).hom
    rw [hu] at h1
    have h2 := h1.mul (u⁻¹).isUnit
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at h2
    have : IsLocalHom ((reducedSpecialι f).stalkMap y).hom := inferInstance
    exact (germUnit i _ hz).2 (isUnit_of_map_unit _ _ h2)
  have hgenU : UnitAt (genericPoint Z) P := (unitAt_fnOf_iff (U := ⊤) trivial trivial π).2 hgen
  have hPne : P ≠ 0 := hgenU.ne_zero
  have hall : ∀ i, ∀ z ∈ D.U i, UnitAt z (φ i)⁻¹ := by
    intro i z hz
    refine UnitAt.inv ?_
    by_cases hzπ : z ∈ Z.basicOpen π
    · have h3 := unitAt_zpow (hτu i z hz hzπ) M
      rw [zpow_natCast] at h3
      rw [hφ]
      exact (unitAt_zpow ((unitAt_fnOf_iff (U := ⊤) trivial trivial π).2 hzπ) n).mul h3.inv
    · exact hspecial i z hz hzπ
  choose u hu using fun i => exists_unit_fnOf_eq (hall i)
  refine ⟨⟨u⟩, fun i j => ?_, fun i h => ?_⟩
  · apply Units.ext
    apply fn_ext
    intro h
    have h' : genericPoint Z ∈ D.U i ⊓ D.U j := h
    change fnOf (D.U i ⊓ D.U j) h' ((res (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (u i) : Γ(Z, D.U i ⊓ D.U j)ˣ) : Γ(Z, D.U i ⊓ D.U j)) =
      fnOf (D.U i ⊓ D.U j) h' (((D.g i j ^ M) * res (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (u j) : Γ(Z, D.U i ⊓ D.U j)ˣ) : Γ(Z, D.U i ⊓ D.U j))
    rw [Units.val_mul, Units.val_pow_eq_pow_val, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, map_mul, map_pow]
    erw [fnOf_resG, fnOf_resG, hu, hu]
    exact key i j h'
  · change fnOf _ h (u i : Γ(Z, D.U i)) * P ^ n = _
    rw [hu, hφ, mul_inv, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hPne), one_mul]

end GlobalTheory.PropZCore
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_extends_over_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D → genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  IsField Γ(reducedSpecialFibre f, ⊤) →
  (∀ (φ : Z.functionField) (x : Z),
    (∀ z : Z, z ⤳ x → IsDiscreteValuationRing (Z.presheaf.stalk z) → RegAt z φ) → RegAt x φ) →
  ∀ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → UnitAt z (τ i : Z.functionField)) →
  ∀ (M : ℕ) (n : ℤ) (x₀ : Z), 1 ≤ M → x₀ ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → IsDiscreteValuationRing (Z.presheaf.stalk z) →
    RegAt z (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  (∀ i : D.ι, x₀ ∈ D.U i → UnitAt x₀ (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  ∃ gen : (lbPow D M).Gen, gen.IsGen ∧
    ∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
      fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n = (τ i : Z.functionField) ^ M := by
  atlas_forward_decl GlobalTheory.PropZCore.gen_of_exponent
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.PropZRow

theorem propZ : PropZ := by
  intro O _ _ _ ϖ hϖ Z f D hD sig hs
  obtain ⟨hI, hN, hP, hF, hC, hL, ht⟩ := hD
  haveI := hI
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace f).mp inferInstance
  have hD : Hyp f D := ⟨hI, hN, hP, hF, hC, hL, ht⟩
  obtain ⟨τ, hτ, hU, hPow⟩ := GlobalTheory.T.exists_ratSec_unit_generic_fibre O ϖ hϖ Z f D hF hL sig hs
  obtain ⟨hg, hz⟩ := GlobalTheory.T.flat_scheme_special_fibre_nonempty O ϖ hϖ Z f hF (hC.toNonempty)
  obtain ⟨M, n, x₀, hM, hx₀, hreg, hunit⟩ := GlobalTheory.T.exists_power_section_special_fibre Z hN _ hg hz D τ hL hτ hU
  obtain ⟨gen, hgen, heq⟩ := GlobalTheory.T.regular_section_extends_over_fibre O ϖ hϖ Z f D hD hg (GlobalTheory.T.reduced_special_fibre_global_field O Z f hP hC) (GlobalTheory.T.regular_of_regular_at_codim_one Z hN) τ hτ hU M n x₀ hM hx₀ hreg hunit
  exact ⟨M, n, hM, ⟨gen, hgen, hPow M n gen heq⟩, GlobalTheory.T.valuation_constant_of_power_eq O ϖ hϖ Z f D hL sig hs M n gen hM hgen (hPow M n gen heq)⟩

end GlobalTheory.PropZRow
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prop_z_statement : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ := by
  first | exact @GlobalTheory.PropZRow.propZ | exact GlobalTheory.PropZRow.propZ | (intros; apply GlobalTheory.PropZRow.propZ <;> assumption)
end
