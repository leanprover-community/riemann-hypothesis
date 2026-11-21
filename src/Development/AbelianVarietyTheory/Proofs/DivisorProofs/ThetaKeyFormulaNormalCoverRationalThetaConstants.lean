import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfSmallTraits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMapOfModelHasDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPropeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingElementarySymmetricUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelSemiAbelianRelDimCotangentVectorBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionThetaQuotientProjChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesianStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoords_in_standardChart_ratio : ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (a : Fin (n + 1)), PCrd x v → ⊤ ≤ x ⁻¹ᵁ ProjSpace.chart o n a → v a ≠ 0 ∧ ∀ b, valR x (ProjSpace.chart o n a) (ProjSpace.ratio o n a b) = v b / v a := by
  first | exact @GlobalTheory.UMin.CrdChart.pCrd_chart | exact GlobalTheory.UMin.CrdChart.pCrd_chart | (intros; apply GlobalTheory.UMin.CrdChart.pCrd_chart <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (A : Subalgebra k Ω) [IsLocalRing A] (N : ℕ) (c : Fin N → Ω) (a j : Fin N), c a ≠ 0 → (∀ b, c b / c a ∈ A) → symTup c j ≠ 0 → (∀ b, symTup c b / symTup c j ∈ A) → symTup c j / c a ^ N.factorial ≠ 0 ∧ symTup c j / c a ^ N.factorial ∈ A ∧ (symTup c j / c a ^ N.factorial)⁻¹ ∈ A := by
  intro k Ω _ _ _ A _ N c a j hca hcb hj hjb
  have hpow : c a ^ N.factorial ≠ 0 := pow_ne_zero _ hca
  let d : Fin N → A := fun b => ⟨c b / c a, hcb b⟩
  have hd : ∀ j' : Fin N, symTup c j' / c a ^ N.factorial = ((symTup d j' : A) : Ω) := by
    intro j'
    have h1 : c = fun b => c a * ((d b : A) : Ω) := by
      funext b; show c b = c a * (c b / c a); field_simp
    have h2 := (GlobalTheory.UMin.symTup_basic).1 Ω N (fun b => ((d b : A) : Ω)) (c a) j'
    have h3 := (GlobalTheory.UMin.symTup_basic).2.2.1 A Ω A.val.toRingHom N d j'
    have h4 : symTup c j' = c a ^ N.factorial * symTup (fun b => ((d b : A) : Ω)) j' := by
      rw [← h2, ← h1]
    rw [h4, mul_div_cancel_left₀ _ hpow]
    exact h3.symm
  have hda : d a = 1 := Subtype.ext (by show c a / c a = 1; exact div_self hca)
  obtain ⟨k0, hk1, hk2, hku⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one A (Fin N) d a hda
  rw [Fintype.card_fin] at hk2
  let j' : Fin N := ⟨k0 - 1, by omega⟩
  have hk0 : (j' : ℕ) + 1 = k0 := by show k0 - 1 + 1 = k0; omega
  have hu : IsUnit (symTup d j') := by
    unfold symTup; rw [hk0]; exact hku.pow _
  let x : A := ⟨symTup c j / c a ^ N.factorial, by rw [hd j]; exact (symTup d j).2⟩
  let z : A := ⟨symTup c j' / symTup c j, hjb j'⟩
  have hxz : symTup d j' = x * z := by
    apply Subtype.ext
    show ((symTup d j' : A) : Ω) = (symTup c j / c a ^ N.factorial) * (symTup c j' / symTup c j)
    rw [← hd j']
    field_simp
  rw [hxz] at hu
  have hx : IsUnit x := isUnit_of_mul_isUnit_left hu
  refine ⟨div_ne_zero hj hpow, x.2, ?_⟩
  obtain ⟨v, hv⟩ := hx.exists_right_inv
  have hv' : (symTup c j / c a ^ N.factorial) * (v : Ω) = 1 := by
    have := congrArg (fun t : A => (t : Ω)) hv
    simpa using this
  rw [← eq_inv_of_mul_eq_one_right hv']
  exact v.2
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSymmetricFunctions_div_pow_factorial_isUnit : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (A : Subalgebra k Ω) [IsLocalRing A] (N : ℕ) (c : Fin N → Ω) (a j : Fin N), c a ≠ 0 → (∀ b, c b / c a ∈ A) → symTup c j ≠ 0 → (∀ b, symTup c b / symTup c j ∈ A) → symTup c j / c a ^ N.factorial ≠ 0 ∧ symTup c j / c a ^ N.factorial ∈ A ∧ (symTup c j / c a ^ N.factorial)⁻¹ ∈ A := by
  atlas_forward_decl GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdSym

open GlobalTheory.Points GlobalTheory.ProjSpace

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω]

theorem div_mem_O {o : Type} [CommRing o] {M : RatModel k Ω} {n : ℕ} {h : M.Z ⟶ PSpace o n}
    {c : Fin (n + 1) → Ω} (hc : PCrd (M.pt ≫ h) c) {a : Fin (n + 1)} {z : M.Z}
    (hz : z ∈ h ⁻¹ᵁ ProjSpace.chart o n a) : c a ≠ 0 ∧ ∀ b, c b / c a ∈ M.O z := by
  have hW : ⊤ ≤ M.pt ⁻¹ᵁ (h ⁻¹ᵁ ProjSpace.chart o n a) := M.top_le_preimage_pt ⟨z, hz⟩
  obtain ⟨h0, hv⟩ := GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o Ω n (M.pt ≫ h) c a hc (le_preimage_comp M.pt h le_rfl hW)
  refine ⟨h0, fun b => ?_⟩
  have e : valF M.pt (h ⁻¹ᵁ ProjSpace.chart o n a) (ProjSpace.pullRatio h _ a le_rfl b) = c b / c a :=
    (Points.valR_appLE M.pt h le_rfl hW _).trans (hv b)
  exact e ▸ M.valF_mem_O hz _

theorem valR_pullO1_g {L : Type} [Field L] {X : Scheme.{0}} {o : Type} [CommRing o] {r : ℕ} (y0 : Sp L ⟶ X)
    (π : X ⟶ PSpace o r) {t : Fin (r + 1) → L} (ht : PCrd (y0 ≫ π) t) (i j : PUnit → Fin (r + 1))
    (h : ⊤ ≤ y0 ⁻¹ᵁ (((ProjSpace.O1 o r).pull π).U i ⊓ ((ProjSpace.O1 o r).pull π).U j)) :
    valR y0 _ (((ProjSpace.O1 o r).pull π).g i j).val = t (j PUnit.unit) / t (i PUnit.unit) := by
  have h1 : ⊤ ≤ (y0 ≫ π) ⁻¹ᵁ (ProjSpace.chart o r (i PUnit.unit) ⊓ ProjSpace.chart o r (j PUnit.unit)) :=
    le_preimage_comp y0 π (inf_le_inf (LB.wchart_le (ProjSpace.O1 o r) (fun _ => π) i PUnit.unit)
      (LB.wchart_le (ProjSpace.O1 o r) (fun _ => π) j PUnit.unit)) h
  refine (TuplePoint.valR_linComb_g y0 (ProjSpace.O1 o r) π 1 i j h).trans ((zpow_one _).trans ?_)
  refine (valR_res (y0 ≫ π) inf_le_left h1 (ProjSpace.ratio o r (i PUnit.unit) (j PUnit.unit))).trans ?_
  exact (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o L r (y0 ≫ π) t _ ht (le_preimage_mono _ inf_le_left h1)).2 _

open Classical in

def unitOf (M : RatModel k Ω) (U : M.Z.Opens) (x : Ω) (hx : ∀ z ∈ U, x ≠ 0 ∧ x ∈ M.O z ∧ x⁻¹ ∈ M.O z) :
    Γ(M.Z, U)ˣ :=
  if hU : (U : Set M.Z).Nonempty then
    Units.map (M.sectionsEquiv U hU).symm.toMonoidHom
      ⟨⟨x, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.1⟩, ⟨x⁻¹, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.2⟩,
        Subtype.ext (mul_inv_cancel₀ (hx _ hU.some_mem).1), Subtype.ext (inv_mul_cancel₀ (hx _ hU.some_mem).1)⟩
  else 1

theorem valR_unitOf {M : RatModel k Ω} {U : M.Z.Opens} {x : Ω} {hx : ∀ z ∈ U, x ≠ 0 ∧ x ∈ M.O z ∧ x⁻¹ ∈ M.O z}
    (h : ⊤ ≤ M.pt ⁻¹ᵁ U) : valR M.pt U (unitOf M U x hx).val = x := by
  have hU : (U : Set M.Z).Nonempty := ⟨_, h (x := IsLocalRing.closedPoint Ω) trivial⟩
  rw [unitOf, dif_pos hU]
  have := M.coe_sectionsEquiv U hU ((M.sectionsEquiv U hU).symm ⟨x, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.1⟩)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.UMin.CrdSym
end

namespace GlobalTheory.UMin.CrdSym
open GlobalTheory.Points GlobalTheory.ProjSpace

theorem lbIso_symTup : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (h : M.Z ⟶ PSpace k n) (g : M.Z ⟶ PSpace o n) (c : Fin (n + 1) → Ω), PCrd (M.pt ≫ h) c → PCrd (M.pt ≫ g) (symTup c) → LBIso ((ProjSpace.O1 o n).pull g) (lbPow ((ProjSpace.O1 k n).pull h) (n + 1).factorial) := by
  intro k Ω o _ _ _ _ M n h g c hc he
  set D := (n + 1).factorial
  set L := (ProjSpace.O1 o n).pull g
  set L' := lbPow ((ProjSpace.O1 k n).pull h) D
  have h2 : ∀ a : L'.ι, L'.U a ≤ ((ProjSpace.O1 k n).pull h).U (a PUnit.unit) := fun a =>
    LB.wchart_le ((ProjSpace.O1 k n).pull h) (fun _ => 𝟙 M.Z) a PUnit.unit
  have hL' : ∀ a : L'.ι, L'.U a ≤ h ⁻¹ᵁ ProjSpace.chart k n (a PUnit.unit PUnit.unit) := fun a =>
    (h2 a).trans (LB.wchart_le (ProjSpace.O1 k n) (fun _ => h) _ PUnit.unit)
  have hL : ∀ j : L.ι, L.U j ≤ g ⁻¹ᵁ ProjSpace.chart o n (j PUnit.unit) := fun j =>
    LB.wchart_le (ProjSpace.O1 o n) (fun _ => g) j PUnit.unit
  let x : L'.ι × L.ι → Ω := fun p => symTup c (p.2 PUnit.unit) / c (p.1 PUnit.unit PUnit.unit) ^ D
  have hx : ∀ p : L'.ι × L.ι, ∀ z ∈ (LB.div L' L).U p, x p ≠ 0 ∧ x p ∈ M.O z ∧ (x p)⁻¹ ∈ M.O z := by
    rintro ⟨a, j⟩ z ⟨hza, hzj⟩
    obtain ⟨h1, h3⟩ := div_mem_O hc (hL' a hza)
    obtain ⟨h4, h5⟩ := div_mem_O he (hL j hzj)
    exact GlobalTheory.T.thetaSymmetricFunctions_div_pow_factorial_isUnit k Ω (M.O z) (n + 1) c _ _ h1 h3 h4 h5
  have nzh : ∀ a : L'.ι, ⊤ ≤ M.pt ⁻¹ᵁ L'.U a → c (a PUnit.unit PUnit.unit) ≠ 0 := fun a ha =>
    (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio k Ω n (M.pt ≫ h) c _ hc (le_preimage_comp M.pt h (hL' a) ha)).1
  have nzg : ∀ j : L.ι, ⊤ ≤ M.pt ⁻¹ᵁ L.U j → symTup c (j PUnit.unit) ≠ 0 := fun j hj =>
    (GlobalTheory.T.homogeneousCoords_in_standardChart_ratio o Ω n (M.pt ≫ g) (symTup c) _ he (le_preimage_comp M.pt g (hL j) hj)).1
  let w : LB.Iso L L' := ⟨fun p => unitOf M ((LB.div L' L).U p) (x p) (hx p)⟩
  refine ⟨w, ?_⟩
  rintro ⟨a, j⟩ ⟨a', j'⟩
  refine Units.ext (TuplePoint.ext_of_dense M.pt fun hW => ?_)
  have ha := le_preimage_mono M.pt inf_le_left hW
  have hb := le_preimage_mono M.pt inf_le_right hW
  have hk : ⊤ ≤ M.pt ⁻¹ᵁ (L'.U a ⊓ L'.U a') :=
    le_preimage_mono M.pt (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) hW
  have hj : ⊤ ≤ M.pt ⁻¹ᵁ (L.U j ⊓ L.U j') :=
    le_preimage_mono M.pt (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) hW
  have e1 := TuplePoint.valR_linComb_g M.pt ((ProjSpace.O1 k n).pull h) (𝟙 M.Z) D a a' hk
  rw [Category.comp_id, valR_pullO1_g M.pt h hc _ _ (le_preimage_mono M.pt (inf_le_inf (h2 a) (h2 a')) hk),
    zpow_natCast] at e1
  have e2 := valR_pullO1_g M.pt g he j j' hj
  have n1 := nzh a (le_preimage_mono M.pt inf_le_left ha)
  have n2 := nzh a' (le_preimage_mono M.pt inf_le_left hb)
  have n3 := nzg j (le_preimage_mono M.pt inf_le_right ha)
  have n4 := nzg j' (le_preimage_mono M.pt inf_le_right hb)
  refine (TuplePoint.valR_res_unit M.pt _ hW _).trans ((valR_unitOf (hx := hx (a, j)) ha).trans (Eq.symm ?_))
  refine (TuplePoint.valR_mul_unit M.pt hW _ _).trans ?_
  have eg : valR M.pt _ ((LB.div L' L).g (a, j) (a', j')).val =
      (c (a' PUnit.unit PUnit.unit) / c (a PUnit.unit PUnit.unit)) ^ D *
        (symTup c (j' PUnit.unit) / symTup c (j PUnit.unit))⁻¹ := by
    refine (TuplePoint.valR_mul_unit M.pt hW _ _).trans ?_
    exact congrArg₂ (· * ·) ((TuplePoint.valR_res_unit M.pt _ hW _).trans e1)
      ((TuplePoint.valR_inv_unit M.pt hW _).trans (congrArg (·⁻¹) ((TuplePoint.valR_res_unit M.pt _ hW _).trans e2)))
  rw [eg, TuplePoint.valR_res_unit M.pt _ hW, valR_unitOf (hx := hx (a', j')) hb]
  simp only [x]
  rw [div_pow]
  field_simp

end GlobalTheory.UMin.CrdSym
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_coordinates_O1_factorial_power : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (h : M.Z ⟶ PSpace k n) (g : M.Z ⟶ PSpace o n) (c : Fin (n + 1) → Ω), PCrd (M.pt ≫ h) c → PCrd (M.pt ≫ g) (symTup c) → LBIso ((ProjSpace.O1 o n).pull g) (lbPow ((ProjSpace.O1 k n).pull h) (n + 1).factorial) := by
  atlas_forward_decl GlobalTheory.UMin.CrdSym.lbIso_symTup
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianLocus_eq_preimage_moduli_and_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : Scheme.{0}) (π : T ⟶ Y.X) (t : SAB H T), Nonempty (SABMap t Y.t π) → abLocus t.G = π ⁻¹' Set.range Y.j ∧ IsOpen (abLocus t.G) ∧ ∀ W : T.Opens, (W : Set T) ⊆ abLocus t.G → RelAmple ((Over.pullback W.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom W.ι)) := by
  first | exact @GlobalTheory.ModelAbLocus.abLocus_eq_and_pol | exact GlobalTheory.ModelAbLocus.abLocus_eq_and_pol | (intros; apply GlobalTheory.ModelAbLocus.abLocus_eq_and_pol <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThBdl

theorem resG_resG_glue {X : Scheme.{0}} {A B C : X.Opens} (h : B ≤ A) (h' : C ≤ B) (f : Γ(X, A)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem locSec_glue : ∀ (S : Scheme.{0}) (G : Over S) (L : LB G.left) (V : S.Opens) (κ : Type) (N : κ → S.Opens)
    (s : ∀ k, LocSec G L (N k)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V → (∀ k, IsLocSec (s k)) →
    (∀ k k' i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k) (s k i) =
      resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k') (s k' i)) →
    ∃ s' : LocSec G L V, IsLocSec s' ∧ ∀ k i,
      resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i := by
  intro S G L V κ N s hN hV hs hc
  have hmem : ∀ x : G.left, G.hom.base x ∈ V → ∃ k, G.hom.base x ∈ N k := by
    intro x hx
    have : G.hom.base x ∈ (⨆ k, N k) := by rw [hV]; exact hx
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hcov : ∀ i, L.U i ⊓ G.hom ⁻¹ᵁ V ≤ ⨆ k, (L.U i ⊓ G.hom ⁻¹ᵁ N k) := by
    intro i x hx
    obtain ⟨k, hk⟩ := hmem x hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩
  have hWV : ∀ i k, L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V := fun i k _ hx => ⟨hx.1, hN k hx.2⟩
  have hglue : ∀ i, ∃! t : Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ V), ∀ k, resG _ (hWV i k) t = s k i := by
    intro i
    refine G.left.sheaf.existsUnique_gluing' (fun k => L.U i ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ G.hom ⁻¹ᵁ V)
      (fun k => homOfLE (hWV i k)) (hcov i) (fun k => s k i) ?_
    intro k k'
    have hle : (L.U i ⊓ G.hom ⁻¹ᵁ N k) ⊓ (L.U i ⊓ G.hom ⁻¹ᵁ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') :=
      fun _ hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩
    have e := congrArg (resG _ hle) (hc k k' i)
    exact (resG_resG_glue _ _ _).symm.trans (e.trans (resG_resG_glue _ _ _))
  choose s' hs' _ using hglue
  refine ⟨s', ?_, fun k i => hs' i k⟩
  intro i j
  have hTV : ∀ k, L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V := fun k _ hx => ⟨hx.1, hN k hx.2⟩
  refine G.left.sheaf.eq_of_locally_eq' (fun k => L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V)
    (fun k => homOfLE (hTV k)) ?_ _ _ ?_
  · intro x hx
    obtain ⟨k, hk⟩ := hmem x hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩
  · intro k
    have hi1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k := fun _ hx => ⟨hx.1.1, hx.2⟩
    have hj1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U j ⊓ G.hom ⁻¹ᵁ N k := fun _ hx => ⟨hx.1.2, hx.2⟩
    have e1 : resG _ (hi1.trans (hWV i k)) (s' i) = resG _ hi1 (s k i) := by
      rw [← hs' i k, resG_resG_glue]
    have e2 : resG _ (hj1.trans (hWV j k)) (s' j) = resG _ hj1 (s k j) := by
      rw [← hs' j k, resG_resG_glue]
    change resG _ (hTV k) (resG _ _ (s' i)) =
      resG _ (hTV k) (resG _ _ (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) * resG _ _ (s' j))
    rw [map_mul]
    refine ((resG_resG_glue _ _ _).trans e1).trans ((hs k i j).trans ?_)
    congr 1
    · exact (resG_resG_glue _ _ _).symm
    · exact ((resG_resG_glue _ _ _).trans e2).symm

end GlobalTheory.UMin.ThBdl
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glued_lineBundleSection_over_cover : ∀ (S : Scheme.{0}) (G : Over S) (L : LB G.left) (V : S.Opens) (κ : Type) (N : κ → S.Opens)
    (s : ∀ k, LocSec G L (N k)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V → (∀ k, IsLocSec (s k)) →
    (∀ k k' i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k) (s k i) =
      resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k') (s k' i)) →
    ∃ s' : LocSec G L V, IsLocSec s' ∧ ∀ k i,
      resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i := by
  atlas_forward_decl GlobalTheory.UMin.ThBdl.locSec_glue
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

theorem genPt_dom {S : Scheme.{0}} [IsIntegral S] {K : Type} [Field K] (ξ : Sp K ⟶ S)
    (hξ : Set.range ξ = {genericPoint S}) : QuasiCompact ξ ∧ IsSchemeTheoreticallyDominant ξ := by
  have hd : IsDominant ξ := ⟨by
    show Dense (Set.range ξ)
    rw [hξ]
    exact dense_iff_closure_eq.2 (genericPoint_spec S)⟩
  refine ⟨⟨fun U _ _ => (Set.subsingleton_of_subsingleton).isCompact⟩, ?_⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant ξ

theorem app_snd_injective {S : Scheme.{0}} [IsIntegral S] (G : Over S) [Flat G.hom] {K : Type} [Field K]
    (ξ : Sp K ⟶ S) (hξ : Set.range ξ = {genericPoint S}) (O : G.left.Opens) :
    Function.Injective ((snd (Over.mk ξ) G).left.app O).hom := by
  obtain ⟨_, _⟩ := genPt_dom ξ hξ
  have hP : IsPullback (fst (Over.mk ξ) G).left (snd (Over.mk ξ) G).left ξ G.hom := .of_hasPullback _ _
  have : IsSchemeTheoreticallyDominant (snd (Over.mk ξ) G).left := IsSchemeTheoreticallyDominant.of_isPullback hP
  have : QuasiCompact (snd (Over.mk ξ) G).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hP inferInstance
  exact (snd (Over.mk ξ) G).left.app_injective O

theorem locSec_eq_of_genIs : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S), Set.range ξ = {genericPoint S} →
    ∀ (N N' : S.Opens) (s : LocSec G L N) (s' : LocSec G L N') (v : SecM G L 1 (Over.mk ξ)),
      GenIs ξ s v → GenIs ξ s' v → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i) := by
  intro S _ G _ _ hG L K _ ξ hξ N N' s s' v ⟨h₁, e₁⟩ ⟨h₂, e₂⟩ i
  have := hG.smooth
  have hfl : Flat G.hom := inferInstance
  have e := congrFun (e₁.trans e₂.symm) (fun _ => i)
  have h₃ : Set.range ξ ⊆ ((N ⊓ N' : S.Opens) : Set S) := fun x hx => ⟨h₁ hx, h₂ hx⟩
  set O : G.left.Opens := L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') with hO
  set W : (Over.mk ξ ⊗ G).left.Opens := (LPow G L 1 (Over.mk ξ)).U (fun _ => i) with hW
  have hle : W ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ O := lpow_U_le h₃ (fun _ => i)
  have hge : (snd (Over.mk ξ) G).left ⁻¹ᵁ O ≤ W := fun y hy => Set.mem_iInter.2 fun _ => hy.1
  have hinj : Function.Injective ((snd (Over.mk ξ) G).left.appLE O W hle).hom := by
    have hEq : W = (snd (Over.mk ξ) G).left ⁻¹ᵁ O := le_antisymm hle hge
    clear_value W
    subst hEq
    rw [← Scheme.Hom.app_eq_appLE]
    exact app_snd_injective G ξ hξ O
  apply hinj
  have k₁ : ((snd (Over.mk ξ) G).left.appLE O W hle).hom
      (resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : O ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i)) = genPull h₁ s (fun _ => i) := by
    dsimp only [resG]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have k₂ : ((snd (Over.mk ξ) G).left.appLE O W hle).hom
      (resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : O ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) = genPull h₂ s' (fun _ => i) := by
    dsimp only [resG]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  exact k₁.trans (e.trans k₂.symm)

end GlobalTheory.UMin.ThBdl
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleLocalSection_eq_of_generic_fibre : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S), Set.range ξ = {genericPoint S} →
    ∀ (N N' : S.Opens) (s : LocSec G L N) (s' : LocSec G L N') (v : SecM G L 1 (Over.mk ξ)),
      GenIs ξ s v → GenIs ξ s' v → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i) := by
  atlas_forward_decl GlobalTheory.UMin.ThBdl.locSec_eq_of_genIs
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl.Glued

theorem valF_resG {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) {U W : X.Opens} (h : W ≤ U) (f : Γ(X, U))
    (hy : ⊤ ≤ y ⁻¹ᵁ W) : valF y W (resG X h f) = valF y U f := by
  have hU : ⊤ ≤ y ⁻¹ᵁ U := fun a ha => h (hy ha)
  unfold valF
  rw [dif_pos hy, dif_pos hU]
  congr 1
  show (X.presheaf.map (homOfLE h).op ≫ y.appLE W ⊤ hy).hom f = _
  rw [Scheme.Hom.map_appLE]

theorem glued : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S)
    (V : S.Opens) (κ : Type) (N : κ → S.Opens) (s : ∀ k, LocSec G L (N k)) (s' : LocSec G L V)
    (v : SecM G L 1 (Over.mk ξ)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V →
    (∀ k i, resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i) →
    (∀ k, GenIs ξ (s k) v) → (∀ k, FibNz (s k) (N k)) → (Nonempty κ → GenIs ξ s' v) ∧ FibNz s' V := by
  intro S G _ L K _ ξ V κ N s s' v hN hsup hres hgen hnz
  refine ⟨fun ⟨k⟩ => ?_, ?_⟩
  · obtain ⟨hξk, hk⟩ := hgen k
    refine ⟨hξk.trans (hN k), ?_⟩
    rw [← hk]
    funext j
    unfold genPull
    rw [← hres k (j 0)]
    show _ = (G.left.presheaf.map _ ≫ (snd (Over.mk ξ) G).left.appLE _ _ _).hom (s' (j 0))
    rw [Scheme.Hom.map_appLE]
  · intro K' _ _ x hx
    obtain ⟨p⟩ : Nonempty (Sp K') := inferInstance
    have hp : x p ∈ (⨆ k, N k : S.Opens) := hsup ▸ hx ⟨p, rfl⟩
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
    have hxk : Set.range x ⊆ N k := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q p]
      exact hk
    obtain ⟨y, i, hyx, hyr, hval⟩ := hnz k K' x hxk
    refine ⟨y, i, hyx, fun z hz => ⟨(hyr hz).1, hN k (hyr hz).2⟩, ?_⟩
    rw [← hres k i] at hval
    convert hval using 1
    exact (valF_resG y _ (s' i) ((GlobalTheory.ZH.top_le_preimage_iff _ _).2 hyr)).symm

end GlobalTheory.UMin.ThBdl.Glued
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_section_generic_value_nonvanishing : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S)
    (V : S.Opens) (κ : Type) (N : κ → S.Opens) (s : ∀ k, LocSec G L (N k)) (s' : LocSec G L V)
    (v : SecM G L 1 (Over.mk ξ)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V →
    (∀ k i, resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i) →
    (∀ k, GenIs ξ (s k) v) → (∀ k, FibNz (s k) (N k)) → (Nonempty κ → GenIs ξ s' v) ∧ FibNz s' V := by
  atlas_forward_decl GlobalTheory.UMin.ThBdl.Glued.glued
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

theorem cross_resG_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} {V W : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (s : Γ(Y, U)) :
    resG X h ((f.appLE U V e).hom s) = (f.appLE U W (h.trans e)).hom s := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

theorem cross_resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (s : Γ(X, U)) :
    resG X h2 (resG X h1 s) = resG X (h2.trans h1) s := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom _ = _
  rw [← Functor.map_comp]
  rfl

theorem cross_resG_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (s : Γ(X, U)) : resG X h s = s := by
  change (X.presheaf.map (𝟙 _)).hom s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem cross_appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : U ≤ U') (s : Γ(Y, U')) :
    (f.appLE U V e).hom (resG Y h s) = (f.appLE U' V (e.trans fun _ hx => h hx)).hom s := by
  rw [← Scheme.Hom.map_appLE f e (homOfLE h).op]
  rfl

theorem cross_ratio_val {k Ω : Type} [CommRing k] [Field Ω] {n : ℕ} {x : Sp Ω ⟶ PSpace k n}
    {c : Fin (n + 1) → Ω} (hc : PCrd x c) {U : (PSpace k n).Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) {a : Fin (n + 1)}
    (ha : U ≤ chart k n a) :
    c a ≠ 0 ∧ ∀ b, (x.appLE U ⊤ hU).hom (ratioOn U a ha b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b * (c a)⁻¹) := by
  obtain ⟨τ, -, H⟩ := hc
  have h1 : ((O1 k n).pull x).U (fun _ => a) ≤ x ⁻¹ᵁ (O1 k n).U a :=
    LB.wchart_le (O1 k n) (fun _ => x) (fun _ => a) PUnit.unit
  have h2 : ⊤ ≤ ((O1 k n).pull x).U (fun _ => a) :=
    fun y hy => Set.mem_iInter.2 fun _ => ha (hU hy)
  set t : Γ(Sp Ω, ⊤) := resG _ h2 (τ.s (fun _ => a)).val with ht
  have key : ∀ b, (x.appLE U ⊤ hU).hom (ratioOn U a ha b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b) * t := by
    intro b
    have e := congrArg (resG _ h2) (H b (fun _ => a) h1)
    rw [map_mul, cross_resG_appLE] at e
    have e2 : ratioOn U a ha b = resG _ ha (ratio k n a b) := rfl
    rw [e2, cross_appLE_resG]
    refine e.trans (congrArg (· * t) ?_)
    exact (cross_resG_resG _ _ _).trans (cross_resG_self _ _)
  have ka := key a
  rw [ratioOn_self, map_one] at ka
  have hne : c a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at ka
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ka
    rw [map_one, map_zero] at this
    exact one_ne_zero (α := Ω) this
  refine ⟨hne, fun b => ?_⟩
  rw [key, map_mul]
  congr 1
  have : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ *
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a) = 1 := by
    rw [← map_mul]
    exact (congrArg _ (inv_mul_cancel₀ hne)).trans (map_one _)
  calc t = (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ *
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a) * t) := by rw [← _root_.mul_assoc, this, _root_.one_mul]
    _ = _ := by rw [← ka, _root_.mul_one]

theorem cross_pull_base {S : Scheme.{0}} (G : Over S) [GrpObj G] {K : Type} [Field K] (ξ : Sp K ⟶ S)
    {N : S.Opens} (hN : ⊤ ≤ ξ ⁻¹ᵁ N) {V : G.left.Opens} (hV : V ≤ G.hom ⁻¹ᵁ N) {W : (Over.mk ξ ⊗ G).left.Opens}
    (hW : W ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ V) (r : Γ(S, N)) :
    ((snd (Over.mk ξ) G).left.appLE V W hW).hom (resG _ hV ((G.hom.app N).hom r)) =
      liftHom G (T := Over.mk ξ) W ((ξ.appLE N ⊤ hN).hom r) := by
  have e : (snd (Over.mk ξ) G).left ≫ G.hom = (fst (Over.mk ξ) G).left ≫ ξ :=
    (Over.w (snd (Over.mk ξ) G)).trans (Over.w (fst (Over.mk ξ) G)).symm
  have e1 : ((snd (Over.mk ξ) G).left.appLE V W hW).hom (resG _ hV ((G.hom.app N).hom r)) =
      (G.hom.appLE N V hV ≫ (snd (Over.mk ξ) G).left.appLE V W hW).hom r := rfl
  have e2 : liftHom G (T := Over.mk ξ) W ((ξ.appLE N ⊤ hN).hom r) =
      (ξ.appLE N ⊤ hN ≫ (fst (Over.mk ξ) G).left.appLE ⊤ W le_top).hom r := rfl
  rw [e1, e2, Scheme.Hom.appLE_comp_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  simp only [e]

theorem cross_ratio_sections : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (G : Over M.Z) [GrpObj G]
    (L : LB G.left) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (v : SecM G L 1 (Over.mk M.pt)),
    PCrd (M.pt ≫ h) c →
    (∀ (N N' : M.Z.Opens) (s : LocSec G L N) (s' : LocSec G L N') (w : SecM G L 1 (Over.mk M.pt)),
      GenIs M.pt s w → GenIs M.pt s' w → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) →
    ∀ (a b : Fin (n + 1)) (sa : LocSec G L (h ⁻¹ᵁ chart k n a)) (sb : LocSec G L (h ⁻¹ᵁ chart k n b)),
      (((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sa ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v)) →
      (((h ⁻¹ᵁ chart k n b : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sb ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b)⁻¹ • v)) →
      ∀ i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a)) (sa i) =
        resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i) := by
  intro k Ω _ _ _ M G _ L n c h v hc huniq a b sa sb ha hb i
  by_cases hne : ((h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) : Set M.Z).Nonempty
  swap
  · have hbot : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) = ⊥ :=
      eq_bot_iff.2 fun y hy => hne ⟨_, hy.2⟩
    have : Subsingleton Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b))) := by
      rw [hbot]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨ha1, ha2⟩ := ha (hne.mono fun _ hx => hx.1)
  obtain ⟨hb1, hb2⟩ := hb (hne.mono fun _ hx => hx.2)
  have htop := M.top_le_preimage_pt hne
  have hr : Set.range M.pt ⊆ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) :=
    (top_le_preimage_iff _ _).1 htop
  have htop' : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ (chart k n a ⊓ chart k n b) := htop
  obtain ⟨hca, hra⟩ := cross_ratio_val hc htop' inf_le_left
  obtain ⟨hcb, -⟩ := cross_ratio_val hc htop' inf_le_right
  let s₂ : LocSec G L (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) := fun i =>
    resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i)
  have g₂ : GenIs M.pt s₂ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v) := by
    refine ⟨hr, funext fun j => ?_⟩
    have e3 := congrFun hb2 j
    simp only [genPull, s₂] at e3 ⊢
    rw [map_mul, cross_pull_base G M.pt htop]
    refine (congrArg (_ * ·) ((cross_appLE_resG _ _ _ _).trans e3)).trans ?_
    have e4 : (M.pt.appLE _ ⊤ htop).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b)) =
        ((M.pt ≫ h).appLE _ ⊤ htop').hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b) := by
      rw [Scheme.Hom.comp_appLE]
      rfl
    rw [e4, hra]
    change liftHom G _ _ * (liftHom G _ _ * v.1 j) = liftHom G _ _ * v.1 j
    rw [← _root_.mul_assoc, ← map_mul]
    congr 2
    erw [← map_mul]
    congr 1
    change c b * (c a)⁻¹ * (c b)⁻¹ = (c a)⁻¹
    field_simp
  have e := congrArg (resG _ (fun _ hx => ⟨hx.1, hx.2.1, hx.2⟩ :
    L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
      L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a ⊓ h ⁻¹ᵁ (chart k n a ⊓ chart k n b))))
    (huniq _ _ sa s₂ _ ⟨ha1, ha2⟩ g₂ i)
  exact (cross_resG_resG _ _ _).symm.trans (e.trans ((cross_resG_resG _ _ _).trans (cross_resG_self _ _)))

end GlobalTheory.UMin.ThBdl
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localThetaSections_ratio_coordinates_overlap : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (G : Over M.Z) [GrpObj G]
    (L : LB G.left) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (v : SecM G L 1 (Over.mk M.pt)),
    PCrd (M.pt ≫ h) c →
    (∀ (N N' : M.Z.Opens) (s : LocSec G L N) (s' : LocSec G L N') (w : SecM G L 1 (Over.mk M.pt)),
      GenIs M.pt s w → GenIs M.pt s' w → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) →
    ∀ (a b : Fin (n + 1)) (sa : LocSec G L (h ⁻¹ᵁ chart k n a)) (sb : LocSec G L (h ⁻¹ᵁ chart k n b)),
      (((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sa ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v)) →
      (((h ⁻¹ᵁ chart k n b : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sb ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b)⁻¹ • v)) →
      ∀ i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a)) (sa i) =
        resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i) := by
  atlas_forward_decl GlobalTheory.UMin.ThBdl.cross_ratio_sections
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

theorem resG_resG' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (f : Γ(X, U)) :
    resG X h₂ (resG X h₁ f) = resG X (h₂.trans h₁) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem chart_sec (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G))
    (hn : Geo.Tor.IsNormalScheme M.Z) (ho : Odd m) (h3 : 3 ≤ m) (hu : IsUnit (m : k)) (hp : PolFib t.G t.PP.L g M.pt)
    (hg : IsGenSec t.G t.PP.L _ θ) (hl : ThList t.G t.PP.L t.PP.rig m M.pt θ pt c) (hc : PCrd (M.pt ≫ h) c)
    (a : Fin (n + 1)) : ∃ s : LocSec t.G t.PP.L (h ⁻¹ᵁ chart k n a), IsLocSec s ∧
      ((((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ)) ∧
      FibNz s (h ⁻¹ᵁ chart k n a)) := by
  by_cases hne : ((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty
  · have hloc := GlobalTheory.T.exists_localSection_thetaQuotient_projChart E H k Ω M t g m n c h θ pt hn ho h3 hu hp hg hl hc a
    choose N hzN hNle s hs hgs hfs using hloc
    let κ := {z : M.Z // z ∈ h ⁻¹ᵁ chart k n a}
    have hsup : (⨆ z : κ, N z.1 z.2) = h ⁻¹ᵁ chart k n a :=
      le_antisymm (iSup_le fun z => hNle z.1 z.2) fun z hz =>
        TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzN z hz⟩
    obtain ⟨s', hs', hres⟩ := GlobalTheory.T.exists_glued_lineBundleSection_over_cover M.Z t.G t.PP.L (h ⁻¹ᵁ chart k n a) κ (fun z => N z.1 z.2) (fun z => s z.1 z.2)
      (fun z => hNle z.1 z.2) hsup (fun z => hs z.1 z.2) (fun z z' i =>
        GlobalTheory.T.lineBundleLocalSection_eq_of_generic_fibre M.Z t.G t.semi t.PP.L Ω M.pt M.gen _ _ _ _ _ (hgs z.1 z.2) (hgs z'.1 z'.2) i)
    obtain ⟨h1, h2⟩ := GlobalTheory.T.glued_section_generic_value_nonvanishing M.Z t.G t.PP.L Ω M.pt _ κ (fun z => N z.1 z.2) (fun z => s z.1 z.2) s' _
      (fun z => hNle z.1 z.2) hsup hres (fun z => hgs z.1 z.2) (fun z => hfs z.1 z.2)
    exact ⟨s', hs', fun _ => h1 ⟨⟨hne.some, hne.some_mem⟩⟩, h2⟩
  · refine ⟨0, isLocSec_zero, fun h' => absurd h' hne, fun K _ _ x hx => absurd ?_ hne⟩
    exact ⟨_, hx ⟨IsLocalRing.closedPoint K, rfl⟩⟩

end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

theorem app_resG {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (e : V ≤ U) (x : Γ(X, U)) :
    (f.app V).hom (resG X e x) = resG Y (fun _ hy => e hy : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) ((f.app U).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, f.naturality]
  rfl

theorem valF_resG {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (hV : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(X, U)) : valF y V (resG X e f) = valF y U f := by
  unfold valF
  rw [dif_pos hV, dif_pos (hV.trans fun x hx => show y x ∈ U from e (show y x ∈ V from hx))]
  congr 1
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl

theorem val_res' {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = resG X e (u : Γ(X, U)) := rfl

theorem val_pullU' {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    ((pullU f U u : Γ(Y, f ⁻¹ᵁ U)ˣ) : Γ(Y, f ⁻¹ᵁ U)) = (f.app U).hom (u : Γ(X, U)) := rfl
end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

set_option maxHeartbeats 2000000 in

theorem pull_theta_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n), Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt → HasTh t.G t.PP.L t.PP.rig m M.pt c → PCrd (M.pt ≫ h) c → ∃ σ : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).Sec, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), ∃ (y : Sp K ⟶ t.G.left) (j : _), y ≫ t.G.hom = x ∧ Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U j ∧ valF y _ (σ.f j) ≠ 0 := by
  intro E _ _ _ H k Ω _ _ _ _ _ M t g m n c h hn ho h3 hu hp hth hc
  obtain ⟨θ, pt, hg, hl⟩ := hth
  choose s hs hgs hfs using chart_sec E H k Ω M t g m n c h θ pt hn ho h3 hu hp hg hl hc
  have hcross := GlobalTheory.T.localThetaSections_ratio_coordinates_overlap k Ω M t.G t.PP.L n c h (SecM.ofSec t.G θ) hc (GlobalTheory.T.lineBundleLocalSection_eq_of_generic_fibre M.Z t.G t.semi t.PP.L Ω M.pt M.gen)
  have hle : ∀ p : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).ι,
      (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U p ≤
        t.PP.L.U p.1 ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n (p.2 PUnit.unit PUnit.unit)) := fun p y hy =>
    ⟨hy.1, Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩
  refine ⟨⟨fun p => resG _ (hle p) (s _ p.1), fun p q => ?_⟩, fun K _ _ x => ?_⟩
  · obtain ⟨i, pj⟩ := p
    obtain ⟨i', qj⟩ := q
    have eB : ∀ (Y : Scheme.{0}) (φ : Y ⟶ M.Z) (u v : PUnit → PUnit → Fin (n + 1)),
        ((((ProjSpace.O1 k n).pull h).pull φ).g u v : Γ(Y, _)) =
          resG Y (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
              Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩ :
            (((ProjSpace.O1 k n).pull h).pull φ).U u ⊓ (((ProjSpace.O1 k n).pull h).pull φ).U v ≤
              φ ⁻¹ᵁ (h ⁻¹ᵁ (chart k n (u PUnit.unit PUnit.unit) ⊓ chart k n (v PUnit.unit PUnit.unit))))
            ((φ.app _).hom ((h.app _).hom (ratioOn (chart k n (u PUnit.unit PUnit.unit) ⊓
              chart k n (v PUnit.unit PUnit.unit)) _ inf_le_left (v PUnit.unit PUnit.unit)))) := by
      intro Y φ u v
      have e1 := ProjSpace.linComb_punit_g ((ProjSpace.O1 k n).pull h) φ 1 u v
      have e2 := ProjSpace.linComb_punit_g (ProjSpace.O1 k n) h 1 (u PUnit.unit) (v PUnit.unit)
      rw [zpow_one] at e1 e2
      erw [e1]
      erw [e2]
      erw [val_res', val_pullU', val_res', val_pullU']
      rw [O1_g_eq_ratioUnit_chart_inf, val_ratioUnit]
      erw [app_resG, resG_resG']
      rfl
    have hW1 : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i, pj) ⊓
        (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i', qj) ≤
        t.PP.L.U i ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n (pj PUnit.unit PUnit.unit) ⊓ chart k n (qj PUnit.unit PUnit.unit))) :=
      fun y hy => ⟨hy.1.1, (hle _ hy.1).2, (hle _ hy.2).2⟩
    have hW2 : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i, pj) ⊓
        (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i', qj) ≤
        t.PP.L.U i ⊓ t.PP.L.U i' ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n (qj PUnit.unit PUnit.unit)) :=
      fun y hy => ⟨⟨hy.1.1, hy.2.1⟩, (hle _ hy.2).2⟩
    have e1 := congrArg (resG t.G.left hW1) (hcross _ _ (s _) (s _) (hgs _) (hgs _) i)
    have e2 := congrArg (resG t.G.left hW2) (hs (qj PUnit.unit PUnit.unit) i i')
    rw [map_mul] at e1 e2
    erw [resG_resG', resG_resG', resG_resG'] at e1
    erw [resG_resG', resG_resG', resG_resG'] at e2
    show resG _ _ (resG _ (hle (i, pj)) (s (pj PUnit.unit PUnit.unit) i)) = _ *
      resG _ _ (resG _ (hle (i', qj)) (s (qj PUnit.unit PUnit.unit) i'))
    rw [resG_resG', resG_resG']
    erw [Units.val_mul, val_res', val_res', eB, resG_resG']
    rw [e1, e2, mul_left_comm, ← _root_.mul_assoc]
    rfl
  · obtain ⟨a, ha⟩ := exists_mem_chart k n (h (x (IsLocalRing.closedPoint K)))
    have hx : Set.range x ⊆ h ⁻¹ᵁ chart k n a := by
      rintro _ ⟨w, rfl⟩
      rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
      exact ha
    obtain ⟨y, i, hyx, hyr, hv⟩ := hfs a K x hx
    have hyr' : Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U
        (i, fun _ _ => a) := fun _ hw =>
      ⟨(hyr hw).1, Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => (hyr hw).2⟩
    refine ⟨y, (i, fun _ _ => a), hyx, hyr', ?_⟩
    show valF y _ (resG _ (hle (i, fun _ _ => a)) (s a i)) ≠ 0
    rwa [valF_resG y _ ((GlobalTheory.ZH.top_le_preimage_iff y _).2 hyr')]

end GlobalTheory.UMin.ThBdl
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_coordinates_section_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n), Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt → HasTh t.G t.PP.L t.PP.rig m M.pt c → PCrd (M.pt ≫ h) c → ∃ σ : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).Sec, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), ∃ (y : Sp K ⟶ t.G.left) (j : _), y ≫ t.G.hom = x ∧ Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U j ∧ valF y _ (σ.f j) ≠ 0 := by
  atlas_forward_decl GlobalTheory.UMin.ThBdl.pull_theta_bundle
end

section
open Polynomial

namespace GlobalTheory

theorem pow_div_mem_of_esymm_pow_div_mem (K : Type) [Field K] (V : ValuationSubring K)
    (A : Type) [Fintype A] (x : A → K) (D : ℕ) (c : K) (hc : c ≠ 0)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card A →
      k ∣ D ∧ (Finset.univ.val.map x).esymm k ^ (D / k) / c ∈ V) (a : A) :
    x a ^ D / c ∈ V := by
  classical
  set v := V.valuation with hv
  set s : Multiset K := Finset.univ.val.map x with hs
  have hcard : Multiset.card s = Fintype.card A := by simp [s, Finset.card_univ]
  have hn : 1 ≤ Multiset.card s := hcard ▸ Fintype.card_pos_iff.mpr ⟨a⟩
  have hvc : v c ≠ 0 := (Valuation.ne_zero_iff v).mpr hc
  have mem_iff : ∀ y : K, y / c ∈ V ↔ v y ≤ v c := by
    intro y
    rw [← V.valuation_le_one_iff, ← hv, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvc)]
  rw [mem_iff]
  by_contra hlt
  push_neg at hlt
  rw [Valuation.map_pow] at hlt
  have key : ∀ k, 1 ≤ k → k ≤ Multiset.card s → v (s.esymm k) < v (x a) ^ k := by
    intro k hk1 hkn
    obtain ⟨hkD, hmem⟩ := h k hk1 (hcard ▸ hkn)
    rw [mem_iff, Valuation.map_pow] at hmem
    by_contra hge
    push_neg at hge
    have hp : (v (x a) ^ k) ^ (D / k) ≤ v (s.esymm k) ^ (D / k) := pow_le_pow_left₀ zero_le' hge _
    rw [← pow_mul, Nat.mul_div_cancel' hkD] at hp
    exact absurd (hp.trans hmem) (not_le.mpr hlt)
  have hpos : 0 < v (x a) := by
    have := key 1 le_rfl hn
    rw [pow_one] at this
    exact lt_of_le_of_lt zero_le' this
  have h0 : (s.map fun t => X - C t).prod.eval (x a) = 0 := by
    rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff]
    simp only [Multiset.map_map, Function.comp_def, eval_sub, eval_X, eval_C]
    exact Multiset.mem_map.mpr ⟨x a, by simp [s], sub_self _⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, eval_finset_sum, Finset.sum_range_succ'] at h0
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_X, pow_zero, one_mul,
    Nat.sub_zero] at h0
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  rw [he0, one_mul, ← eq_neg_iff_add_eq_zero] at h0
  have hlt2 : v (∑ j ∈ Finset.range (Multiset.card s),
      (-1) ^ (j + 1) * (s.esymm (j + 1) * x a ^ (Multiset.card s - (j + 1)))) < v (x a) ^ Multiset.card s := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hpos.ne')
    intro j hj
    have hj' : j + 1 ≤ Multiset.card s := Finset.mem_range.mp hj
    rw [map_mul, map_mul, map_pow, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    calc v (s.esymm (j + 1)) * v (x a) ^ (Multiset.card s - (j + 1))
        < v (x a) ^ (j + 1) * v (x a) ^ (Multiset.card s - (j + 1)) :=
          mul_lt_mul_of_pos_right (key (j + 1) (Nat.succ_le_succ (Nat.zero_le _)) hj') (pow_pos hpos _)
      _ = v (x a) ^ Multiset.card s := by rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [h0, Valuation.map_neg, map_pow] at hlt2
  exact lt_irrefl _ hlt2

end GlobalTheory
end

section
namespace GlobalTheory

theorem exists_esymm_pow_div_mem_of_isLocalRing : ∀ (K : Type) [Field K] (O : Subring K) [IsLocalRing O] (A : Type) [Fintype A] (x : A → K) (D k : ℕ) (c : K), 1 ≤ D → 1 ≤ k → k ∣ D → c ≠ 0 → (Finset.univ.val.map x).esymm k ^ (D / k) = c → (∀ a, x a ^ D / c ∈ O) → ∃ a, x a ≠ 0 ∧ c / x a ^ D ∈ O := by
  intro K _ O _ A _ x D k c hD hk hkD hc hce hO
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.mk O).exists_le_valuationSubring
  have hkD' : 0 < D / k := Nat.div_pos (Nat.le_of_dvd (by omega) hkD) (by omega)
  have hes : (Finset.univ.val.map x).esymm k = ∑ t ∈ (Finset.univ : Finset A).powersetCard k, ∏ b ∈ t, x b :=
    Finset.esymm_map_val x _ k
  rcases isEmpty_or_nonempty A with hA | hA
  · exfalso
    apply hc
    rw [← hce, hes, Finset.powersetCard_eq_empty.2 (by simp; omega), Finset.sum_empty, zero_pow hkD'.ne']
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A) (fun b => V.valuation (x b))
    Finset.univ_nonempty
  have hvc : V.valuation c ≠ 0 := by simpa using hc
  have h1 : V.valuation (x a) ^ D ≤ V.valuation c := by
    have := (V.valuation_le_one_iff _).2 (hle (hO a))
    rw [map_div₀, map_pow] at this
    exact (div_le_one₀ (zero_lt_iff.2 hvc)).1 this
  have h2 : V.valuation c ≤ V.valuation (x a) ^ D := by
    rw [← hce, map_pow, hes]
    have hb : V.valuation (∑ t ∈ (Finset.univ : Finset A).powersetCard k, ∏ b ∈ t, x b) ≤ V.valuation (x a) ^ k := by
      refine Valuation.map_sum_le _ (fun t ht => ?_)
      rw [map_prod]
      have hcard := (Finset.mem_powersetCard.1 ht).2
      rw [← hcard]
      exact Finset.prod_le_pow_card _ _ _ (fun b _ => ha b (Finset.mem_univ b))
    calc _ ≤ (V.valuation (x a) ^ k) ^ (D / k) := pow_le_pow_left₀ zero_le' hb _
      _ = V.valuation (x a) ^ D := by rw [← pow_mul, Nat.mul_div_cancel' hkD]
  have heq : V.valuation (x a) ^ D = V.valuation c := le_antisymm h1 h2
  have hxa : x a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_pow (by omega)] at heq
    exact hvc heq.symm
  refine ⟨a, hxa, ?_⟩
  let y : O := ⟨x a ^ D / c, hO a⟩
  have hyV : IsUnit (Subring.inclusion hle y) := by
    refine (V.valuation_eq_one_iff ⟨x a ^ D / c, hle (hO a)⟩).2 ?_
    show V.valuation (x a ^ D / c) = 1
    rw [map_div₀, map_pow, heq, div_self hvc]
  have hy : IsUnit y := hloc.map_nonunit _ hyV
  obtain ⟨u, hu⟩ := hy
  have : ((u⁻¹ : Oˣ) : O) = c / x a ^ D := by
    have h3 : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    rw [hu] at h3
    have h4 : (x a ^ D / c) * (((u⁻¹ : Oˣ) : O) : K) = 1 := h3
    show (((u⁻¹ : Oˣ) : O) : K) = c / x a ^ D
    rw [eq_inv_of_mul_eq_one_right h4, inv_div]
  rw [← this]
  exact ((u⁻¹ : Oˣ) : O).2

end GlobalTheory
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem hasDiv_of_hasDiv_symTup : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (N : ℕ)
    (c : Fin N → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv (symTup c) → M.HasDiv c := by
  intro k Ω _ _ _ M N c hn hd z
  obtain ⟨j, he, hdiv⟩ := hd z
  haveI := RatModel.isIntegrallyClosed_O hn z
  set D := N.factorial with hD
  set e := symTup c j with he'
  have hD1 : 1 ≤ D := Nat.factorial_pos N

  haveI : IsFractionRing (M.O z).toSubring Ω := inferInstanceAs (IsFractionRing (M.O z) Ω)
  haveI : IsIntegrallyClosed (M.O z).toSubring := inferInstanceAs (IsIntegrallyClosed (M.O z))
  haveI hcl : IsIntegrallyClosedIn (M.O z).toSubring Ω :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn Ω).1 inferInstance
  have h1 : ∀ a, c a ^ D / e ∈ M.O z := by
    intro a
    have hmem : c a ^ D / e ∈ ⨅ V : {V : ValuationSubring Ω // (M.O z).toSubring ≤ V.toSubring}, V.1.toSubring := by
      refine Subring.mem_iInf.2 fun V => ?_
      refine pow_div_mem_of_esymm_pow_div_mem Ω V.1 (Fin N) c D e he (fun i hi1 hi2 => ?_) a
      simp only [Fintype.card_fin] at hi2
      refine ⟨Nat.dvd_factorial hi1 hi2, V.2 ?_⟩
      have := hdiv ⟨i - 1, by omega⟩
      simp only [symTup, Nat.sub_add_cancel hi1] at this
      exact this
    rw [← Subring.eq_iInf_of_isIntegrallyClosedIn] at hmem
    exact hmem
  haveI : IsLocalRing (M.O z).toSubring := inferInstanceAs (IsLocalRing (M.O z))
  obtain ⟨a, ha, hea⟩ := exists_esymm_pow_div_mem_of_isLocalRing Ω (M.O z).toSubring (Fin N) c D ((j : ℕ) + 1) e hD1
    (by omega) (Nat.dvd_factorial (by omega) (by omega)) he rfl h1
  refine ⟨a, ha, fun b => ?_⟩
  have hpow : (c b / c a) ^ D ∈ M.O z := by
    have : (c b / c a) ^ D = (c b ^ D / e) * (e / c a ^ D) := by
      rw [div_pow, div_mul_div_cancel₀ he]
    rw [this]
    exact mul_mem (h1 b) hea
  have hint : IsIntegral (M.O z) (c b / c a) :=
    IsIntegral.of_pow (by omega) (isIntegral_algebraMap (R := M.O z) (x := ⟨_, hpow⟩))
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact hy ▸ y.2

end GlobalTheory.UMin
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDiv_of_hasDiv_thetaSymmetricFunctionsDegreeFactorial : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (N : ℕ) (c : Fin N → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv (symTup c) → M.HasDiv c := by
  atlas_forward_decl GlobalTheory.UMin.hasDiv_of_hasDiv_symTup
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

section Moves

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}

theorem hasTh_of_sabMap (mm : SABMap t' t f) (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S') {N : ℕ}
    (c : Fin N → K) :
    HasTh t'.G t'.PP.L t'.PP.rig m x c ↔ HasTh t.G t.PP.L t.PP.rig m (x ≫ f) c := by
  rw [hasTh_iff, hasTh_iff]
  exact GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen S' t'.G t'.PP.L t'.PP.rig f mm.φ t'.PP.isLB
    t'.PP.rigGen mm.cart (GlobalTheory.ModelSum.lbIso_of_map mm) m m N N K x c c

theorem polFib_of_sabMap (mm : SABMap t' t f) (g : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S') :
    PolFib t'.G t'.PP.L g x ↔ PolFib t.G t.PP.L g (x ≫ f) :=
  (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S' t.G t.PP.L t'.G t'.PP.L f mm.φ t.PP.isLB t'.PP.isLB mm.cart
    (GlobalTheory.ModelSum.lbIso_of_map mm) g R x).1

end Moves

end GlobalTheory.UMin

namespace GlobalTheory.UMin

open GlobalTheory.CechPic in

theorem key_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (π : M.Z ⟶ Y.X) (y : Sp Ω ⟶ Xo.XF c) (d : Fin (n + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ π = y ≫ Y.j → HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (y ≫ pullback.fst _ _) d → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) 8).pull π) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial)).pull π) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf Y g hYg Ω _ _ _ M π y d hZ hpt hth
  obtain ⟨t, ⟨mt⟩⟩ := GlobalTheory.ModelSum.exists_pull π Y.t
  have hP : PCrd (M.pt ≫ (π ≫ g)) (symTup d) := by
    have h1 : M.pt ≫ (π ≫ g) = y ≫ f := by rw [← Category.assoc, hpt, Category.assoc, hYg]
    rw [h1]; exact hf Ω y d hth
  have hD : M.HasDiv d :=
    GlobalTheory.T.hasDiv_of_hasDiv_thetaSymmetricFunctionsDegreeFactorial c.F Ω M (n + 1) d hZ (GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords c.F Ω o M n (π ≫ g) (symTup d) hP)
  obtain ⟨h, -, hhP⟩ := GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv c.F Ω M n d hD
  have hsym := GlobalTheory.T.symmetric_coordinates_O1_factorial_power c.F Ω o M n h (π ≫ g) d hhP hP
  have hThO : HasTh Y.oF.t.G Y.oF.t.PP.L Y.oF.t.PP.rig m y d := (hasTh_of_sabMap Y.m0.toSABMap m y d).2 hth
  have hThY : HasTh Y.t.G Y.t.PP.L Y.t.PP.rig m (M.pt ≫ π) d := by
    rw [hpt]; exact (hasTh_of_sabMap Y.m m y d).1 hThO
  have hTh : HasTh t.G t.PP.L t.PP.rig m M.pt d := (hasTh_of_sabMap mt m M.pt d).2 hThY
  have hPolO : PolFib Y.oF.t.G Y.oF.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) y :=
    (polFib_of_sabMap Y.m0.toSABMap _ y).2 (GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c Ω _)
  have hPolY : PolFib Y.t.G Y.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (M.pt ≫ π) := by
    rw [hpt]; exact (polFib_of_sabMap Y.m _ y).1 hPolO
  have hPol : PolFib t.G t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) M.pt := (polFib_of_sabMap mt _ M.pt).2 hPolY
  have hmk : IsUnit (m : c.F) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (by omega))
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.theta_coordinates_section_exists E H c.F Ω M t _ m n d h hZ hm hm3 hmk hPol hTh hhP
  obtain ⟨hab, hop, hamp⟩ := GlobalTheory.T.abelianLocus_eq_preimage_moduli_and_principal E H Dw l Xo c Y M.Z π t ⟨mt⟩
  obtain ⟨hsmY, hvY⟩ := GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y
  have hsm : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback mt.cart.1 hsmY
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have hne : ((⊤ : M.Z.Opens) : Set M.Z).Nonempty := ⟨M.pt (IsLocalRing.closedPoint Ω), trivial⟩
  haveI : CharZero Γ(M.Z, ⊤) := (M.res ⊤ hne).charZero
  have hne2 : (abLocus t.G).Nonempty := by
    refine ⟨M.pt (IsLocalRing.closedPoint Ω), ?_⟩
    rw [hab]
    show π (M.pt (IsLocalRing.closedPoint Ω)) ∈ Set.range Y.j
    have hq := congrArg (fun φ : Sp Ω ⟶ Y.X => φ (IsLocalRing.closedPoint Ω)) hpt
    exact ⟨y (IsLocalRing.closedPoint Ω), hq.symm⟩
  have hδ : ((ProjSpace.O1 c.F n).pull h).IsLB := pull_isLB (ProjSpace.O1_isLB c.F n) h
  have := Y.t.semi.separated
  have hHY := hvY.isLB_det
  have hHt := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback mt.cart hvY).isLB_det
  have hkey : LBIso (lbPow ((ProjSpace.O1 c.F n).pull h) 8)
      (lbPow (GlobalTheory.SiegelTor.hodge t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) 4) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) with h0 | h0
    · have hn0 : n = 0 := by
        rw [h0] at hn
        simpa using hn
      subst hn0
      refine (cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hHt 4)).1 ?_
      have hz : cls _ hHt = 0 := by
        revert hHt
        rw [h0]
        exact fun hHt => KeySmall.cls_det_zero _ hHt
      rw [cls_lbPow hδ, cls_lbPow hHt, hz, cls_pull (ProjSpace.O1_isLB c.F 0), KeySmall.cls_O1_zero, map_zero,
        nsmul_zero, nsmul_zero]
    · refine KeySmall.key_sab M.Z t _ _ σ h0 hZ inferInstance inferInstance (fun A _ ξ hξ => ?_) hsm hne2 hop hδ hamp
        (KeySmall.nzFib_of_geom σ hσ)
      exact KeySmall.mk_le_of_lft ((Cardinal.mk_le_of_injective (f := fun a : c.F => (a : ℂ)) Subtype.val_injective).trans_eq
        Cardinal.mk_complex) (ξ ≫ M.s)
  have hO := ProjSpace.O1_isLB o n
  have e1 := (cls_eq_iff (pull_isLB hO (π ≫ g)) (isLB_lbPow hδ _)).2 hsym
  have e2 := (cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hHt 4)).2 hkey
  have e3 := (cls_eq_iff (pull_isLB hHY π) hHt).2 (GlobalTheory.HodgeGenDesc.lbIso_hodge_pull mt.cart hvY)
  rw [cls_pull hO, pull_comp, cls_lbPow hδ] at e1
  rw [cls_lbPow hδ, cls_lbPow hHt] at e2
  rw [cls_pull hHY] at e3
  refine (cls_eq_iff (pull_isLB (isLB_lbPow (pull_isLB hO g) 8) π) (pull_isLB (isLB_lbPow hHY _) π)).1 ?_
  rw [cls_pull (isLB_lbPow (pull_isLB hO g) 8), cls_pull (isLB_lbPow hHY _), cls_lbPow (pull_isLB hO g),
    cls_lbPow hHY, map_nsmul, map_nsmul, cls_pull hO, e1, e3, smul_smul, mul_comm 8, ← smul_smul, e2, smul_smul,
    mul_comm]

end GlobalTheory.UMin

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyFormula_normalCover_rational_thetaConstants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (π : M.Z ⟶ Y.X) (y : Sp Ω ⟶ Xo.XF c) (d : Fin (n + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ π = y ≫ Y.j → HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (y ≫ pullback.fst _ _) d → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) 8).pull π) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial)).pull π) := by
  atlas_forward_decl GlobalTheory.UMin.key_on_cover
end
