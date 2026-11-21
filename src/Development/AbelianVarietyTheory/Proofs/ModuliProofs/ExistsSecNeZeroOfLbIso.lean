import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVarietyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMaximalMinorNeZeroOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.EffectiveCube

theorem unitAt_pull {X Y : Scheme.{0}} {N : LB X} (s : N.Sec) (φ : Y ⟶ X) (y : Y)
    (h : φ y ∈ Out.nonzeroLocus s) : UnitAt N (K := PUnit) (fun _ => φ) (fun _ => 1) y := by
  have h' : y ∈ Out.nonzeroLocus (GlobalTheory.secPull s φ) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact h
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h'
  exact ⟨GlobalTheory.secPull s φ, fun J hJ => isUnit_sval _ (𝟙 Y) y hJ k hk⟩

theorem exists_mem_of_unitAt {X Y : Scheme.{0}} {N : LB X} (hN : N.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {ε : I → ℤ} {y : Y} (h : UnitAt N φ ε y) :
    ∃ u : (LB.LinComb N φ ε).Sec, y ∈ Out.nonzeroLocus u := by
  obtain ⟨u, hu⟩ := h
  choose J hJ using fun χ : Y ⟶ X => exists_chart hN (χ y)
  exact ⟨u, (mem_nonzeroLocus u y).2 ⟨_, Good.mem hJ φ (𝟙 Y), hu J hJ⟩⟩

theorem exists_fin_cover {X : Scheme.{0}} [CompactSpace X] [JacobsonSpace X] (M : LB X)
    (h : ∀ y : X, IsClosed {y} → ∃ u : M.Sec, y ∈ Out.nonzeroLocus u) :
    ∃ (r : ℕ) (u : Fin r → M.Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  have hall : (Set.univ : Set X) ⊆ ⋃ u : M.Sec, (Out.nonzeroLocus u : Set X) := by
    intro y _
    by_contra hy
    have ho : IsOpen (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X)) :=
      isOpen_iUnion fun u => (Out.nonzeroLocus u).isOpen
    obtain ⟨c, hc, hcl⟩ := nonempty_inter_closedPoints
      (Z := (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X))ᶜ) ⟨y, hy⟩ ho.isClosed_compl.isLocallyClosed
    obtain ⟨u, hu⟩ := h c hcl
    exact hc (Set.mem_iUnion.2 ⟨u, hu⟩)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover _ (fun u : M.Sec => (Out.nonzeroLocus u).isOpen) hall
  refine ⟨T.card, fun i => (T.equivFin.symm i).1, eq_top_iff.2 fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨T.equivFin ⟨u, hu⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hy

theorem exists_sections_cube_cover :
    (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (s : N.Sec), N.IsLB → (∃ j, s.f j ≠ 0) → ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro hcube K _ _ P N s hN ⟨j, hj⟩
  obtain ⟨t, ht⟩ := hcube _ P N hN
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have : IsIntegral (T ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 (Sp K)) _ _ (IsPullback.of_hasPullback (𝟙 (Sp K)) P.A.hom).flip
  have : JacobsonSpace P.A.left := LocallyOfFiniteType.jacobsonSpace P.A.hom
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  let π : P.A ⟶ T := Over.homMk P.A.hom (Category.comp_id _)
  have hD : (((snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s : (T ⊗ P.A).left.Opens) : Set (T ⊗ P.A).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((P.A.left.basicOpen (s.f j) : P.A.left.Opens) : Set P.A.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨(lift π (𝟙 _)).left d, ?_⟩
    show (snd T P.A).left ((lift π (𝟙 _)).left d) ∈ Out.nonzeroLocus s
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hd⟩
  refine exists_fin_cover _ fun y hy => ?_
  let x : T ⟶ P.A := Over.homMk (pointOfClosedPoint P.A.hom y hy) (pointOfClosedPoint_comp P.A.hom y hy)
  let p : T.left := IsLocalRing.closedPoint K
  have hx : x.left p = y := pointOfClosedPoint_apply P.A.hom y hy p
  have hxπ : x ≫ π = 𝟙 T := Over.OverMorphism.ext (pointOfClosedPoint_comp P.A.hom y hy)
  have good : ∀ a : T ⟶ P.A, (Out.ptSecT P.A (a * x)).left p ∈ (snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s →
      UnitAt N (K := PUnit) (fun _ => ((π ≫ a) * 𝟙 P.A).left) (fun _ => 1) y := fun a ha => by
    refine unitAt_pull s _ y ?_
    have e : x ≫ ((π ≫ a) * 𝟙 P.A) = Out.ptSecT P.A (a * x) ≫ snd T P.A := by
      simp [Out.ptSecT, MonObj.comp_mul, reassoc_of% hxπ]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact ha
  obtain ⟨a, ha, -⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x x
  obtain ⟨b, hb, hc⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x (a⁻¹ * x)
  rw [← _root_.mul_assoc] at hc
  choose i hi using fun k : Fin 4 => exists_chart hN ((![a, b, b⁻¹ * a⁻¹, 1] k).left p)
  obtain ⟨w, hw⟩ := SepPoints.exists_gen_three hN t ht (π ≫ a) (π ≫ b) (π ≫ (b⁻¹ * a⁻¹)) (𝟙 P.A) 1
    (by rw [pow_one, ← MonObj.comp_mul, ← MonObj.comp_mul]; simp) i (fun k z => by
      have e : (![(π ≫ a).left, (π ≫ b).left, (π ≫ (b⁻¹ * a⁻¹)).left, (1 : P.A ⟶ P.A).left] k) =
          π.left ≫ (![a, b, b⁻¹ * a⁻¹, 1] k).left := by
        fin_cases k
        · rfl
        · rfl
        · rfl
        · exact congrArg (fun q : P.A ⟶ P.A => q.left) (MonObj.comp_one π).symm
      rw [e, Scheme.Hom.comp_apply, spec_pt_eq (k := K) (π.left z) p]
      exact hi k)
  have hw' : UnitAt N _ _ y := ⟨genSec w hw, fun J hJ => by
    rw [sval_genSec w hw _ y hJ]; exact Units.isUnit _⟩
  refine exists_mem_of_unitAt hN (UnitAt.congr hN (formEq_of_add fun U _ hh => ?_)
    (((hw'.mul (good a (ha p))).mul (good b (hb p))).mul (good _ (hc p))))
  simp [Fin.sum_univ_succ]
  module

end GlobalTheory.EffectiveCube
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_sections_cover_cube_effective_abelianVariety : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (s : N.Sec), N.IsLB → (∃ j, s.f j ≠ 0) → ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.EffectiveCube.exists_sections_cube_cover | exact GlobalTheory.EffectiveCube.exists_sections_cube_cover | (intros; apply GlobalTheory.EffectiveCube.exists_sections_cube_cover <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem IsAmpleLB.of_pow_div_generated {X : Scheme.{0}} {L N : LB X} (hL : IsAmpleLB L) (hN : N.IsLB) {m : ℕ}
    (hm : 1 ≤ m) {J : Type} (u : J → (lbPow (LB.div N L) m).Sec) (hu : ⨆ i, Out.nonzeroLocus (u i) = ⊤) :
    IsAmpleLB N := by
  refine ⟨hN, hL.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := hL.exists_affine x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
  have hD := LB.isLB_div hN hL.isLB
  obtain ⟨v, hv⟩ := exists_sec_pow_nonzeroLocus_eq_inf hL.isLB hD hN (lbIso_refl hD) (secPow s m)
    (secCast (Nat.mul_comm m n) (secPow (u i) n))
  rw [nonzeroLocus_secCast, nonzeroLocus_secPow _ hn, nonzeroLocus_secPow _ hm] at hv
  exact ⟨n * m, Nat.mul_pos hn hm, v, hv.ge ⟨hi, hs⟩,
    hv ▸ isAffineOpen_nonzeroLocus_inf (isLB_lbPow hD m) (u i) ha⟩

theorem relAmple_of_cube_div_generated : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left) (a r : ℕ) (u : Fin r → (lbPow (LB.div (lbPow M a) L) 3).Sec), IsProper A.hom → L.IsLB → M.IsLB → 1 ≤ a → Out.RelAmple A L → ⨆ i, Out.nonzeroLocus (u i) = ⊤ → Out.RelAmple A M := by
  intro K _ A L M a r u hA hL hM ha hamp hu
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  exact (relAmple_iff_isAmpleLB_of_isAffine A hM).2 ((isAmpleLB_pow_iff hM ha).1
    (h₁.of_pow_div_generated (isLB_lbPow hM a) (by norm_num) u hu))

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.relAmple_of_cube_div_generated_field : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left) (a r : ℕ) (u : Fin r → (lbPow (LB.div (lbPow M a) L) 3).Sec), IsProper A.hom → L.IsLB → M.IsLB → 1 ≤ a → Out.RelAmple A L → ⨆ i, Out.nonzeroLocus (u i) = ⊤ → Out.RelAmple A M := by
  first | exact @GlobalTheory.relAmple_of_cube_div_generated | exact GlobalTheory.relAmple_of_cube_div_generated | (intros; apply GlobalTheory.relAmple_of_cube_div_generated <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleDivSec

open LBGerm GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}}

def invLB (L : LB X) : LB X := ⟨L.1, L.U, fun i j => (L.g i j)⁻¹⟩

theorem isLB_invLB {L : LB X} (hL : L.IsLB) : (invLB L).IsLB where
  cover := hL.cover
  g_self i := by
    have h := congrArg (·⁻¹) (hL.g_self i)
    simp only [inv_one, ← map_inv] at h
    exact h
  cocycle i j k := by
    have h := congrArg (·⁻¹) (hL.cocycle i j k)
    simp only [mul_inv, ← map_inv] at h
    exact h

theorem exists_sec_div (L M : LB X) (n t : ℕ) (u : LB.Sec (tw (invLB L) (lbPow M n) (t : ℤ))) :
    ∃ s : (LB.div (lbPow M (n * t)) L).Sec, nonzeroLocus u ≤ nonzeroLocus s := by
  have le : ∀ p : (PUnit → M.ι) × L.ι, powChart M p.1 ⊓ L.U p.2 ≤ L.U p.2 ⊓ powChart M p.1 :=
    fun p y hy => ⟨hy.2, hy.1⟩
  let F : ∀ p : (PUnit → M.ι) × L.ι, Γ(X, powChart M p.1 ⊓ L.U p.2) := fun p =>
    resG X (le p) (show Γ(X, L.U p.2 ⊓ powChart M p.1) from u.f (p.2, p.1))
  have hF : ∀ (y : X) (p : (PUnit → M.ι) × L.ι), y ∈ powChart M p.1 ⊓ L.U p.2 → gs (𝟙 X) y _ (F p) =
      gs (𝟙 X) y _ (u.f (p.2, p.1)) := fun y p hy => gs_res (𝟙 X) y (le p) hy _
  refine ⟨secOfGerm (M := LB.div (lbPow M (n * t)) L) F fun y p q hp hq => ?_, fun y hy => ?_⟩
  · have e₁ := gs_compat u (𝟙 X) y (j := (p.2, p.1)) (j' := (q.2, q.1)) (le p hp) (le q hq)
    have e₂ := TwistGen.gm_tw_g (invLB L) (lbPow M n) t y (p.2, p.1) (q.2, q.1) (le p hp) (le q hq)
    have e₃ := gm_lbPow_g (L := M) n (𝟙 X) y p.1 q.1 hp.1 hq.1
    have e₄ := gm_lbPow_g (L := M) (n * t) (𝟙 X) y p.1 q.1 hp.1 hq.1
    have e₅ := gm_div L (lbPow M (n * t)) (𝟙 X) y p q ⟨hp, hq⟩
    have e₆ : gm (𝟙 X) y ((invLB L).U p.2 ⊓ (invLB L).U q.2) ((invLB L).g p.2 q.2) =
        (gm (𝟙 X) y (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := map_inv _ _
    rw [e₄] at e₅
    dsimp only at e₂
    rw [e₃, e₆] at e₂
    refine (hF y p hp).trans (e₁.trans (congrArg₂ (· * ·) (e₂.trans ?_) (hF y q hq).symm))
    refine Eq.trans ?_ (congrArg Units.val e₅).symm
    rw [Units.val_mul, pow_mul, _root_.mul_comm]
    simp only [Units.val_pow_eq_pow_val]
  · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy
    have hp' : y ∈ powChart M p.2 ⊓ L.U p.1 := ⟨hp.2, hp.1⟩
    refine (mem_nonzeroLocus_iff_isUnit (M := LB.div (lbPow M (n * t)) L) _ (k := (p.2, p.1)) hp').2 ?_
    exact (congrArg IsUnit (hF y (p.2, p.1) hp')).mpr ((mem_nonzeroLocus_iff_isUnit u hp).1 hy)

theorem exists_sec_div_mem {L M : LB X} (hL : L.IsLB) (hM : IsAmpleLB M) (x : X) :
    ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ x ∈ nonzeroLocus s := by
  have := hM.compactSpace
  have := hM.quasiSeparatedSpace
  obtain ⟨n, hn, σ, hx, ha⟩ := hM.exists_affine x
  obtain ⟨V, N, hV, h⟩ := TwistGen.exists_nhds (isLB_invLB hL) (isLB_lbPow hM.isLB n) σ ha x hx
  obtain ⟨u, hu⟩ := h 1
  obtain ⟨s, hs⟩ := exists_sec_div L M n (N + 1) u
  exact ⟨_, s, Nat.mul_pos hn (Nat.succ_pos N), hs (hu hV)⟩

theorem exists_sec_pow_div_ne_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left), IsProper A.hom → Nonempty A.left → L.IsLB → M.IsLB → Out.RelAmple A M → ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ ∃ j, s.f j ≠ 0 := by
  intro K _ A L M _ ⟨x⟩ hL hM hA
  obtain ⟨a, s, ha, hx⟩ := exists_sec_div_mem hL (isAmpleLB_of_relAmple_of_isAffine A hM hA) x
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨a, s, ha, j, fun h => ?_⟩
  rw [h, Scheme.basicOpen_zero] at hj
  exact hj

end GlobalTheory.AmpleDivSec
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_sec_relAmplePow_div_ne_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left), IsProper A.hom → Nonempty A.left → L.IsLB → M.IsLB → Out.RelAmple A M → ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ ∃ j, s.f j ≠ 0 := by
  first | exact @GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero | exact GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero | (intros; apply GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.GenericSection
open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecBC

theorem exists_ker_ne_zero {R K K' : Type} [CommRing R] [Field K] [Field K'] (g : R →+* K) (g' : R →+* K')
    (hg : Function.Injective g) {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (v : Fin a → K) (hv : v ≠ 0)
    (h : (D.map g).mulVec v = 0) : ∃ v' : Fin a → K', v' ≠ 0 ∧ (D.map g').mulVec v' = 0 := by
  by_contra hno
  push Not at hno
  have hind : LinearIndependent K' (fun j : Fin a => fun i : Fin b => (D.map g') i j) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hc0
    push Not at hc0
    have hc' : c ≠ 0 := fun h0 => by
      obtain ⟨j, hj⟩ := hc0
      exact hj (by rw [h0]; rfl)
    apply hno c hc'
    funext i
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  obtain ⟨e, -, he⟩ := GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent K' b (Fin a) _ hind
  have hdet : (D.submatrix e id).det ≠ 0 := by
    intro h0
    apply he
    have : (Matrix.of fun k j => (D.map g') (e k) j) = (D.submatrix e id).map g' := by
      ext k j
      rfl
    have hm := RingHom.map_det g' (D.submatrix e id)
    rw [RingHom.mapMatrix_apply] at hm
    rw [this, ← hm, h0, map_zero]
  have hdetK : ((D.map g).submatrix e id).det ≠ 0 := by
    have : (D.map g).submatrix e id = (D.submatrix e id).map g := rfl
    have hm := RingHom.map_det g (D.submatrix e id)
    rw [RingHom.mapMatrix_apply] at hm
    rw [this, ← hm]
    exact fun h0 => hdet (hg (by rw [h0, map_zero]))
  apply hv
  apply Matrix.eq_zero_of_mulVec_eq_zero hdetK
  funext k
  have := congrFun h (e k)
  simpa [Matrix.mulVec, dotProduct, Matrix.submatrix] using this

def zeroSec {X : Scheme.{0}} (M : LB X) : LB.Sec M where
  f := fun _ => 0
  compat := fun _ _ => by rw [map_zero, map_zero, mul_zero]

theorem exists_sec_iff {X X' Y : Scheme.{0}} {L : LB Y} {p : X ⟶ Y} {R R' : Type} [CommRing R] [CommRing R']
    {f : X ⟶ Spec (CommRingCat.of R)} (F : Perf f (L.pull p)) (g : R →+* R') {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {q : X' ⟶ Y} (e : q = π ≫ p) :
    (∃ (s : (L.pull q).Sec) (j : _), s.f j ≠ 0) ↔ ∃ v : Fin F.a → R', v ≠ 0 ∧ (F.D₀.map g).mulVec v = 0 := by
  subst e
  unfold LB.pull at F ⊢
  let c : R' →+* Γ(X', ⊤) := f'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
  obtain ⟨h1, h2, h3⟩ := SecBC.rep_main (F := F) (ψ := fun _ => π ≫ p) (fun _ => rfl) g f' H c (fun _ => rfl)
  have h0 : SecBC.Rep π (fun _ => π ≫ p) F c 0 (zeroSec (L.LinComb (fun _ : PUnit.{1} => π ≫ p) (fun _ => 1))).f := by
    have hs := SecBC.Rep.sum (F := F) (ψ := fun _ => π ≫ p) (c := c) (fun _ => rfl) (I := Empty)
      (w := Empty.elim) (b := Empty.elim) (fun l => l.elim) Empty.elim
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
    exact hs
  constructor
  · rintro ⟨s, j, hs⟩
    obtain ⟨v, hv, hrep⟩ := h2 s
    refine ⟨v, fun hv0 => hs ?_, hv⟩
    subst hv0
    rw [SecBC.Rep.sec_eq (fun _ => rfl) hrep h0]
    rfl
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨s, hs⟩ := h1 v hv
    by_contra hno
    push Not at hno
    apply hv0
    have hz : s = zeroSec _ := SecBC.sec_ext (fun j => hno s j)
    rw [hz] at hs
    exact h3 v 0 (zeroSec (L.LinComb (fun _ : PUnit.{1} => π ≫ p) (fun _ => 1))) hv (Matrix.mulVec_zero _) hs h0

theorem exists_ringHom {S : Scheme.{0}} {R K : Type} [CommRing R] [Field K] (t : Sp R ⟶ S) [IsOpenImmersion t]
    (x : Sp K ⟶ S) (h : Set.range x ⊆ Set.range t) :
    ∃ g : R →+* K, Spec.map (CommRingCat.ofHom g) ≫ t = x := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift t x h)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac t x h

theorem exists_isPullback {A S T T' : Scheme.{0}} (a : A ⟶ S) (t : T ⟶ S) (u : T' ⟶ T) (x : T' ⟶ S)
    (h : u ≫ t = x) : ∃ π : pullback a x ⟶ pullback a t,
      IsPullback π (pullback.snd a x) (pullback.snd a t) u ∧ pullback.fst a x = π ≫ pullback.fst a t := by
  subst h
  have hc : pullback.fst a (u ≫ t) ≫ a = (pullback.snd a (u ≫ t) ≫ u) ≫ t := by
    rw [pullback.condition, Category.assoc]
  refine ⟨pullback.lift _ _ hc, ?_, (pullback.lift_fst _ _ hc).symm⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ hc) (IsPullback.of_hasPullback a t)
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback a (u ≫ t)

theorem exists_sec_ne_zero_of_generic : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] (P : Out.PolAV S) (N : LB P.A.left) (K K' : Type) [Field K] [Field K'] (x : Sp K ⟶ S) (y : Sp K' ⟶ S) (s : (N.pull (pullback.fst P.A.hom x)).Sec), N.IsLB → Set.range x = {genericPoint S} → (∃ j, s.f j ≠ 0) → ∃ (s' : (N.pull (pullback.fst P.A.hom y)).Sec) (j : _), s'.f j ≠ 0 := by
  intro hLaws S _ P N K K' _ _ x y s hN hx hs
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show y (IsLocalRing.closedPoint K') ∈ (⊤ : S.Opens) from trivial)
  let t : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hrange : Set.range t = W := hW.range_fromSpec
  have hgen : genericPoint S ∈ (W : Set S) := by
    rw [(genericPoint_spec S).mem_open_set_iff W.isOpen]
    exact ⟨_, trivial, hyW⟩
  have : Nonempty W := ⟨⟨_, hyW⟩⟩
  have hxr : Set.range x ⊆ Set.range t := by
    rw [hx, hrange]
    simpa using hgen
  have hyr : Set.range y ⊆ Set.range t := by
    rintro _ ⟨z, rfl⟩
    rw [hrange, Subsingleton.elim z (IsLocalRing.closedPoint K')]
    exact hyW
  obtain ⟨gx, hgx⟩ := exists_ringHom t x hxr
  obtain ⟨gy, hgy⟩ := exists_ringHom t y hyr
  have hinj : Function.Injective gx := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hne : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W))).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa [PrimeSpectrum.mem_basicOpen] using hr0⟩
    have hop : IsOpen (t '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W)))) :=
      t.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen r).isOpen
    have hg2 : genericPoint S ∈ t '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(S, W))) := by
      rw [(genericPoint_spec S).mem_open_set_iff hop]
      obtain ⟨q, hq⟩ := hne
      exact ⟨_, trivial, q, hq, rfl⟩
    obtain ⟨q, hq, hqe⟩ := hg2
    have hxpt : x (IsLocalRing.closedPoint K) = genericPoint S := by
      have hm : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rw [hx] at hm
      exact hm
    have hq2 : q = Spec.map (CommRingCat.ofHom gx) (IsLocalRing.closedPoint K) := by
      apply t.isOpenEmbedding.injective
      rw [hqe, ← hxpt, ← hgx]
      rfl
    rw [hq2] at hq
    apply (PrimeSpectrum.mem_basicOpen _ _).1 hq
    show r ∈ (PrimeSpectrum.comap gx (IsLocalRing.closedPoint K)).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hr]
    exact zero_mem _
  have H0 : IsPullback (pullback.fst P.A.hom t) (pullback.snd P.A.hom t) P.A.hom t :=
    IsPullback.of_hasPullback _ _
  obtain ⟨n, -, m, σ, hlb, hva⟩ := polAV_veryAmpleBy hLaws.polBaseChange S P Γ(S, W) t _ _ _ H0
  have : Smooth P.A.hom := by
    have := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g P.A.hom
  have hproj : IsProjBy (pullback.snd P.A.hom t) := ⟨_, hlb, m, σ, hva⟩
  obtain ⟨F⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj Γ(S, W) _ (pullback.snd P.A.hom t) inferInstance hproj
    (N.pull (pullback.fst P.A.hom t)) (LB.isLB_pull hN _)
  obtain ⟨πx, hπx, hex⟩ := exists_isPullback P.A.hom t (Spec.map (CommRingCat.ofHom gx)) x hgx
  obtain ⟨πy, hπy, hey⟩ := exists_isPullback P.A.hom t (Spec.map (CommRingCat.ofHom gy)) y hgy
  obtain ⟨v, hv, hker⟩ := (exists_sec_iff F gx hπx hex).1 ⟨s, hs⟩
  obtain ⟨v', hv', hker'⟩ := exists_ker_ne_zero gx gy hinj F.D₀ v hv hker
  exact (exists_sec_iff F gy hπy hey).2 ⟨v', hv', hker'⟩

end GlobalTheory.GenericSection
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_ne_zero_fibre_of_generic_section : Out.Laws → ∀ (S : Scheme.{0}) [IsIntegral S] (P : Out.PolAV S) (N : LB P.A.left) (K K' : Type) [Field K] [Field K'] (x : Sp K ⟶ S) (y : Sp K' ⟶ S) (s : (N.pull (pullback.fst P.A.hom x)).Sec), N.IsLB → Set.range x = {genericPoint S} → (∃ j, s.f j ≠ 0) → ∃ (s' : (N.pull (pullback.fst P.A.hom y)).Sec) (j : _), s'.f j ≠ 0 := by
  first | exact @GlobalTheory.GenericSection.exists_sec_ne_zero_of_generic | exact GlobalTheory.GenericSection.exists_sec_ne_zero_of_generic | (intros; apply GlobalTheory.GenericSection.exists_sec_ne_zero_of_generic <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_ample_geometricFibres_abelianScheme : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), Out.RelAmple (Over.mk (pullback.snd P.A.hom y)) (M.pull (pullback.fst P.A.hom y))) → Out.RelAmple P.A M := by
  first | exact @GlobalTheory.FibreAmple.relAmple_of_geometricFibres | exact GlobalTheory.FibreAmple.relAmple_of_geometricFibres | (intros; apply GlobalTheory.FibreAmple.relAmple_of_geometricFibres <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleSpecialisation

theorem exists_sec_ne_zero_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (hs : ∃ s : LB.Sec B, ∃ j, s.f j ≠ 0) : ∃ s : LB.Sec A, ∃ j, s.f j ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, b, hb⟩ := hs
  refine ⟨DVR.secOfIso t hu hA hB, ?_⟩
  by_contra hn
  push Not at hn
  refine hb (fn_ext fun y hy => ?_)
  obtain ⟨a, ha⟩ := exists_chart hA y
  have e := (DVR.secOfIso_spec t hu hA hB a b).symm
  rw [hn a] at e
  have e' := (DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans
    (map_zero _))
  have e'' := (Units.mul_right_eq_zero _).1 e'
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b := ⟨ha, hy⟩
  refine (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)
  rw [gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]

theorem lbIso_pull_div_lbPow {X Y : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (f : Y ⟶ X) (a : ℕ) :
    LBIso ((LB.div (lbPow M a) L).pull f) (LB.div (lbPow (M.pull f) a) (L.pull f)) := by
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hp' : (lbPow (M.pull f) a).IsLB := LB.isLB_linComb (pull_isLB hM f) _ _
  refine (CechPic.cls_eq_iff (pull_isLB (LB.isLB_div hp hL) f) (LB.isLB_div hp' (pull_isLB hL f))).1 ?_
  rw [CechPic.cls_pull (LB.isLB_div hp hL), CechPic.cls_div hp hL, CechPic.cls_div hp' (pull_isLB hL f),
    CechPic.cls_lbPow hM, CechPic.cls_lbPow (pull_isLB hM f), CechPic.cls_pull hM, CechPic.cls_pull hL,
    map_sub, map_nsmul]

def baseChange {S S' : Scheme.{0}} (P : Out.PolAV S) (f : S' ⟶ S) : Out.PolAV S' where
  A := (Over.pullback f).obj P.A
  isAb := Out.TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (isGrpPullback_pullback P.A f).1 P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
  ktriv := by
    obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
    exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv

theorem relAmple_of_genericFibre : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (P : Out.PolAV S) (M : LB P.A.left) (K : Type) [Field K] (x : Sp K ⟶ S), M.IsLB → Set.range x = {genericPoint S} → Out.RelAmple ((Over.pullback x).obj P.A) (M.pull (pullback.fst P.A.hom x)) → Out.RelAmple P.A M := by
  intro hL _ S _ _ P M K _ x hM hx hamp
  have hne : Nonempty (baseChange P x).A.left :=
    ⟨eSec (baseChange P x).A (Classical.arbitrary (Sp K))⟩
  obtain ⟨a, s, ha, hs⟩ := GlobalTheory.T.exists_sec_relAmplePow_div_ne_zero K (baseChange P x).A (baseChange P x).L (M.pull (pullback.fst P.A.hom x))
    (baseChange P x).isAb.proper hne (baseChange P x).isLB (pull_isLB hM _) hamp
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hN := LB.isLB_div hp P.isLB
  have hN' : ∀ {Y : Scheme.{0}} (f : Y ⟶ P.A.left), (LB.div (lbPow (M.pull f) a) (P.L.pull f)).IsLB := fun f =>
    LB.isLB_div (LB.isLB_linComb (pull_isLB hM f) _ _) (pull_isLB P.isLB f)
  obtain ⟨t, ht⟩ := exists_sec_ne_zero_of_lbIso (pull_isLB hN _) (hN' _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom x) a) ⟨s, hs⟩
  refine GlobalTheory.T.relAmple_of_ample_geometricFibres_abelianScheme hL S P M hM fun K' _ _ y => ?_
  obtain ⟨t', ht'⟩ := exists_sec_ne_zero_of_lbIso (hN' _) (pull_isLB hN _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom y) a).symm
    (GlobalTheory.T.exists_section_ne_zero_fibre_of_generic_section hL S P _ K K' x y t hN hx ht)
  obtain ⟨r, u, hu⟩ := GlobalTheory.T.exists_sections_cover_cube_effective_abelianVariety GlobalTheory.T.cube_theorem_and_sections_finite_growth_abelianVariety.1 K' (baseChange P y) _ t' (hN' _) ht'
  exact GlobalTheory.T.relAmple_of_cube_div_generated_field K' (baseChange P y).A (baseChange P y).L (M.pull (pullback.fst P.A.hom y)) a r u
    (baseChange P y).isAb.proper (baseChange P y).isLB (pull_isLB hM _) ha (baseChange P y).ample hu

end GlobalTheory.AmpleSpecialisation
end
end
