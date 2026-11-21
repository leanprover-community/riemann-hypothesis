import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomOfTest
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzero
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisOfFormEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong
import BuildAid.ForwardExisting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorNormalisedMulByNIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSectionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClassicalPointOfLargeTest
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointSpecialFibreSectionNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalLiftOfSmooth
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localThetaSection_fibreNonzero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), Q.LocTheta → ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.FibNe N σ := by
  first | exact @GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe | exact GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe | (intros; apply GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ThetaLine
open GlobalTheory.Points

variable {B : Scheme.{0}} (A : Over B) (L : LB A.left) (a : ℤ)

theorem le_chart {T : Over B} {K : Type} [CommRing K] (q : Sp K ⟶ (T ⊗ A).left) (j : L.ι)
    (h : Set.range (q ≫ (snd T A).left) ⊆ L.U j) : ⊤ ≤ q ⁻¹ᵁ (LPow A L a T).U (fun _ => j) :=
  fun y _ => Set.mem_iInter.2 fun _ => h ⟨y, rfl⟩

theorem valR_pull [GrpObj A] {T T' : Over B} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} (H : IsPullSec A L a h hh s s')
    {K : Type} [CommRing K] (q : Sp K ⟶ (T' ⊗ A).left) (j : Fin 1 → L.ι) (hq : ⊤ ≤ q ⁻¹ᵁ (LPow A L a T').U j) :
    valR q _ (s'.f j) = valR (q ≫ h.left) _ (s.f j) := by
  rw [H j, valR_res q _ hq, valR_comp]

theorem valR_of_basis {Ω : Type} [CommRing Ω] (t : Sp Ω ⟶ B) {m : ℕ} (hm : m = 1)
    {b : Fin m → LB.Sec (LPow A L a (Over.mk t))} (hb : IsSecBasis _ b) :
    ∃ b₀ : LB.Sec (LPow A L a (Over.mk t)), ∀ s : LB.Sec (LPow A L a (Over.mk t)), ∃ c : Ω,
      ∀ (K : Type) [CommRing K] (β : Ω →+* K) (q : Sp K ⟶ (Over.mk t ⊗ A).left) (j : Fin 1 → L.ι),
        q ≫ (fst (Over.mk t) A).left = spMap β → ⊤ ≤ q ⁻¹ᵁ (LPow A L a (Over.mk t)).U j →
        valR q _ (s.f j) = β c * valR q _ (b₀.f j) := by
  subst hm
  refine ⟨b 0, fun s => ?_⟩
  obtain ⟨r, hr, -⟩ := hb s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (r 0), fun K _ β q j hq hj => ?_⟩
  rw [hr j, Fin.sum_univ_one, valR_mul q _ hj, valR_res q _ hj]
  congr 1
  have e := valR_comp q (fst (Over.mk t) A).left ⊤ (r 0)
  refine e.symm.trans ?_
  rw [hq]
  have e2 := valR_specMap (C := K) (A := CommRingCat.of Ω) (CommRingCat.ofHom β)
    ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (r 0))
  refine Eq.trans ?_ e2
  exact congrArg (valR (spMap β) ⊤) ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom_inv_id_apply (r 0)).symm

theorem valR_ne_zero [GrpObj A] {T : Over B} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s z τ v) {K : Type} [Field K] (x : Sp K ⟶ T.left) (j : L.ι)
    (hj : Set.range (x ≫ z.left) ⊆ L.U j) (hv : valR x ⊤ v ≠ 0) :
    valR (x ≫ (ptSecT A z).left) _ (s.f fun _ => j) ≠ 0 := by
  have hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => z.left) (fun _ => j) :=
    fun y _ => Set.mem_iInter.2 fun _ => hj ⟨y, rfl⟩
  have e := congrArg (valR x _) (H fun _ => j)
  rw [valR_res x _ hx, valR_mul x _ hx, valR_res x _ hx] at e
  rw [valR_comp]
  refine e.trans_ne (mul_ne_zero hv ?_)
  rw [valR_eq x _ hx]
  exact ((τ.s fun _ => j).isUnit.map _).ne_zero

end GlobalTheory.ZH.ThetaLine

open GlobalTheory.Points GlobalTheory.ZH.ThetaLine in

theorem GlobalTheory.ZH.sec_generic_eq_mul_theta : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)))), ∃ c : Ω, ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → Set.range (q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → valF q _ (s.f fun _ => jP) = β c * valF r _ (ρ.th₁.f fun _ => jP) := by
  intro _ hL2 o Ω _ _ _ _ S ρ s
  let t₀ : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom
  let h : (Over.mk t₀ : Over (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk t₀ (Category.comp_id t₀)
  obtain ⟨th, hth⟩ : ∃ th, IsPullSec ρ.P.A ρ.P.L 1 (h ▷ ρ.P.A) (whiskerRight_snd h ρ.P.A) ρ.th₁ th :=
    (GlobalTheory.LN.PolFrames.exists_pullSec ρ.P.A ρ.P.L 1 h ρ.th₁).imp fun _ H => H.1
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow hL2.secTwist ρ.P 1 le_rfl Ω t₀
  obtain ⟨b₀, hb₀⟩ := valR_of_basis ρ.P.A ρ.P.L 1 t₀ (one_pow _) hb
  obtain ⟨c, hc⟩ := hb₀ s
  obtain ⟨d, hd⟩ := hb₀ th
  have hd0 : d ≠ 0 := by
    obtain ⟨a, ha⟩ := S.th_ne
    obtain ⟨j, hj⟩ := exists_chart ρ.P.isLB ((t₀ ≫ (ρ.pt a).left) (IsLocalRing.closedPoint Ω))
    have hj' : Set.range (t₀ ≫ (ρ.pt a).left) ⊆ ρ.P.L.U j := by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint Ω)]
      exact hj
    have hne := valR_ne_zero ρ.P.A ρ.P.L 1 (ρ.th_val a) t₀ j hj'
      ((valR_specMap (C := Ω) (A := CommRingCat.of S.R) (CommRingCat.ofHom S.R.val.toRingHom) _).trans_ne ha)
    let x : Sp Ω ⟶ ((Over.mk t₀ : Over (Sp S.R)) ⊗ ρ.P.A).left := (ptSecT ρ.P.A (h ≫ ρ.pt a)).left
    have hx1 : x ≫ (fst (Over.mk t₀ : Over (Sp S.R)) ρ.P.A).left = spMap (RingHom.id Ω) :=
      (congrArg CommaMorphism.left (lift_fst (𝟙 (Over.mk t₀ : Over (Sp S.R))) (h ≫ ρ.pt a))).trans (Spec.map_id _).symm
    have hx2 : x ≫ (snd (Over.mk t₀ : Over (Sp S.R)) ρ.P.A).left = t₀ ≫ (ρ.pt a).left :=
      congrArg CommaMorphism.left (lift_snd (𝟙 (Over.mk t₀ : Over (Sp S.R))) (h ≫ ρ.pt a))
    have hx3 : x ≫ (h ▷ ρ.P.A).left = t₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left := by
      have : ptSecT ρ.P.A (h ≫ ρ.pt a) ≫ h ▷ ρ.P.A = h ≫ ptSecT ρ.P.A (ρ.pt a) := by
        simp [ptSecT]
      exact congrArg CommaMorphism.left this
    have hxj := le_chart ρ.P.A ρ.P.L 1 x j (hx2 ▸ hj')
    rintro rfl
    apply hne
    rw [← hx3, ← valR_pull ρ.P.A ρ.P.L 1 hth x _ hxj, hd Ω _ x _ hx1 hxj, map_zero, zero_mul]
  refine ⟨c / d, fun K _ β q r j hq hr hj => ?_⟩
  have hqj := le_chart ρ.P.A ρ.P.L 1 q j hj
  have hrq : r = q ≫ (h ▷ ρ.P.A).left := by
    have h2 : r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left =
        (q ≫ (h ▷ ρ.P.A).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left := by
      rw [hr, Category.assoc, ← Over.comp_left, whiskerRight_snd]
    have w : (fst (baseOver (Sp S.R)) ρ.P.A).left =
        (snd (baseOver (Sp S.R)) ρ.P.A).left ≫ ρ.P.A.hom :=
      (Category.comp_id _).symm.trans (pullback.condition (f := 𝟙 (Sp S.R)) (g := ρ.P.A.hom))
    refine pullback.hom_ext (f := 𝟙 (Sp S.R)) (g := ρ.P.A.hom) ?_ h2
    change r ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left = _ ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left
    rw [w, ← Category.assoc, h2]
    simp only [Category.assoc]
  change valR q _ _ = β (c / d) * valR r _ _
  rw [hrq, ← valR_pull ρ.P.A ρ.P.L 1 hth q _ hqj, hc K β q _ hq hqj, hd K β q _ hq hqj, map_div₀,
    ← _root_.mul_assoc, div_mul_cancel₀ _ ((map_ne_zero β).2 hd0)]

end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_generic_eq_mul_theta_alt : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)))), ∃ c : Ω, ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → Set.range (q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → valF q _ (s.f fun _ => jP) = β c * valF r _ (ρ.th₁.f fun _ => jP) := by
  atlas_forward_decl GlobalTheory.ZH.sec_generic_eq_mul_theta
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GenSec
open GlobalTheory.Points

theorem sec_up {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w)
    (hL : L.IsLB) (hL' : L'.IsLB) (m : Y ⟶ X') (p : Y ⟶ X) (hp : m ≫ F = p) (τ : ∀ k, Γ(Y, m ⁻¹ᵁ L'.U k))
    (hτ : ∀ (y : Y) k k', m y ∈ L'.U k → m y ∈ L'.U k' →
      gs (𝟙 Y) y _ (τ k) = (gm m y (L'.U k ⊓ L'.U k') (L'.g k k')).val * gs (𝟙 Y) y _ (τ k')) :
    ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => 1)),
      ∀ (K : Type) [Field K] (q : Sp K ⟶ Y) j k, ⊤ ≤ (q ≫ m) ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k) →
        valR q _ (s.f fun _ => j) = valR (q ≫ m) _ (w.s (fun _ => j, k)).val * valR q _ (τ k) := by
  subst hp
  let W : L.ι → L'.ι → Y.Opens := fun j k => m ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k)
  have leU : ∀ (J : Fin 1 → L.ι) k, W (J 0) k ≤ LB.wchart L (fun _ : Fin 1 => m ≫ F) J := fun J k y hy =>
    Set.mem_iInter.2 fun i => by
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact mem_pull.1 hy.1
  have leT : ∀ j k, W j k ≤ m ⁻¹ᵁ L'.U k := fun j k y hy => hy.2
  let u : ∀ j k, Γ(Y, W j k) := fun j k =>
    (m.app ((L.pull F).U (fun _ => j) ⊓ L'.U k)).hom (w.s (fun _ => j, k)).val * resG Y (leT j k) (τ k)
  have hu : ∀ j k (y : Y), y ∈ W j k → gs (𝟙 Y) y _ (u j k) = (gw w m y j k).val * gs (𝟙 Y) y _ (τ k) :=
    fun j k y hy => (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_pull (𝟙 Y) m y _ hy _).trans (by rw [Category.id_comp]; exact gs_unit m y _ hy _)) (gs_res _ y _ hy _))
  have glue : ∀ J : Fin 1 → L.ι, ∃ a : Γ(Y, LB.wchart L (fun _ : Fin 1 => m ≫ F) J),
      ∀ k, resG Y (leU J k) a = u (J 0) k := by
    intro J
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' (W (J 0)) (LB.wchart L (fun _ : Fin 1 => m ≫ F) J)
      (fun k => homOfLE (leU J k)) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' (m y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.2 (Set.mem_iInter.1 hy 0), hk⟩) (u (J 0))
      (fun k k' => fn_ext (V := W (J 0) k ⊓ W (J 0) k') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        have hj : F (m y) ∈ L.U (J 0) := mem_pull.1 hy.1.1
        rw [hu _ _ y hy.1, hu _ _ y hy.2, hτ y k k' hy.1.2 hy.2.2, hw _ m y _ _ k k' hj hj hy.1.2 hy.2.2,
          gm_self hL (m ≫ F) y hj, _root_.one_mul, ← _root_.mul_assoc, ← Units.val_mul, mul_right_comm,
          inv_mul_cancel, _root_.one_mul])
    exact ⟨a, ha⟩
  choose a ha using glue
  refine ⟨⟨a, fun J J' => fn_ext fun y hy => ?_⟩, fun K _ q j k hq => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' (m y)
    have hj : F (m y) ∈ L.U (J 0) := Set.mem_iInter.1 hy.1 0
    have hj' : F (m y) ∈ L.U (J' 0) := Set.mem_iInter.1 hy.2 0
    have key : ∀ I : Fin 1 → L.ι, F (m y) ∈ L.U (I 0) →
        gs (𝟙 Y) y _ (a I) = (gw w m y (I 0) k).val * gs (𝟙 Y) y _ (τ k) := fun I hI => by
      have hy' : y ∈ W (I 0) k := ⟨mem_pull.2 hI, hk⟩
      exact (gs_res (𝟙 Y) y (leU I k) hy' _).symm.trans ((congrArg (gs (𝟙 Y) y _) (ha I k)).trans (hu _ _ y hy'))
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y J J' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (key J hj).trans (Eq.trans ?_ (congrArg _ (key J' hj')).symm)
    rw [hw _ m y _ _ k k hj hj' hk hk, gm_self hL' m y hk, inv_one, _root_.mul_one, Units.val_mul, _root_.mul_assoc,
      Fin.prod_univ_one, zpow_one, Category.id_comp]
  · have hq' : ⊤ ≤ q ⁻¹ᵁ W j k := hq
    refine (valR_res q (leU (fun _ => j) k) hq' _).symm.trans ((congrArg (valR q _) (ha (fun _ => j) k)).trans ?_)
    exact (valR_mul q _ hq' _ _).trans (congrArg₂ (· * ·) (valR_comp q m _ _).symm (valR_res q _ hq' _))

theorem sec_up_secOn {X X' Y G : Scheme.{0}} {L : LB X} {M : LB G} {F : X' ⟶ X} {φ : X' ⟶ G}
    {w : LB.Iso (M.pull φ) (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hM : M.IsLB) (m : Y ⟶ X') (p : Y ⟶ X)
    (hp : m ≫ F = p) (V : G.Opens) (hV : ∀ y, (m ≫ φ) y ∈ V)
    (σ : ∀ j, Γ(G, V ⊓ (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 G) (fun _ => 1)).U j))
    (hσ : σ ∈ secOn (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 G) (fun _ => 1)) V) :
    ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => 1)),
      ∀ (K : Type) [Field K] (q : Sp K ⟶ Y) j k, Set.range ((q ≫ m) ≫ F) ⊆ L.U j → Set.range ((q ≫ m) ≫ φ) ⊆ M.U k →
        valR q _ (s.f fun _ => j) =
          valR (q ≫ m) _ (w.s (fun _ => j, fun _ => k)).val * valR ((q ≫ m) ≫ φ) _ (σ fun _ => k) := by
  let O : LB G := LB.LinComb M (K := Fin 1) (fun _ => 𝟙 G) (fun _ => 1)
  have le : ∀ k : PUnit → M.ι, m ⁻¹ᵁ (M.pull φ).U k ≤ (m ≫ φ) ⁻¹ᵁ (V ⊓ O.U fun _ => k PUnit.unit) :=
    fun k y hy => ⟨hV y, Set.mem_iInter.2 fun _ => (mem_pull (F := φ) (x := m y)).1 hy⟩
  have val : ∀ (y : Y) (k : PUnit → M.ι), m y ∈ (M.pull φ).U k →
      gs (𝟙 Y) y _ (((m ≫ φ).appLE _ _ (le k)).hom (σ fun _ => k PUnit.unit)) =
        gs (m ≫ φ) y _ (σ fun _ => k PUnit.unit) := fun y k hk =>
    (gs_res (𝟙 Y) y (le k) hk _).trans ((gs_pull (𝟙 Y) (m ≫ φ) y _ (le k hk) _).trans (by rw [Category.id_comp]))
  obtain ⟨s, hs⟩ := sec_up ((isGen_iff w).1 hw) hL (pull_isLB hM φ) m p hp
    (fun k => ((m ≫ φ).appLE _ _ (le k)).hom (σ fun _ => k PUnit.unit)) (fun y k k' hk hk' => by
      have hm : (m ≫ φ) y ∈ (V ⊓ O.U fun _ => k PUnit.unit) ⊓ O.U fun _ => k' PUnit.unit := ⟨le k hk, (le k' hk').2⟩
      have hm' : (m ≫ φ) y ∈ (O.U fun _ => k PUnit.unit) ⊓ O.U fun _ => k' PUnit.unit := ⟨hm.1.2, hm.2⟩
      rw [val y k hk, val y k' hk', gm_pull_g M φ m y k k' hk hk']
      refine (gs_res _ y _ hm _).symm.trans ((congrArg (gs (m ≫ φ) y _) (hσ _ _)).trans ((gs_mul _ y _ hm _ _).trans
        (congrArg₂ (· * ·) ((gs_res _ y _ hm _).trans ((gs_unit _ y _ hm' _).trans (congrArg Units.val
          ((gm_linComb M _ _ (m ≫ φ) y _ _ hm.1.2 hm.2).trans ?_)))) (gs_res _ y _ hm _))))
      rw [Fin.prod_univ_one, zpow_one, Category.comp_id])
  refine ⟨s, fun K _ q j k hj hk => ?_⟩
  have hk' : ⊤ ≤ q ⁻¹ᵁ (m ⁻¹ᵁ (M.pull φ).U fun _ => k) := fun z _ => mem_pull.2 (hk ⟨z, rfl⟩)
  refine (hs K q j (fun _ => k) fun z hz => ⟨mem_pull.2 (hj ⟨z, rfl⟩), hk' hz⟩).trans (congrArg _ ?_)
  exact (valR_appLE q (m ≫ φ) (le fun _ => k) hk' _).trans (by rw [Category.assoc])

theorem exists_generic_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (eta : Sp Ω ⟶ U₀.toScheme), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → (N : Set M.Z).Nonempty → eta ≫ U₀.ι = M.pt → ∃ s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R))), ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (jP : ρ.P.L.ι) (jL : Q.L.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → g ≫ pullback.fst _ _ = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → g ≫ pullback.snd _ _ = spMap β ≫ eta → Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL → valF q _ (s.f fun _ => jP) = valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val * valF (g ≫ Q.φ) _ (σ fun _ => jL) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q N σ eta hσ hN heta
  have hw : (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left ≫ ρ.P.A.hom =
      ((fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left ≫ eta) ≫ Q.u₀ := by
    rw [Category.assoc, Q.u₀_gen eta heta, Over.w]
    exact (Over.w (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A)).symm
  have hc : Q.φ ≫ Q.G.hom = pullback.snd ρ.P.A.hom Q.u₀ ≫ U₀.ι := Q.cart.1.w
  have hb : (pullback.lift _ _ hw ≫ Q.φ) ≫ Q.G.hom =
      (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left ≫ M.pt := by
    rw [Category.assoc, hc, pullback.lift_snd_assoc, Category.assoc, heta]
  obtain ⟨s, hs⟩ := sec_up_secOn Q.w_gen ρ.P.isLB Q.L.isLB (pullback.lift _ _ hw) _ (pullback.lift_fst _ _ _)
    (Q.G.hom ⁻¹ᵁ N) (fun y => by
      show ((pullback.lift _ _ hw ≫ Q.φ) ≫ Q.G.hom) y ∈ N
      rw [hb]
      exact M.top_le_preimage_pt hN (x := (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left y)
        trivial) σ hσ
  refine ⟨s, fun K _ β q g jP jL h₁ h₂ h₃ hP hL => ?_⟩
  obtain rfl : g = q ≫ pullback.lift _ _ hw := by
    refine pullback.hom_ext ?_ ?_
    · rw [h₂, Category.assoc, pullback.lift_fst]
    · rw [h₃, Category.assoc, pullback.lift_snd, ← Category.assoc, h₁]
  exact hs K q jP jL hP hL

end GlobalTheory.ZH.GenSec
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFibre_section_of_model_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (eta : Sp Ω ⟶ U₀.toScheme), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → (N : Set M.Z).Nonempty → eta ≫ U₀.ι = M.pt → ∃ s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R))), ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (jP : ρ.P.L.ι) (jL : Q.L.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → g ≫ pullback.fst _ _ = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → g ≫ pullback.snd _ _ = spMap β ≫ eta → Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL → valF q _ (s.f fun _ => jP) = valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val * valF (g ≫ Q.φ) _ (σ fun _ => jL) := by
  atlas_forward_decl GlobalTheory.ZH.GenSec.exists_generic_section
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsReg
open GlobalTheory.Points

theorem valR_appIso_inv {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (U : X.Opens) (f : Γ(X, U))
    {C : Type} [CommRing C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    valR (y ≫ j) (j ''ᵁ U) ((j.appIso U).inv.hom f) = valR y U f := by
  rw [← valR_appLE y j (j.preimage_image_eq U).ge hy, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res y le_rfl hy f

theorem valR_valueAt {B : Scheme.{0}} (A : Over B) (L : LB A.left) (a : ℤ) [GrpObj A] {T : Over B}
    {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s z τ v) {K : Type} [CommRing K] (x : Sp K ⟶ T.left) (j : L.ι)
    (hj : Set.range (x ≫ z.left) ⊆ L.U j) :
    valR (x ≫ (ptSecT A z).left) _ (s.f fun _ => j) = valR x ⊤ v * valR x _ (τ.s fun _ => j).val := by
  have hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => z.left) (fun _ => j) :=
    fun y _ => Set.mem_iInter.2 fun _ => hj ⟨y, rfl⟩
  have e := congrArg (valR x _) (H fun _ => j)
  rw [valR_res x _ hx, valR_mul x _ hx, valR_res x _ hx] at e
  rw [valR_comp]
  exact e

theorem range_subset {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) {U : X.Opens} (p : Sp K) (h : x p ∈ U) :
    Set.range x ⊆ U := by
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y p]
  exact h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem exists_eq_mul_unit (hne : (U₀ : Set M.Z).Nonempty) {N : M.Z.Opens} {σ : Q.SecFam N} {c : Ω}
    (hσ : Q.ThMul c N σ) {a : S.Gam} {W : M.Z.Opens} {h : W.toScheme ⟶ Q.G.left} {w : W.toScheme}
    (hE : Q.ExtPt a W h) (hF : Q.FrameUnit a W h w) (hw : W.ι w ∈ N) (jL : Q.L.L.ι) (hj : h w ∈ Q.L.L.U jL) :
    ∃ (T : M.Z.Opens) (f : Γ(M.Z, T)) (e : Ω), W.ι w ∈ T ∧ e ≠ 0 ∧ e ∈ M.O (W.ι w) ∧ e⁻¹ ∈ M.O (W.ι w) ∧
      c * S.th a = valF M.pt T f * e⁻¹ ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ W.toScheme), Set.range y = {w} →
        valF (y ≫ W.ι) T f = valF (y ≫ h) _ (σ fun _ => jL) := by
  let V : W.toScheme.Opens := h ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U fun _ => jL)
  have hwV : w ∈ V := by
    refine ⟨?_, Set.mem_iInter.2 fun _ => hj⟩
    change (h ≫ Q.G.hom) w ∈ N
    rw [hE.1]
    exact hw
  have hT : W.ι w ∈ W.ι ''ᵁ V := ⟨w, hwV, rfl⟩
  have hval : ∀ (K : Type) [Field K] (y : Sp K ⟶ W.toScheme), ⊤ ≤ y ⁻¹ᵁ V →
      valF (y ≫ W.ι) (W.ι ''ᵁ V) ((W.ι.appIso V).inv.hom ((h.app _).hom (σ fun _ => jL))) =
        valF (y ≫ h) _ (σ fun _ => jL) := fun K _ y hy =>
    (valR_appIso_inv W.ι V _ y hy).trans (valR_comp y h _ _).symm
  have lift : ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → ∃ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt := fun U hU =>
    ⟨IsOpenImmersion.lift U.ι M.pt (by
      rw [Scheme.Opens.range_ι]
      exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hU)), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨x, hx⟩ := lift W ⟨w.1, w.2⟩
  obtain ⟨x₀, hx₀⟩ := lift U₀ hne
  let t₀ : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom
  have hcond : (t₀ ≫ (ρ.pt a).left) ≫ ρ.P.A.hom = x₀ ≫ Q.u₀ := by
    rw [Q.u₀_gen x₀ hx₀, Category.assoc, Over.w (ρ.pt a)]
    exact Category.comp_id _
  let x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀ := pullback.lift _ _ hcond
  have h1 : x' ≫ pullback.fst _ _ = t₀ ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
  have h2 : x' ≫ pullback.snd _ _ ≫ U₀.ι = M.pt := by
    rw [← Category.assoc, pullback.lift_snd, hx₀]
  have h3 : x' ≫ Q.φ ≫ Q.G.hom = M.pt := by
    rw [← h2]
    exact congrArg (x' ≫ ·) Q.cart.1.w
  have h4 : x ≫ h = x' ≫ Q.φ := hE.2 x x' hx h3 h1
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := by
    have h5 := M.top_le_preimage_pt ⟨_, hT⟩
    rw [← hx] at h5
    exact le_preimage_mono x (W.ι.preimage_image_eq V).le h5
  have hxh : Set.range (x' ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U fun _ => jL : Q.G.left.Opens) := by
    rw [← h4]
    exact (top_le_preimage_iff _ _).1 hxV
  obtain ⟨jP, hjP⟩ : ∃ jP, Set.range (t₀ ≫ (ρ.pt a).left) ⊆ ρ.P.L.U jP := by
    have h5 : (t₀ ≫ (ρ.pt a).left) (IsLocalRing.closedPoint Ω) ∈ ⨆ i, ρ.P.L.U i := by
      rw [ρ.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h5
    exact ⟨i, range_subset _ _ hi⟩
  obtain ⟨he0, he1, he2⟩ := hF jP jL x' _ hj h3 h1 (h1 ▸ hjP) rfl
  refine ⟨_, _, _, hT, he0, he1, he2, ?_, fun K _ y hy => hval K y fun p _ => ?_⟩
  · have hr : (t₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left =
        x' ≫ pullback.fst _ _ := by
      rw [h1, Category.assoc, ← Over.comp_left, ptSecT, lift_snd]
    have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := Spec.map_id _
    have e := hσ Ω (RingHom.id Ω) x' _ jP jL (by rw [h2, hid, Category.id_comp]) hr (h1 ▸ hjP)
      (fun p hp => Set.mem_iInter.1 (hxh hp).2 0) (fun p hp => (hxh hp).1)
    have e2 := valR_valueAt ρ.P.A ρ.P.L 1 (ρ.th_val a) t₀ jP hjP
    have e3 : valR (X := (baseOver (Sp S.R)).left) t₀ ⊤ (fn (⟨S.th a, S.th_mem a⟩ : S.R)) = S.th a :=
      valR_specMap (C := Ω) (A := CommRingCat.of S.R) (CommRingCat.ofHom S.R.val.toRingHom) _
    rw [e3] at e2
    rw [Fintype.sum_unique, zpow_one, RingHom.id_apply, valF_eq_valR, e2, ← h4, ← hval Ω x hxV, hx] at e
    have hn := (div_ne_zero_iff.1 he0).1
    rw [inv_div, ← mul_div_assoc, eq_div_iff hn, _root_.mul_assoc, _root_.mul_comm (valF M.pt _ _)]
    exact e
  · have h5 : y p ∈ Set.range y := ⟨p, rfl⟩
    rw [hy] at h5
    change y p ∈ V
    rw [show y p = w from h5]
    exact hwV

end GlobalTheory.ZH.TorsReg

open GlobalTheory.Points GlobalTheory.ZH.TorsReg in

theorem GlobalTheory.ZH.mul_theta_regular_and_unit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (c : Ω), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w → W.ι w ∈ N → c * S.th a ∈ M.O (W.ι w) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι), Set.range x = {w} → valF (x ≫ h) _ (σ j) ≠ 0 → c * S.th a ≠ 0 ∧ (c * S.th a)⁻¹ ∈ M.O (W.ι w) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO N σ c _ hσ a W h w hE hF hw
  constructor
  · have h5 : h w ∈ ⨆ i, Q.L.L.U i := by
      rw [Q.L.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h5
    obtain ⟨T, f, e, hT, -, -, he, hc, -⟩ := exists_eq_mul_unit Q hO.ne hσ hE hF hw i hi
    rw [hc]
    exact mul_mem (RatModel.valF_mem_O hT f) he
  · intro K _ x j hx hv
    have hxw : x (IsLocalRing.closedPoint K) = w := by
      have h5 : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rwa [hx] at h5
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim k 0)⟩
    have hi : h w ∈ Q.L.L.U i := by
      by_contra hi
      refine hv (dif_neg fun hle => hi ?_)
      rw [← hxw]
      exact Set.mem_iInter.1 (hle (x := IsLocalRing.closedPoint K) trivial).2 0
    obtain ⟨T, f, e, hT, he0, he1, -, hc, hK⟩ := exists_eq_mul_unit Q hO.ne hσ hE hF hw i hi
    rw [← hK K x hx] at hv
    have hxw' : (x ≫ W.ι) (IsLocalRing.closedPoint K) = W.ι w := by rw [← hxw]; rfl
    have hle : ⊤ ≤ (x ≫ W.ι) ⁻¹ᵁ T := (le_preimage_iff _ _).2 (hxw' ▸ hT)
    have hb : W.ι w ∈ M.Z.basicOpen f :=
      hxw' ▸ (le_preimage_iff _ _).1 ((le_preimage_basicOpen_iff _ hle f).2 (isUnit_iff_ne_zero.2 hv))
    obtain ⟨hf0, hf1⟩ := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hT f).2 hb)
    rw [hc]
    refine ⟨mul_ne_zero hf0 (inv_ne_zero he0), ?_⟩
    rw [_root_.mul_inv, inv_inv]
    exact mul_mem hf1 he1

end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_mul_regular_and_unit_along_torsion : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (c : Ω), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w → W.ι w ∈ N → c * S.th a ∈ M.O (W.ι w) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι), Set.range x = {w} → valF (x ≫ h) _ (σ j) ≠ 0 → c * S.th a ≠ 0 ∧ (c * S.th a)⁻¹ ∈ M.O (W.ι w) := by
  first | exact @GlobalTheory.ZH.mul_theta_regular_and_unit | exact GlobalTheory.ZH.mul_theta_regular_and_unit | (intros; apply GlobalTheory.ZH.mul_theta_regular_and_unit <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem ZHPre.exists_testFac_of_large : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → ∃ jV yV yK, Q.TestFac y u jV yV yK := by
  intro o Ω _ _ _ hA S ρ M U₀ Q hO z p _ y hy
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
  have hle : S.R ≤ M.O ((gPt p ≫ y) w) := hO.le.trans (RatModel.ringOn_le_O hw)
  let y₀ : S.R →+* PadicAlgCl p :=
    (RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
  have hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a =>
    RatModel.norm_val_le_one (y := y) rfl (x := algebraMap o Ω a) ((M.O _).algebraMap_mem a)
  have hat : S.At M y y₀ := fun _ => rfl
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y (le_preimage_top y)
  haveI := hA.ft
  haveI := M.lft
  obtain ⟨t, ht⟩ := exists_finset_closure_eq_top M.s hW
  refine ⟨y₀, t.image (fun f => (((valMap y W hyW).hom f : OO p) : PadicAlgCl p)), hat, hn, fun u hu => ?_⟩
  let j : u.V →+* OO p :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).codRestrict (OO p)
      fun x => (mem_OO_iff _).2 ((u.norm_le _).2 ⟨x, rfl⟩)
  have hj : Function.Injective j := fun a b h =>
    IsFractionRing.injective u.V (FractionRing u.V)
      ((algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (congrArg Subtype.val h))
  obtain ⟨ψ, hψ⟩ := exists_factor_of_closure (valMap y W hyW).hom j hj ht (by
    intro a ha
    obtain ⟨x, hx⟩ := hu _ (Finset.mem_image_of_mem _ ha)
    obtain ⟨v, hv⟩ := (u.norm_le x).1 (by rw [hx]; exact (mem_OO_iff _).1 (Subtype.prop _))
    exact ⟨v, Subtype.ext (by rw [← hx, ← hv]; rfl)⟩)
  let yV : Sp u.V ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec
  have hfac : spMap j ≫ yV = y := by
    rw [← specMap_valMap_fromSpec hW y hyW, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    rfl
  have hg : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V ≫ yV = gPt p ≫ y := by
    have e : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V = gPt p ≫ spMap j := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    rw [← hfac, ← Category.assoc, e, Category.assoc]
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) w)]
    rw [← hg] at hw
    exact hw
  refine ⟨j, yV, IsOpenImmersion.lift U₀.ι _ hr, fun _ => rfl, hfac, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  rw [← Spec.map_preimage (IsOpenImmersion.lift U₀.ι _ hr ≫ Q.u₀)]
  congr 1
  ext a
  apply (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective
  have h1 := preimage_comp_eq_val M U₀ hO.ne S.R Q.u₀ Q.u₀_gen
    (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ IsOpenImmersion.lift U₀.ι _ hr) a
  rw [Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, hg, ← hat a, Spec.preimage_comp,
    Spec.preimage_map] at h1
  exact h1.trans (DFunLike.congr_fun u.fac a).symm

end GlobalTheory.ZH
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classical_point_factor_large_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → ∃ jV yV yK, Q.TestFac y u jV yV yK := by
  atlas_forward_decl GlobalTheory.ZH.ZHPre.exists_testFac_of_large
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

theorem exists_iso_of_existsUnique_ext {B B' : Scheme.{0}} (j : B' ⟶ B) (G G' : Over B) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hext : ∀ (G G' : Over B) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f)
    (e : (Over.pullback j).obj G ≅ (Over.pullback j).obj G') (he : IsMonHom e.hom) :
    ∃ E : G ≅ G', IsMonHom E.hom ∧ (Over.pullback j).map E.hom = e.hom := by
  obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hext G G' hG hG' e.hom he
  obtain ⟨b, ⟨hb, hb'⟩, -⟩ := hext G' G hG' hG e.inv inferInstance
  refine ⟨⟨a, b, ?_, ?_⟩, ha, ha'⟩
  · exact (hext G G hG hG (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, ha', hb', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (hext G' G' hG' hG' (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, ha', hb', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

theorem ZHPre.exists_testMap : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∃ F ψ, Q.TestMap u yV yK F ψ := by
  intro hext o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK hT
  obtain ⟨-, -, h₁, h₂⟩ := hT
  have := u.U.gen_hom
  have gp₁ : IsGrpPullback ((Over.pullback (jK u.V)).obj u.G) ρ.P.A (spMap u.yK) (u.U.gen.hom.left ≫ u.φ) :=
    ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  have gp₂ := ((isGrpPullback_pullback ((Over.pullback Q.u₀).obj ρ.P.A) yK).comp
    (isGrpPullback_pullback ρ.P.A Q.u₀)).congr h₂ rfl
  obtain ⟨e₁, m₁, he₁⟩ := grpPullback_iso gp₁ gp₂
  have gp₃ := ((((isGrpPullback_of_iso e₁).comp
    (isGrpPullback_pullback ((Over.pullback Q.u₀).obj ρ.P.A) yK)).congr (Category.id_comp _) rfl).comp Q.cart).congr h₁ rfl
  have gp₄ := (isGrpPullback_pullback ((Over.pullback yV).obj Q.G) (jK u.V)).comp (isGrpPullback_pullback Q.G yV)
  obtain ⟨e₂, m₂, he₂⟩ := grpPullback_iso gp₃ gp₄
  obtain ⟨E, mE, hE⟩ := exists_iso_of_existsUnique_ext (jK u.V) u.G ((Over.pullback yV).obj Q.G) u.semi
    (IsSemiAbelian.pullback _ Q.G Q.semi) (fun G G' _ _ => hext u.V (FractionRing u.V) G G') e₂ m₂
  refine ⟨E.hom.left ≫ pullback.fst Q.G.hom yV,
    e₁.hom.left ≫ pullback.fst ((Over.pullback Q.u₀).obj ρ.P.A).hom yK,
    ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback Q.G yV)).congr (Category.id_comp _) rfl, ?_, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans he₁
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (e₁.hom.left ≫ ·) (pullback.condition (f := ((Over.pullback Q.u₀).obj ρ.P.A).hom) (g := yK))).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ yK) (Over.w e₁.hom))
  · refine he₂.symm.trans ?_
    have a : ((Over.pullback (jK u.V)).map E.hom).left ≫ pullback.fst ((Over.pullback yV).obj Q.G).hom (jK u.V) =
        pullback.fst u.G.hom (jK u.V) ≫ E.hom.left := pullback.lift_fst _ _ _
    rw [← hE]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst Q.G.hom yV) a).trans (Category.assoc _ _ _))

end GlobalTheory.ZH
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_testMap_of_testFac : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∃ F ψ, Q.TestMap u yV yK F ψ := by
  atlas_forward_decl GlobalTheory.ZH.ZHPre.exists_testMap
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.TestBundle

open GlobalTheory.CechPic

theorem lbIso_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (P : Over (Spec (CommRingCat.of V))) [Smooth P.hom] [GeometricallyConnected P.hom]
    (e : Spec (CommRingCat.of V) ⟶ P.left) (he : e ≫ P.hom = 𝟙 _) {L M : LB P.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : CechPic.pull (pullback.fst P.hom (jK V)) (cls L hL) =
      CechPic.pull (pullback.fst P.hom (jK V)) (cls M hM)) : LBIso L M := by
  have hN := LB.isLB_div hM hL
  have h₁ : IsPreimmersion (jK V) := IsPreimmersion.of_isLocalization (nonZeroDivisors V)
  have h₂ : Flat (jK V) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors V))
  refine GenericExtend.exists_isGen_of_densePart _ _ (jK V) ((isNormalScheme_iff_pred _).1 inferInstance) h₁ h₂
    DVR.isDominant_jK inferInstance P e (LB.div M L) he ‹_› (geometricallyIntegral_of_smooth P.hom) hN
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hN _)) ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  rw [cls_pull hN, cls_div hM hL, map_sub, h, sub_self]

theorem lbIso_pull_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L := by
  intro o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK _ F ψ ⟨_, h₁, _, h₂⟩
  have := u.semi.smooth
  have := u.semi.geomConnected
  have hL := Q.L.isLB
  have hP := ρ.P.isLB
  have hA := u.A.isLB
  have hG := u.U.LG.isLB
  refine lbIso_of_generic u.G (eSec u.G) (Over.w η[u.G]) (pull_isLB hL F) hG ?_
  have a : CechPic.pull Q.φ (cls _ hL) = CechPic.pull (pullback.fst ρ.P.A.hom Q.u₀) (cls _ hP) :=
    (cls_eq_iff (pull_isLB hL _) (pull_isLB hP _)).2 ⟨Q.w, Q.w_gen⟩
  have b : cls _ hA = CechPic.pull u.φ (cls _ hP) := (cls_eq_iff hA (pull_isLB hP _)).2 u.lb
  have c : CechPic.pull u.U.gen.hom.left (cls _ hA) = CechPic.pull (pullback.fst u.G.hom (jK u.V)) (cls _ hG) :=
    (cls_eq_iff (pull_isLB hA _) (pull_isLB hG _)).2 u.U.ext
  refine Eq.trans ?_ c
  rw [cls_pull hL, ← pull_comp, ← h₂, pull_comp, a, ← pull_comp, h₁, b]
  exact pull_comp _ _ _

end GlobalTheory.ZH.TestBundle
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pullback_uniformisedThetaModel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L := by
  first | exact @GlobalTheory.ZH.TestBundle.lbIso_pull_unif | exact GlobalTheory.ZH.TestBundle.lbIso_pull_unif | (intros; apply GlobalTheory.ZH.TestBundle.lbIso_pull_unif <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ZJ.exists_torsion_lift_of_residue :
    ∀ (p : ℕ) [Fact p.Prime] (B : Scheme.{0}) (G : Over B) [GrpObj G], IsSemiAbelian G → ∀ (y : Sp (OO p) ⟶ B) (n : ℕ), IsUnit (n : Γ(B, ⊤)) → ∀ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ y) ⟶ G, t ^ n = 1 → ∃ b : Over.mk y ⟶ G, b ^ n = 1 ∧ spMap (IsLocalRing.residue (OO p)) ≫ b.left = t.left := by
  intro p _ B G _ hG y n hn t ht
  have := hG.comm
  have := hG.smooth
  have := GrpTangent.etale_torsion G hn
  have hP := GrpTangent.isPullback_torsion G n
  have e : ∀ {T : Scheme.{0}} (q : T ⟶ B), (1 : Over.mk q ⟶ G).left = q ≫ η[G].left := by
    intro T q
    rw [Hom.one_def, Over.comp_left]; rfl
  have w : t.left ≫ (mulN G n).left =
      (spMap (IsLocalRing.residue (OO p)) ≫ y) ≫ η[G].left := by
    rw [← Over.comp_left, GrpTangent.comp_mulN, ht, e]
  obtain ⟨c, hc₁, hc₂⟩ := ZJ.exists_classical_lift_of_smooth p _ _ (torsion G n).hom y
    (hP.lift _ _ w) (hP.lift_snd _ _ w)
  let b : Over.mk y ⟶ G := Over.homMk (c ≫ (torsion.ι G n).left) (by
    rw [Category.assoc, Over.w]; exact hc₁)
  refine ⟨b, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [← GrpTangent.comp_mulN, Over.comp_left, e]
    change (c ≫ (torsion.ι G n).left) ≫ _ = _
    rw [Category.assoc, hP.w, ← Category.assoc, hc₁]
  · change _ ≫ c ≫ (torsion.ι G n).left = _
    rw [← Category.assoc]
    exact (congrArg (· ≫ (torsion.ι G n).left) hc₂).trans (hP.lift_fst _ _ w)

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicLift_torsionPoint_invertibleOrder : ∀ (p : ℕ) [Fact p.Prime] (B : Scheme.{0}) (G : Over B) [GrpObj G], IsSemiAbelian G → ∀ (y : Sp (OO p) ⟶ B) (n : ℕ), IsUnit (n : Γ(B, ⊤)) → ∀ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ y) ⟶ G, t ^ n = 1 → ∃ b : Over.mk y ⟶ G, b ^ n = 1 ∧ spMap (IsLocalRing.residue (OO p)) ≫ b.left = t.left := by
  atlas_forward_decl GlobalTheory.ZJ.exists_torsion_lift_of_residue
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_point_of_inter {V K O C : Type} [CommRing V] [Field K] [CommRing O] [IsLocalRing O] [Field C]
    (i : V →+* K) (j : V →+* O) (k : K →+* C) (l : O →+* C) (hi : Function.Injective i) (hl : Function.Injective l)
    (hc : ∀ v, l (j v) = k (i v)) (hint : ∀ (a : K) (c : O), k a = l c → ∃ v, i v = a)
    {X : Scheme.{0}} (x : Sp K ⟶ X) (b : Sp O ⟶ X) (h : spMap k ≫ x = spMap l ≫ b) :
    ∃ y : Sp V ⟶ X, spMap i ≫ y = x ∧ spMap j ≫ y = b := by
  obtain ⟨U, hU, hb, -⟩ := exists_isAffineOpen_le b (le_preimage_top b)
  have hlb : ⊤ ≤ (spMap l ≫ b) ⁻¹ᵁ U := le_preimage_comp _ b hb (le_preimage_top _)
  have hx : ⊤ ≤ x ⁻¹ᵁ U := by
    have h1 : ⊤ ≤ (spMap k ≫ x) ⁻¹ᵁ U := h ▸ hlb
    intro w _
    rw [Subsingleton.elim w (spMap k (IsLocalRing.closedPoint C))]
    exact h1 (x := IsLocalRing.closedPoint C) trivial
  have hv : ∀ f, k ((valMap x U hx).hom f) = l ((valMap b U hb).hom f) := fun f => by
    rw [← valR_eq, ← valR_eq, ← valR_spMap_comp k x U hx, ← valR_spMap_comp l b U hb, h]
  choose g hg using fun f => hint _ _ (hv f)
  let ψ : Γ(X, U) →+* V :=
    { toFun := g
      map_one' := hi (by simp only [hg, map_one])
      map_mul' := fun a c => hi (by simp only [hg, map_mul])
      map_zero' := hi (by simp only [hg, map_zero])
      map_add' := fun a c => hi (by simp only [hg, map_add]) }
  have e1 : (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ CommRingCat.ofHom i = valMap x U hx := by
    ext f
    exact hg f
  have e2 : (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ CommRingCat.ofHom j = valMap b U hb := by
    ext f
    exact hl ((hc _).trans ((congrArg k (hg f)).trans (hv f)))
  refine ⟨Spec.map (CommRingCat.ofHom ψ : Γ(X, U) ⟶ CommRingCat.of V) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, e1, specMap_valMap_fromSpec]
  · rw [← Category.assoc, ← Spec.map_comp, e2, specMap_valMap_fromSpec]

theorem pushHom_inj_of_cartesian {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    Function.Injective (pushHom h T) := fun a b e =>
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w a).trans (Over.w b).symm))

theorem torsion_integral_descends : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p), (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) → ∀ b : Over.mk (spMap jV) ⟶ u.G, b ^ (S.r * S.N) = 1 → ∃ (a : S.Gam) (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) ∧ spMap jV ≫ hV = b.left := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u jV hj b hb
  haveI := u.U.gen_hom
  let k : FractionRing u.V →+* PadicAlgCl p := algebraMap _ _
  have hsq : gPt p ≫ spMap jV = spMap k ≫ jK u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => spMap φ) (RingHom.ext hj)
  have hbw : b.left ≫ u.G.hom = spMap jV := Over.w b
  let T : Over (Sp (FractionRing u.V)) := Over.mk (spMap k)
  let wl : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V) :=
    pullback.lift (gPt p ≫ b.left) (spMap k) (by rw [Category.assoc, hbw, hsq])
  have w1 : wl ≫ pullback.fst _ _ = gPt p ≫ b.left := pullback.lift_fst _ _ _
  have w2 : wl ≫ pullback.snd _ _ = spMap k := pullback.lift_snd _ _ _
  let w : T ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk wl w2
  let W : Over.mk (T.hom ≫ jK u.V) ⟶ Over.mk (spMap jV) := Over.homMk (gPt p) hsq
  have hp := isGrpPullback_pullback u.G (jK u.V)
  have e0 : pushHom hp T w = preHom W b := Over.OverMorphism.ext w1
  have hw : w ^ (S.r * S.N) = 1 := pushHom_inj_of_cartesian hp T (by
    rw [map_pow, e0, ← map_pow, hb, map_one, map_one])
  have hw' : (w ≫ u.U.gen.hom) ^ (S.r * S.N) = 1 := by
    rw [← MonObj.pow_comp, hw, MonObj.one_comp]
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) (T.hom ≫ spMap u.yK) (pushHom u.cart T (w ≫ u.U.gen.hom))
    (by rw [← map_pow, hw', map_one])
  have ha' : (spMap k ≫ spMap u.yK) ≫ (ρ.pt a).left = (wl ≫ u.U.gen.hom.left) ≫ u.φ :=
    congrArg (fun z => z.left) ha
  have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
  have hg : u.U.gen.hom.left ≫ u.A.A.hom = pullback.snd _ _ := Over.w u.U.gen.hom
  have hg' : u.U.gen.inv.left ≫ pullback.snd _ _ = u.A.A.hom := Over.w u.U.gen.inv
  have hih : u.U.gen.inv.left ≫ u.U.gen.hom.left = 𝟙 _ := congrArg (fun z => z.left) u.U.gen.inv_hom_id
  have hhi : u.U.gen.hom.left ≫ u.U.gen.inv.left = 𝟙 _ := congrArg (fun z => z.left) u.U.gen.hom_inv_id
  obtain ⟨x', x1, x2⟩ : ∃ x' : Sp (FractionRing u.V) ⟶ u.A.A.left,
      x' ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left ∧ x' ≫ u.A.A.hom = 𝟙 _ :=
    ⟨u.cart.1.lift (spMap u.yK ≫ (ρ.pt a).left) (𝟙 _) (by
      rw [Category.assoc, hpa, Category.id_comp]; exact Category.comp_id _), u.cart.1.lift_fst _ _ _,
      u.cart.1.lift_snd _ _ _⟩
  have hx' : spMap k ≫ x' = wl ≫ u.U.gen.hom.left := by
    refine u.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, x1, ← Category.assoc]
      exact ha'
    · rw [Category.assoc, x2, Category.comp_id, Category.assoc]
      exact ((congrArg (wl ≫ ·) hg).trans w2).symm
  let x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V) := x' ≫ u.U.gen.inv.left
  have hx : spMap k ≫ x = wl := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.U.gen.inv.left) hx').trans ?_)
    exact (Category.assoc _ _ _).trans ((congrArg (wl ≫ ·) hhi).trans (Category.comp_id _))
  have hxs : x ≫ pullback.snd _ _ = 𝟙 _ := (Category.assoc _ _ _).trans ((congrArg (x' ≫ ·) hg').trans x2)
  obtain ⟨hV, h1, h2⟩ := exists_point_of_inter (algebraMap u.V (FractionRing u.V)) jV k (OO p).subtype
    (IsFractionRing.injective _ _) Subtype.val_injective hj
    (fun a c e => (u.norm_le a).1 ((mem_OO_iff _).1 (by
      have e' : algebraMap _ (PadicAlgCl p) a = c := e
      rw [e']; exact c.2)))
    (x ≫ pullback.fst _ _) b.left (by rw [← Category.assoc, hx, w1])
  refine ⟨a, hV, x, ⟨?_, h1.symm, hxs, ?_⟩, h2⟩
  · rw [← Spec.map_preimage (hV ≫ u.G.hom), ← Spec.map_id]
    congr 1
    have h3 : Spec.preimage (hV ≫ u.G.hom) ≫ CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)) =
        CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc]
      refine (congrArg (· ≫ u.G.hom) h1).trans ?_
      rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, Category.id_comp]
    ext v
    exact IsFractionRing.injective u.V (FractionRing u.V) (congrArg (fun φ => φ.hom v) h3)
  · refine (Category.assoc _ _ _).trans (Eq.trans (congrArg (x' ≫ ·) ?_) x1)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.φ) hih).trans (Category.id_comp _))

end GlobalTheory.ZH
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_torsion_point_descends_to_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p), (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) → ∀ b : Over.mk (spMap jV) ⟶ u.G, b ^ (S.r * S.N) = 1 → ∃ (a : S.Gam) (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) ∧ spMap jV ≫ hV = b.left := by
  atlas_forward_decl GlobalTheory.ZH.torsion_integral_descends
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

theorem extPt_comp_eq_integral_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left), Q.ExtPt a W h → ∀ (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) → ∀ yW : Sp u.V ⟶ W.toScheme, yW ≫ W.ι = yV → yW ≫ h = hV ≫ F := by
  intro o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK hT F ψ hM a W h hE hV x hx yW hyW
  obtain ⟨-, -, hK, hK0⟩ := hT
  obtain ⟨hF, hψ1, hψ2, hψ3⟩ := hM
  obtain ⟨hh, hE⟩ := hE
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hsep : IsSeparated Q.G.hom := Q.semi.separated
  have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
  have hφ : Q.φ ≫ Q.G.hom = pullback.snd ρ.P.A.hom Q.u₀ ≫ U₀.ι := Q.cart.1.w
  have hFw : F ≫ Q.G.hom = u.G.hom ≫ yV := hF.1.w
  let sec : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
    pullback.lift (Q.u₀ ≫ (ρ.pt a).left) (𝟙 _) (by
      rw [Category.assoc, hpa]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have hs1 : sec ≫ pullback.fst _ _ = Q.u₀ ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
  have hs2 : sec ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hs3 : sec ≫ Q.φ ≫ Q.G.hom = U₀.ι := by
    rw [hφ, ← Category.assoc, hs2, Category.id_comp]
  let N : M.Z.Opens := W ⊓ U₀
  let iW : N.toScheme ⟶ W.toScheme := M.Z.homOfLE inf_le_left
  let iU : N.toScheme ⟶ U₀.toScheme := M.Z.homOfLE inf_le_right
  have hiW : iW ≫ W.ι = N.ι := M.Z.homOfLE_ι _
  have hiU : iU ≫ U₀.ι = N.ι := M.Z.homOfLE_ι _
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range N.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [← hyW]
      exact (yW (jK u.V w)).2
    · rw [← hK]
      exact (yK w).2
  let k : Sp (FractionRing u.V) ⟶ N.toScheme := IsOpenImmersion.lift N.ι (jK u.V ≫ yV) hr
  have hk : k ≫ N.ι = jK u.V ≫ yV := IsOpenImmersion.lift_fac _ _ _
  have hkW : k ≫ iW = jK u.V ≫ yW := by
    rw [← cancel_mono W.ι, Category.assoc, hiW, hk, Category.assoc, hyW]
  have hkU : k ≫ iU = yK := by
    rw [← cancel_mono U₀.ι, Category.assoc, hiU, hk, hK]
  have hne : (N : Set M.Z).Nonempty :=
    ⟨_, (k (IsLocalRing.closedPoint (FractionRing u.V))).2⟩
  have hg : Set.range M.pt ⊆ Set.range N.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let g : Sp Ω ⟶ N.toScheme := IsOpenImmersion.lift N.ι M.pt hg
  have hgN : g ≫ N.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant (g ≫ N.ι) := by rw [hgN]; infer_instance
  have : IsDominant g := IsDominant.of_comp_of_isOpenImmersion g N.ι
  have key : iW ≫ h = iU ≫ sec ≫ Q.φ := by
    refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ g ?_
    · simp only [Category.assoc]
      rw [hh, hs3, hiW, hiU]
    · have h1 : (g ≫ iU) ≫ U₀.ι = M.pt := by rw [Category.assoc, hiU, hgN]
      have := hE (g ≫ iW) (g ≫ iU ≫ sec) (by rw [Category.assoc, hiW, hgN])
        (by simp only [Category.assoc]; rw [hs3, hiU, hgN])
        (by
          simp only [Category.assoc]
          rw [hs1, ← Q.u₀_gen _ h1]
          simp only [Category.assoc])
      simpa only [Category.assoc] using this
  have hxψ : yK ≫ sec = x ≫ ψ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hs1, Category.assoc, hψ1, ← Category.assoc, hK0]
      exact hx4.symm
    · rw [Category.assoc, hs2, Category.assoc, hψ2, ← Category.assoc, hx3, Category.comp_id, Category.id_comp]
  have : IsDominant (jK u.V) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap u.V (FractionRing u.V))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective u.V (FractionRing u.V))]
      exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ (jK u.V) ?_
  · simp only [Category.assoc]
    rw [hh, hyW, hFw, ← Category.assoc, hx1, Category.id_comp]
  · rw [← Category.assoc, ← hkW, Category.assoc, key, ← Category.assoc, hkU, ← Category.assoc, hxψ,
      Category.assoc, hψ3, ← Category.assoc, hx2, Category.assoc]

end GlobalTheory.ZH
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionSection_eq_integral_point_at_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left), Q.ExtPt a W h → ∀ (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) → ∀ yW : Sp u.V ⟶ W.toScheme, yW ≫ W.ι = yV → yW ≫ h = hV ≫ F := by
  atlas_forward_decl GlobalTheory.ZH.extPt_comp_eq_integral_point
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem resG_trans_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem scale_mem_secOn {X : Scheme.{0}} (L : LB X) {V V' : X.Opens} (h : V' ≤ V) (a : Γ(X, V'))
    {σ : ∀ j, Γ(X, V ⊓ L.U j)} (hσ : σ ∈ secOn L V) :
    (fun j => resG X inf_le_left a * resG X (inf_le_inf_right _ h) (σ j)) ∈ secOn L V' := by
  intro i j
  have e := congrArg (resG X (inf_le_inf_right _ (inf_le_inf_right _ h) :
    V' ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hσ i j)
  simp only [map_mul, resG_trans_apply] at e ⊢
  rw [e, mul_left_comm]

theorem valF_scale {X Z : Scheme.{0}} (p : X ⟶ Z) {N N' : Z.Opens} (h : p ⁻¹ᵁ N' ≤ p ⁻¹ᵁ N) (F : Γ(Z, N'))
    (U : X.Opens) (s : Γ(X, p ⁻¹ᵁ N ⊓ U)) {K : Type} [Field K] (g : Sp K ⟶ X)
    (hg : ⊤ ≤ g ⁻¹ᵁ (p ⁻¹ᵁ N' ⊓ U)) :
    valF g (p ⁻¹ᵁ N' ⊓ U) (resG X inf_le_left ((p.app N').hom F) * resG X (inf_le_inf_right _ h) s) =
      valF (g ≫ p) N' F * valF g _ s := by
  rw [valF_eq_valR, valR_mul g _ hg, valR_res g _ hg, valR_res g _ hg, ← valR_comp]
  rfl

theorem RatModel.exists_unit_fn {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (N' : M.Z.Opens) (f : Ω) (hf : ∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) :
    ∃ F : Γ(M.Z, N'), (∀ z ∈ N', z ∈ M.Z.basicOpen F) ∧ ((N' : Set M.Z).Nonempty → valF M.pt N' F = f) := by
  by_cases hN : (N' : Set M.Z).Nonempty
  · obtain ⟨F, hF⟩ := (RatModel.mem_ringOn_iff_exists hN).1 (RatModel.mem_ringOn.2 fun z hz => (hf z hz).2.1)
    subst hF
    exact ⟨F, fun z hz => (RatModel.isUnit_valF_iff hz F).1
      ((RatModel.isUnit_O_iff _).2 ⟨(hf z hz).1, (hf z hz).2.2⟩), fun _ => rfl⟩
  · exact ⟨1, fun z hz => (hN ⟨z, hz⟩).elim, fun h => (hN h).elim⟩

theorem ZHPre.exists_scale_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (c f : Ω), N' ≤ N → (∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) → σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → Q.FibNe N σ → ∃ σ' : Q.SecFam N', σ' ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N') ∧ Q.ThMul (f * c) N' σ' ∧ Q.FibNe N' σ' := by
  intro o Ω _ _ _ _ S ρ M U₀ Q N N' σ c f hN hf hσ hT hF
  obtain ⟨F, hFu, hFv⟩ := M.exists_unit_fn N' f hf
  have h : Q.G.hom ⁻¹ᵁ N' ≤ Q.G.hom ⁻¹ᵁ N := fun _ hz => hN hz
  refine ⟨_, scale_mem_secOn Q.LOne h ((Q.G.hom.app N').hom F) hσ, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    have e := hT K β g r jP jL h1 h2 h3 h4 (h5.trans h)
    have hg : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U (fun _ => jL)) := fun w _ =>
      ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
    have hp : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
      rw [Category.assoc, Q.cart.1.w, ← h1]
      rfl
    have hne : (N' : Set M.Z).Nonempty := ⟨_, h5 ⟨IsLocalRing.closedPoint K, rfl⟩⟩
    have hv := valF_scale Q.G.hom h F _ (σ fun _ => jL) _ hg
    rw [hp, valF_eq_valR (spMap β ≫ M.pt), valR_spMap_comp β M.pt N' (M.top_le_preimage_pt hne),
      ← valF_eq_valR, hFv hne] at hv
    refine Eq.trans ?_ (congrArg (_ * ·) hv.symm)
    refine Eq.trans ?_ ((congrArg (β f * ·) e).trans (mul_left_comm _ _ _))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by rw [map_mul, _root_.mul_assoc]
  · intro K _ _ x hx
    obtain ⟨g, j, hg, hne⟩ := hF K x (hx.trans hN)
    have h1 : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) := by
      by_contra hc
      exact hne (dif_neg hc)
    have hx' : ⊤ ≤ x ⁻¹ᵁ N' := (top_le_preimage_iff x N').2 hx
    have h2 : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j) := fun w hw =>
      ⟨(show ⊤ ≤ (g ≫ Q.G.hom) ⁻¹ᵁ N' from hg ▸ hx') hw, (h1 hw).2⟩
    refine ⟨g, j, hg, ?_⟩
    rw [valF_scale Q.G.hom h F _ (σ j) g h2, hg]
    exact mul_ne_zero ((le_preimage_basicOpen_iff x hx' F).1 fun w hw => hFu _ (hx' hw)).ne_zero hne

end GlobalTheory.ZH
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_section_restriction_unit_twist : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (c f : Ω), N' ≤ N → (∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) → σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → Q.FibNe N σ → ∃ σ' : Q.SecFam N', σ' ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N') ∧ Q.ThMul (f * c) N' σ' ∧ Q.FibNe N' σ' := by
  atlas_forward_decl GlobalTheory.ZH.ZHPre.exists_scale_section
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem ZHPre.resG_eq_of_thMul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N') (c : Ω), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO N N' σ σ' c hσ hσ' j O h h'
  obtain ⟨K, _, β, g, r, jP, h1, h2, h3, h4⟩ := Q.exists_generic hO.ne
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine eq_of_valF_generic (g ≫ Q.φ) h4 fun hm => ?_
  have hm' := (top_le_preimage_iff _ _).1 hm
  have hV : Set.range (g ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N : Q.G.left.Opens) := fun y hy => (h (hm' hy)).1
  have hV' : Set.range (g ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N' : Q.G.left.Opens) := fun y hy => (h' (hm' hy)).1
  have hL : Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL := fun y hy => Set.mem_iInter.1 (h (hm' hy)).2 0
  have e := (hσ K β g r jP jL h1 h2 h3 hL hV).symm.trans (hσ' K β g r jP jL h1 h2 h3 hL hV')
  refine (valR_res _ h hm _).trans (Eq.trans ?_ (valR_res _ h' hm _).symm)
  refine mul_left_cancel₀ (zpow_ne_zero _ ?_) e
  refine IsUnit.ne_zero ?_
  have hw : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
      (fun _ => jP, fun _ => jL) := fun w _ =>
    ⟨Set.mem_iInter.2 fun _ => h3 ⟨w, Scheme.Hom.comp_apply _ _ _⟩,
      Set.mem_iInter.2 fun _ => hL ⟨w, Scheme.Hom.comp_apply _ _ _⟩⟩
  rw [valF_eq_valR, valR_eq g _ hw]
  exact (Units.isUnit _).map _

end GlobalTheory.ZH
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_eq_of_same_theta_multiple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N') (c : Ω), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j) := by
  atlas_forward_decl GlobalTheory.ZH.ZHPre.resG_eq_of_thMul
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GlueTheta

theorem res_res {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem glue_secOn {X : Scheme.{0}} (L : LB X) {I : Type} (V : I → X.Opens) (W : X.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : ∀ x ∈ W, ∃ i, x ∈ V i) (σ : ∀ i j, Γ(X, V i ⊓ L.U j)) (hσ : ∀ i, σ i ∈ secOn L (V i))
    (hc : ∀ i i' j (O : X.Opens) (h : O ≤ V i ⊓ L.U j) (h' : O ≤ V i' ⊓ L.U j),
      resG X h (σ i j) = resG X h' (σ i' j)) :
    ∃ s ∈ secOn L W, ∀ i j, resG X (inf_le_inf_right _ (hle i)) (s j) = σ i j := by
  have key : ∀ j, ∃ s : Γ(X, W ⊓ L.U j), ∀ i, resG X (inf_le_inf_right _ (hle i)) s = σ i j := by
    intro j
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun i => V i ⊓ L.U j) (W ⊓ L.U j)
      (fun i => homOfLE (inf_le_inf_right _ (hle i)))
      (fun x hx => by
        obtain ⟨i, hi⟩ := hcov x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi, hx.2⟩)
      (fun i => σ i j) (fun i i' => hc i i' j _ inf_le_left inf_le_right)
    exact ⟨s, hs⟩
  choose s hs using key
  refine ⟨s, fun j k => ?_, fun i j => hs j i⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => V i ⊓ L.U j ⊓ L.U k) (W ⊓ L.U j ⊓ L.U k)
    (fun i => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hle i))))
    (fun x hx => by
      obtain ⟨i, hi⟩ := hcov x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨hi, hx.1.2⟩, hx.2⟩) _ _ fun i => ?_
  have h := hσ i j k
  rw [← hs j i, ← hs k i, res_res, res_res] at h
  change resG X _ _ = resG X _ _
  rw [map_mul, res_res, res_res, res_res]
  exact h

theorem exists_glue : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (c : Ω), (∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N'), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j)) → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ N ≤ W ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.ThMul c N σ ∧ Q.FibNe N σ) → ∃ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ W), Q.ThMul c W σ ∧ Q.FibNe W σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q c huniq W hloc
  choose N σ hz hNW hsec hth hne using fun z : W => hloc z.1 z.2
  obtain ⟨s, hs, hres⟩ := glue_secOn Q.LOne (fun z : W => Q.G.hom ⁻¹ᵁ N z) (Q.G.hom ⁻¹ᵁ W)
    (fun z x hx => hNW z hx) (fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩) σ hsec
    (fun z z' => huniq _ _ _ _ (hth z) (hth z'))
  have hval : ∀ (K : Type) [Field K] (g : Sp K ⟶ Q.G.left) (z : W) (j : Q.LOne.ι),
      ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) → valF g _ (σ z j) = valF g _ (s j) := by
    intro K _ g z j h
    rw [← hres z j]
    exact GlobalTheory.Points.valR_res g _ h _
  refine ⟨s, hs, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    let z : W := ⟨Q.G.hom ((g ≫ Q.φ) (IsLocalRing.closedPoint K)), h5 ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z) := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U fun _ => jL) := fun t ht =>
      ⟨hN ht, Set.mem_iInter.2 fun _ => h4 ⟨t, rfl⟩⟩
    rw [← hval K _ z _ hU]
    exact hth z K β g r jP jL h1 h2 h3 h4 (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
  · intro K _ _ x hx
    let z : W := ⟨x (IsLocalRing.closedPoint K), hx ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ x ⁻¹ᵁ N z := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    obtain ⟨g, j, hg, hv⟩ := hne z K x (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
    refine ⟨g, j, hg, ?_⟩
    have hU : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) := by
      by_contra hU
      exact hv (dif_neg hU)
    rwa [← hval K g z j hU]

end GlobalTheory.ZH.GlueTheta
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_sections_same_theta_multiple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (c : Ω), (∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N'), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j)) → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ N ≤ W ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.ThMul c N σ ∧ Q.FibNe N σ) → ∃ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ W), Q.ThMul c W σ ∧ Q.FibNe W σ := by
  atlas_forward_decl GlobalTheory.ZH.GlueTheta.exists_glue
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ZHPre
open GlobalTheory.Points
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem exists_thMul (h1 : Laws) (h2 : Laws2) (ov : S.Over₀ M U₀) (N : M.Z.Opens) (σ : Q.SecFam N)
    (hσ : σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N)) (hN : (N : Set M.Z).Nonempty) : ∃ c, Q.ThMul c N σ := by
  have hpt : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact (top_le_preimage_iff M.pt U₀).1 (M.top_le_preimage_pt ov.ne) ⟨w, rfl⟩
  have heta : IsOpenImmersion.lift U₀.ι M.pt hpt ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_genericFibre_section_of_model_section o Ω S ρ M U₀ Q N σ _ hσ hN heta
  obtain ⟨c, hc⟩ := GlobalTheory.T.sec_generic_eq_mul_theta_alt h1 h2 o Ω S ρ s
  refine ⟨c, ?_⟩
  intro K _ β g r jP jL hg hr hP hL _
  have hg' : g ≫ pullback.snd _ _ = spMap β ≫ IsOpenImmersion.lift U₀.ι M.pt hpt := by
    rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, heta]
    exact hg
  have hcomm : spMap β ≫ spMap S.R.val.toRingHom = (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ≫ ρ.P.A.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg', Category.assoc, Q.u₀_gen _ heta]
  let q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left :=
    pullback.lift (spMap β) (g ≫ pullback.fst _ _) hcomm
  have hq1 : q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β :=
    pullback.lift_fst _ _ _
  have hq2 : q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left =
      g ≫ pullback.fst _ _ :=
    pullback.lift_snd _ _ _
  have e1 := hs K β q g jP jL hq1 hq2.symm hg' hP hL
  have e2 := hc K β q r jP hq1 (hr.trans hq2.symm) (by rw [hq2]; exact hP)
  simp only [Finset.univ_unique, Finset.sum_singleton, zpow_one]
  rw [← e2, e1]

theorem exists_good_label (h0 : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)) (hs : GlobalTheory.Published.SemistableReductionSt) (hU : ThmUSt) (h1 : Laws) (h2 : Laws2)
    (hT : UTorsSt) (big : S.Big) (ov : S.Over₀ M U₀) (N : M.Z.Opens) (σ : Q.SecFam N)
    (hσ : σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N)) (hne : Q.FibNe N σ) (z : M.Z) (hz : IsClosed ({z} : Set M.Z))
    (hzN : z ∈ N) : ∃ a ∈ S.HH M z, ∀ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme),
      Q.ExtPt a W h → W.ι w = z → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι),
        Set.range x = {w} ∧ valF (x ≫ h) _ (σ j) ≠ 0 := by
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)
  haveI : CharZero Ω := ArithBase.char (o := o)
  obtain ⟨⟨p, hp, y, hy⟩, -⟩ := (classical_points_and_local_regularity o Ω M U₀ ov.normal).1 U₀ le_rfl ov.ne z hz
  obtain ⟨y₀, Fs, hAt, hint, hfac⟩ := GlobalTheory.T.exists_classical_point_factor_large_model o Ω S ρ M U₀ Q ov z p y hy
  obtain ⟨u, l, τ, hmatch, hFs⟩ := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hs hU h1 h2 hT o Ω S ρ).2 p y₀ Fs hint
  obtain ⟨jV, yV, yK, hTF⟩ := hfac u hFs
  obtain ⟨F, ψ, hTM⟩ := GlobalTheory.T.exists_testMap_of_testFac h0 o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF
  have hLB := GlobalTheory.T.lineBundleIso_pullback_uniformisedThetaModel o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM
  have hyN : y (cPt p) ∈ N := by rw [hy.1]; exact hzN
  obtain ⟨t, ht, j, hj⟩ := GlobalTheory.T.exists_torsionPoint_specialFibre_section_ne_zero h1 h2 o Ω S ρ M U₀ Q big p y y₀ u jV yV yK hTF F ψ hTM hLB N σ hσ hne hyN
  have hn : IsUnit ((S.r * S.N : ℕ) : Γ(Sp u.V, ⊤)) := by
    have hv : IsUnit ((S.r * S.N : ℕ) : u.V) := by
      have he : ((S.r * S.N : ℕ) : o) * ↑(S.unit.unit⁻¹) = 1 := S.unit.mul_val_inv
      have hnorm : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (u.yK (algebraMap o S.R ↑(S.unit.unit⁻¹)))‖ ≤ 1 := by
        have hf := RingHom.congr_fun u.fac (algebraMap o S.R ↑(S.unit.unit⁻¹))
        rw [RingHom.comp_apply] at hf
        rw [hf]
        exact hint _
      obtain ⟨v, hvE⟩ := (u.norm_le _).1 hnorm
      have hmul : ((S.r * S.N : ℕ) : u.V) * v = 1 := by
        apply IsFractionRing.injective u.V (FractionRing u.V)
        rw [map_mul, map_one, hvE, map_natCast, ← map_natCast u.yK, ← map_natCast (algebraMap o S.R),
          ← map_mul, ← map_mul, he, map_one, map_one]
      exact ⟨⟨_, v, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
    simpa using hv.map (Scheme.ΓSpecIso (CommRingCat.of u.V)).inv.hom
  obtain ⟨b, hb, hbt⟩ := GlobalTheory.T.exists_padicLift_torsionPoint_invertibleOrder p (Sp u.V) u.G u.semi (spMap jV) (S.r * S.N) hn t ht
  obtain ⟨a, hV, x, ⟨hV1, hx1, hx2, hx3⟩, hbV⟩ := GlobalTheory.T.integral_torsion_point_descends_to_model o Ω S ρ p y₀ u jV hTF.1 b hb
  have hker : a ∈ τ.yy.ker := by
    obtain ⟨e, -, he⟩ := hmatch
    have hl : l.yy a = 0 := (AddMonoidHom.mem_ker).1 ((l.ker_iff a).2 ⟨hV, x, hV1, hx1, hx2, hx3⟩)
    have h0' : τ.yy a = QuotientAddGroup.mk 0 := (he a 0).2 (by rw [hl, map_zero]; rfl)
    rw [AddMonoidHom.mem_ker, h0']
    rfl
  have hHH := (ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ ov z p y y₀ τ hy hAt).2
  refine ⟨a, by rw [hHH]; exact hker, ?_⟩
  intro W h w hExt hwz
  haveI := isLocalHom_of_test u jV hTF.1
  have hzW : z ∈ W := by
    have hr : z ∈ Set.range W.ι := ⟨w, hwz⟩
    rwa [Scheme.Opens.range_ι] at hr
  have hVz : yV (IsLocalRing.closedPoint u.V) = z := by
    rw [← hy.1, ← hTF.2.1, Scheme.Hom.comp_apply]
    congr 1
    exact (IsLocalRing.comap_closedPoint jV).symm
  have hsp : ∀ v, yV v ⤳ z := fun v => hVz ▸ (IsLocalRing.specializes_closedPoint v).map yV.continuous
  have hrange : Set.range yV ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff yV W).1 (top_le_preimage_of_specializes hsp hzW)
  have hyW : IsOpenImmersion.lift W.ι yV hrange ≫ W.ι = yV := IsOpenImmersion.lift_fac _ _ _
  have hcomp := GlobalTheory.T.torsionSection_eq_integral_point_at_test o Ω S ρ M U₀ Q p y y₀ u jV yV yK hTF F ψ hTM a W h hExt hV x
    ⟨hV1, hx1, hx2, hx3⟩ _ hyW
  refine ⟨IsLocalRing.ResidueField (OO p), inferInstance,
    spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange, j, ?_, ?_⟩
  · rw [Set.range_unique]
    congr 1
    apply W.ι.isOpenEmbedding.injective
    rw [hwz, ← Scheme.Hom.comp_apply]
    simp only [Category.assoc, hyW, hTF.2.1]
    rw [Scheme.Hom.comp_apply, ← hy.1]
    congr 1
    rw [show (default : Sp (IsLocalRing.ResidueField (OO p))) = IsLocalRing.closedPoint _ from
      Subsingleton.elim _ _]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  · have hx : (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV ≫ IsOpenImmersion.lift W.ι yV hrange) ≫ h =
        t.left ≫ F := by
      rw [Category.assoc, Category.assoc, hcomp, ← Category.assoc (spMap jV), hbV, ← Category.assoc, hbt]
    rw [hx]
    exact hj

theorem exists_theta_div : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → S.Over₀ M U₀ → Q.Sec → Q.LocTheta → ∀ (W : M.Z.Opens) (x₀ : S.Gam), (∀ z ∈ W, x₀ ∈ S.supI M z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th x₀)⁻¹) _ σ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0 := by
  intro h0 hs hU h1 h2 hT o Ω _ _ _ _ S ρ M U₀ Q big ov hSec hLoc W x₀ hx₀
  refine GlobalTheory.T.exists_glue_sections_same_theta_multiple o Ω S ρ M U₀ Q (S.th x₀)⁻¹
    (fun N N' σ σ' hσ hσ' j O h h' => GlobalTheory.T.restrict_eq_of_same_theta_multiple o Ω S ρ M U₀ Q ov N N' σ σ' _ hσ hσ' j O h h') W ?_
  intro z hzW
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (Ω := Ω)
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : JacobsonSpace M.Z := (classical_points_and_local_regularity o Ω M U₀ ov.normal).2
  obtain ⟨N₀, σ₀, hzN₀, hσ₀, hne₀⟩ := GlobalTheory.T.exists_localThetaSection_fibreNonzero o Ω S ρ M U₀ Q hLoc z
  obtain ⟨c₀, hc₀⟩ := Q.exists_thMul h1 h2 ov N₀ σ₀ hσ₀ ⟨z, hzN₀⟩
  have hext : ∀ (z' : M.Z), ∀ b ∈ S.HH M z', ∃ (Wb : M.Z.Opens) (hb : Wb.toScheme ⟶ Q.G.left) (wb : Wb.toScheme),
      Q.ExtPt b Wb hb ∧ Wb.ι wb = z' ∧ Q.FrameUnit b Wb hb wb := by
    intro z' b hb
    obtain ⟨Wb, hb', hz'Wb, hb1, hb2⟩ := hSec z' b hb
    obtain ⟨wb, hwb⟩ : z' ∈ Set.range Wb.ι := by rw [Scheme.Opens.range_ι]; exact hz'Wb
    have hE : Q.ExtPt b Wb hb' := ⟨hb1, hb2⟩
    exact ⟨Wb, hb', wb, hE, hwb, GlobalTheory.T.torsionFrame_isUnit_along_section o Ω S ρ M U₀ Q ov
      (fun α hα hn => GlobalTheory.T.exists_generator_normalised_mulByN_iso o Ω S ρ M U₀ Q ov (S.r * S.N) α hα hn) b Wb hb' wb hE⟩
  have hcl : ∀ z' : M.Z, IsClosed ({z'} : Set M.Z) → z' ∈ N₀ → z' ∈ W →
      c₀ * S.th x₀ ≠ 0 ∧ c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z' := by
    intro z' hz' hz'N hz'W
    obtain ⟨a, ha, hgood⟩ := Q.exists_good_label h0 hs hU h1 h2 hT big ov N₀ σ₀ hσ₀ hne₀ z' hz' hz'N
    obtain ⟨Wa, ha', wa, hEa, hwa, hFa⟩ := hext z' a ha
    have hwaN : Wa.ι wa ∈ N₀ := by rw [hwa]; exact hz'N
    have hxa := GlobalTheory.T.theta_mul_regular_and_unit_along_torsion o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ a Wa ha' wa hEa hFa hwaN
    obtain ⟨K, _, x, j, hx, hv⟩ := hgood Wa ha' wa hEa hwa
    obtain ⟨hne, hinv⟩ := hxa.2 K x j hx hv
    have hx₀' : x₀ ∈ S.supI M z' := hx₀ z' hz'W
    obtain ⟨Wb, hb', wb, hEb, hwb, hFb⟩ := hext z' x₀ (AddSubgroup.subset_closure hx₀')
    have hwbN : Wb.ι wb ∈ N₀ := by rw [hwb]; exact hz'N
    have hxb := (GlobalTheory.T.theta_mul_regular_and_unit_along_torsion o Ω S ρ M U₀ Q ov N₀ σ₀ c₀ hσ₀ hc₀ x₀ Wb hb' wb hEb hFb hwbN).1
    rw [hwa] at hinv
    rw [hwb] at hxb
    have hdiv : M.Div S.th x₀ z' := hx₀'
    obtain ⟨hth, hdivs⟩ := hdiv
    have hc : c₀ ≠ 0 := left_ne_zero_of_mul hne
    have hta : S.th a ≠ 0 := right_ne_zero_of_mul hne
    refine ⟨mul_ne_zero hc hth, hxb, ?_⟩
    have heq : (c₀ * S.th x₀)⁻¹ = S.th a / S.th x₀ * (c₀ * S.th a)⁻¹ := by
      field_simp
    rw [heq]
    exact Subalgebra.mul_mem _ (hdivs a) hinv
  have hopen : IsOpen {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'} :=
    (M.isOpen_setOf_mem_O _).inter (M.isOpen_setOf_mem_O _)
  have hall : ∀ z' : M.Z, z' ∈ N₀ → z' ∈ W → c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z' := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₂, hz₂N, hz₂W, hbad⟩ := hcon
    have hZ : (((N₀ : Set M.Z) ∩ (W : Set M.Z)) ∩
        {z' : M.Z | c₀ * S.th x₀ ∈ M.O z' ∧ (c₀ * S.th x₀)⁻¹ ∈ M.O z'}ᶜ).Nonempty :=
      ⟨z₂, ⟨hz₂N, hz₂W⟩, fun h => hbad h.1 h.2⟩
    obtain ⟨z', ⟨⟨hz'N, hz'W⟩, hz'bad⟩, hz'c⟩ := nonempty_inter_closedPoints hZ
      ⟨_, _, N₀.isOpen.inter W.isOpen, hopen.isClosed_compl, rfl⟩
    obtain ⟨-, h1', h2'⟩ := hcl z' hz'c hz'N hz'W
    exact hz'bad ⟨h1', h2'⟩
  obtain ⟨z₁, ⟨hz₁N, hz₁W⟩, hz₁c⟩ := nonempty_inter_closedPoints
    (⟨z, hzN₀, hzW⟩ : ((N₀ : Set M.Z) ∩ (W : Set M.Z)).Nonempty) (N₀.isOpen.inter W.isOpen).isLocallyClosed
  have hf0 : c₀ * S.th x₀ ≠ 0 := (hcl z₁ hz₁c hz₁N hz₁W).1
  obtain ⟨σ', hσ', hth', hne'⟩ := GlobalTheory.T.theta_section_restriction_unit_twist o Ω S ρ M U₀ Q N₀ (N₀ ⊓ W) σ₀ c₀ (c₀ * S.th x₀)⁻¹ inf_le_left
    (fun z' hz' => by
      obtain ⟨hz'N, hz'W⟩ := hz'
      obtain ⟨h1', h2'⟩ := hall z' hz'N hz'W
      exact ⟨inv_ne_zero hf0, h2', by rw [inv_inv]; exact h1'⟩) hσ₀ hc₀ hne₀
  have hc₀0 : c₀ ≠ 0 := left_ne_zero_of_mul hf0
  have hth0 : S.th x₀ ≠ 0 := right_ne_zero_of_mul hf0
  have hfc : (c₀ * S.th x₀)⁻¹ * c₀ = (S.th x₀)⁻¹ := by
    field_simp
  rw [hfc] at hth'
  exact ⟨N₀ ⊓ W, σ', ⟨hzN₀, hzW⟩, inf_le_right, hσ', hth', hne'⟩

end GlobalTheory.ZH.ZHPre
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDividedByConstant_nonvanishing_fibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → S.Over₀ M U₀ → Q.Sec → Q.LocTheta → ∀ (W : M.Z.Opens) (x₀ : S.Gam), (∀ z ∈ W, x₀ ∈ S.supI M z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => (S.th x₀)⁻¹) _ σ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ W → ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0 := by
  atlas_forward_decl GlobalTheory.ZH.ZHPre.exists_theta_div
end
