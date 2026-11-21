import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalLevelLeLevelCharactersAgree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix

namespace GlobalTheory.FirstBlocksReduction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ExportSeries GlobalTheory.FlatVecSum

variable {D : D7} {S T : HSp D}
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem exists_reps {G X : Type} [Group G] (J J' : Subgroup G) (φ : G → X) (A : Set X) (hA : A.Finite)
    (hφ : ∀ κ ∈ J, φ κ ∈ A) (h : ∀ u ∈ J, ∀ κ ∈ J, u⁻¹ * κ ∈ J' ↔ φ u = φ κ) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ J) ∧ ∀ κ ∈ J, ∃! u : G, u ∈ F ∧ u⁻¹ * κ ∈ J' := by
  classical
  have hfin : (φ '' (J : Set G)).Finite := hA.subset (by rintro _ ⟨κ, hκ, rfl⟩; exact hφ κ hκ)
  have hs : ∀ x : ↥(φ '' (J : Set G)), ∃ u, u ∈ J ∧ φ u = x.1 := fun x => x.2
  choose s hsJ hsφ using hs
  haveI := hfin.fintype
  refine ⟨Finset.univ.image s, fun u hu => ?_, fun κ hκ => ⟨s ⟨φ κ, κ, hκ, rfl⟩, ⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
    exact hsJ x
  · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · exact (h _ (hsJ _) _ hκ).2 (hsφ _)
  · rintro u ⟨hu, hu'⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
    congr 1
    exact Subtype.ext ((hsφ x).symm.trans ((h _ (hsJ x) _ hκ).1 hu'))

theorem extension_by_one_mul {G H : Type} [Group G] [Monoid H] (K : Subgroup G) (f : K →* H) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    ext1 K f (a * b) = ext1 K f a * ext1 K f b := by
  unfold ext1
  rw [dif_pos ha, dif_pos hb, dif_pos (mul_mem ha hb), ← map_mul]
  rfl

theorem lowerRightBlock_mul_blockTriangular {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) {a b : GL (Fin n) κ} (ha : a ∈ blockTri (blk2 r))
    (hb : b ∈ blockTri (blk2 r)) : upperLeftBlock hr (a * b) = upperLeftBlock hr a * upperLeftBlock hr b :=
  extension_by_one_mul _ _ ha hb

def firstBlocks (B : Base S T) (ψ : Twist D Circle) (k : Bridge.Gf S) : G0 B.G.Pg T.rank :=
  rTup B.F.βS (B.levS ψ) (Formalism.UG.bc (Lev.swapAE D) k.1)

theorem firstBlocks_mul (B : Base S T) (ψ : Twist D Circle) {a b : Bridge.Gf S} (ha : a ∈ B.levJ ψ) (hb : b ∈ B.levJ ψ) :
    firstBlocks B ψ (a * b) = firstBlocks B ψ a * firstBlocks B ψ b := by
  have pa := lev_le_parLev ha
  have pb := lev_le_parLev hb
  funext PP
  show upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) (a.1 * b.1))) =
    upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1)) * upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) b.1))
  have e : redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1 * Formalism.UG.bc (Lev.swapAE D) b.1) =
      redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1) * redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) b.1) :=
    extension_by_one_mul (St B.F.βS) (redAt B.F.βS PP.1) (Base.mem_St_of_mem_levJ ha) (Base.mem_St_of_mem_levJ hb)
  rw [map_mul, e]
  exact lowerRightBlock_mul_blockTriangular _ (blockTri_blkOf_le _ _ (parLev_g pa PP.2)) (blockTri_blkOf_le _ _ (parLev_g pb PP.2))

theorem mem_princ_iff (B : Base S T) (ψ : Twist D Circle) {k : Bridge.Gf S} (hk : k ∈ B.levJ ψ) :
    k ∈ (princ B).levJ ψ ↔ firstBlocks B ψ k = 1 :=
  ⟨fun h => Subgroup.mem_bot.1 h.2, fun h => ⟨mem_parLev.2 (by exact mem_parLev.1 hk.1), Subgroup.mem_bot.2 h⟩⟩

theorem exists_reps_levJ : ∀ {D : Formalism.BasicNotions.D7} {S T : Formalism.BasicNotions.TH.HSp D} (B : GlobalTheory.ExportSeries.Base S T), GlobalTheory.ExportSeries.Base.Good B → ∀ (ψ : GlobalTheory.ExportSeries.Twist D Circle), GlobalTheory.ExportSeries.Base.admitted B (GlobalTheory.ExportSeries.Twist.Q ψ) → ∃ (F : Finset ↥(Formalism.IndefR.Bridge.Gf S)), (∀ u ∈ F, u ∈ GlobalTheory.ExportSeries.Base.levJ B ψ) ∧ ∀ κ ∈ GlobalTheory.ExportSeries.Base.levJ B ψ, ∃! u : ↥(Formalism.IndefR.Bridge.Gf S), u ∈ F ∧ u⁻¹ * κ ∈ GlobalTheory.ExportSeries.Base.levJ (GlobalTheory.FlatVecSum.princ B) ψ := by
  intro D S T B _ ψ _
  refine exists_reps _ _ (firstBlocks B ψ) (B.G.P.H : Set _) (Set.finite_coe_iff.1 (finite_H B.G.P)) (fun κ hκ => hκ.2)
    fun u hu κ hκ => ?_
  have hm := mul_mem (inv_mem hu) hκ
  have e := firstBlocks_mul B ψ hu hm
  rw [mul_inv_cancel_left] at e
  rw [mem_princ_iff B ψ hm, e]
  exact left_eq_mul.symm

end GlobalTheory.FirstBlocksReduction

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.LevReps

def rHomJ {D : D7} {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) :
    B.levJ ψ →* G0 (B.levS ψ).Pg (B.levS ψ).r :=
  (rHom D.sp.cm S.gram B.F.βS (B.levS ψ)).comp
    (((Formalism.UG.bc (Lev.swapAE D)).comp ((finHom S).range.subtype.comp (B.levJ ψ).subtype)).codRestrict _
      (fun κ => κ.2.1))

theorem ker_le {D : D7} {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) :
    (rHomJ B ψ).ker ≤ ((GlobalTheory.FlatVecSum.princ B).levJ ψ).subgroupOf (B.levJ ψ) := by
  intro κ hκ
  rw [Subgroup.mem_subgroupOf]
  exact ⟨κ.2.1, hκ⟩

instance finiteIndex {D : D7} {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) :
    (((GlobalTheory.FlatVecSum.princ B).levJ ψ).subgroupOf (B.levJ ψ)).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ker_le B ψ)

theorem reps : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ F : Finset (Bridge.Gf S), (∀ u ∈ F, u ∈ B.levJ ψ) ∧
      ∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ := by
  first
  | exact @_root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ
  | exact _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ
  | (apply _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> assumption)
  | (intros; apply _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ ..)

end GlobalTheory.LevReps
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_coset_representatives_level : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ F : Finset (Bridge.Gf S), (∀ u ∈ F, u ∈ B.levJ ψ) ∧
      ∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ := by
  atlas_forward_decl GlobalTheory.LevReps.reps
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.ClassRefineBridge

open GlobalTheory.ClassRefine
open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

theorem injective_of_isReps {J : Subgroup G} {I : Type} {y : I → G} (hy : Bridge.IsReps ι J y) :
    Function.Injective y := by
  intro i j hij
  have h1 : ∃ (γ : Γ) (k : J), y i = ι γ * y i * k := ⟨1, 1, by simp⟩
  have h2 : ∃ (γ : Γ) (k : J), y i = ι γ * y j * k := ⟨1, 1, by simp [hij]⟩
  exact (hy (y i)).unique h1 h2

theorem image_reps {J : Subgroup G} {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι J y) :
    ∀ g : G, ∃! t, t ∈ Finset.univ.image y ∧ ∃ (γ : ι.range) (κ : G), κ ∈ J ∧ g = (γ : G) * t * κ := by
  intro g
  obtain ⟨i, ⟨γ, k, e⟩, hu⟩ := hy g
  refine ⟨y i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ⟨ι γ, γ, rfl⟩, k, k.2, e⟩, ?_⟩
  rintro t ⟨ht, ⟨_, δ, rfl⟩, κ, hκ, e'⟩
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
  rw [hu j ⟨δ, ⟨κ, hκ⟩, e'⟩]

theorem card_stab_eq (hι : Function.Injective ι) (J : Subgroup G) (t : G) :
    Nat.card (Bridge.stab ι J t) = Nat.card (stabQ ι.range J t) := by
  refine Nat.card_congr (Equiv.ofBijective (fun γ => ⟨⟨ι γ, γ, rfl⟩, ?_⟩) ⟨?_, ?_⟩)
  · rw [mem_stabQ]; exact (Bridge.mem_stab ι).1 γ.2
  · intro a b h
    apply Subtype.ext
    apply hι
    have := congrArg (fun x : stabQ ι.range J t => ((x : ι.range) : G)) h
    simpa using this
  · rintro ⟨⟨_, γ, rfl⟩, hq⟩
    refine ⟨⟨γ, (Bridge.mem_stab ι).2 (mem_stabQ.1 hq)⟩, rfl⟩

theorem sum_image_eq {I : Type} [Fintype I] {y : I → G} (hy : Function.Injective y) (f : G → ℂ) :
    ∑ i, f (y i) = ∑ t ∈ Finset.univ.image y, f t := by
  rw [Finset.sum_image (fun a _ b _ h => hy h)]

theorem sum_isReps_refine : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G), Function.Injective ι → ∀ {J J₀ : Subgroup G}, J₀ ≤ J →
    ∀ {F : Finset G}, (∀ u ∈ F, u ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J₀) →
    ∀ {I₀ : Type} [Fintype I₀] (y₀ : I₀ → G), Bridge.IsReps ι J₀ y₀ → ∀ {I : Type} [Fintype I] (y : I → G), Bridge.IsReps ι J y →
    ∀ (Φ : G → ℂ), (∀ γ g, Φ (ι γ * g) = Φ g) → (∀ k ∈ J₀, ∀ g, Φ (g * k) = Φ g) →
    ∑ i, ((Nat.card (Bridge.stab ι J₀ (y₀ i)) : ℂ))⁻¹ * Φ (y₀ i) =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ∑ u ∈ F, Φ (y i * u) := by
  intro G Γ _ _ ι hι J J₀ hJ F hF hFu I₀ _ y₀ hy₀ I _ y hy Φ hl hr
  have key := sum_classReps_refine (Q := ι.range) hJ (image_reps ι hy) (image_reps ι hy₀) Φ
    (by rintro ⟨_, γ, rfl⟩ g; exact hl γ g) hr hF hFu
  simp only [card_stab_eq ι hι]
  rw [sum_image_eq (injective_of_isReps ι hy₀) (fun t => ((Nat.card (stabQ ι.range J₀ t) : ℂ))⁻¹ * Φ t),
    sum_image_eq (injective_of_isReps ι hy) (fun t => ((Nat.card (stabQ ι.range J t) : ℂ))⁻¹ * ∑ u ∈ F, Φ (t * u))]
  exact key

end GlobalTheory.ClassRefineBridge
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_regroup_finerLevel_cosets : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G), Function.Injective ι → ∀ {J J₀ : Subgroup G}, J₀ ≤ J →
    ∀ {F : Finset G}, (∀ u ∈ F, u ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J₀) →
    ∀ {I₀ : Type} [Fintype I₀] (y₀ : I₀ → G), Bridge.IsReps ι J₀ y₀ → ∀ {I : Type} [Fintype I] (y : I → G), Bridge.IsReps ι J y →
    ∀ (Φ : G → ℂ), (∀ γ g, Φ (ι γ * g) = Φ g) → (∀ k ∈ J₀, ∀ g, Φ (g * k) = Φ g) →
    ∑ i, ((Nat.card (Bridge.stab ι J₀ (y₀ i)) : ℂ))⁻¹ * Φ (y₀ i) =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ∑ u ∈ F, Φ (y i * u) := by
  atlas_forward_decl GlobalTheory.ClassRefineBridge.sum_isReps_refine
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

namespace GlobalTheory.PrincClassSum

theorem fin_symm {D : D7} (S : HSp D) (y : Bridge.Gf S) :
    finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) = y :=
  (GlobalTheory.ClassRegroup.finEquiv S).apply_symm_apply y

theorem left_inv {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ψ : Twist D Circle) (hψ : ψ.Good)
    (hQ : B.admitted ψ.Q) (ω : PairRep S T) (hω : B.IsWeil ψ.chi ω) {F : Bridge.Gf S → _} (hF : F ∈ B.formsC ψ)
    (g : GA D T) (γ : GQ S) (y : Bridge.Gf S) :
    series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
        (F (Bridge.ratF S γ * y)) g =
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  have e : finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S) =
      Bridge.ratF S γ * finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) *
        ((1 : (GlobalTheory.FlatVecSum.princ B).levJ ψ) : Bridge.Gf S) := by
    rw [fin_symm, fin_symm, OneMemClass.coe_one, mul_one]
  have hm := GlobalTheory.BaseClassSum.series_move (GlobalTheory.FlatVecSum.princ_good hB) hS hψ hQ hω (Subtype.property _) (Subtype.property _)
    γ 1 e (F (Bridge.ratF S γ * y))
  have hl := (B.mem_formsC.1 hF).2 γ y 1
  rw [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at hl
  have hinv : B.act ((γ⁻¹ : GQ S) : GA D S) (B.act (γ : GA D S) (F y)) = F y := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [map_one, Units.val_one, inv_one, one_smul] at hm
  rw [hl] at hm ⊢
  rw [show (GlobalTheory.FlatVecSum.princ B).act = B.act from rfl, hinv] at hm
  exact congrFun hm g

set_option maxHeartbeats 8000000 in
theorem right_inv {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ψ : Twist D Circle) (hψ : ψ.Good)
    (hQ : B.admitted ψ.Q) (ω : PairRep S T) (hω : B.IsWeil ψ.chi ω) {F : Bridge.Gf S → _} (hF : F ∈ B.formsC ψ)
    (g : GA D T) (k : Bridge.Gf S) (hk : k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ) (y : Bridge.Gf S) :
    series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
        (F (y * k)) g =
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  obtain ⟨hle, hlam⟩ := GlobalTheory.T.principalLevel_le_level_characters_agree B hB ψ hQ
  have e : finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S) =
      Bridge.ratF S 1 * finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) *
        ((⟨k, hk⟩ : (GlobalTheory.FlatVecSum.princ B).levJ ψ) : Bridge.Gf S) := by
    rw [fin_symm, fin_symm, (Bridge.ratF S).map_one, one_mul]
  have hm := GlobalTheory.BaseClassSum.series_move (GlobalTheory.FlatVecSum.princ_good hB) hS hψ hQ hω (Subtype.property _) (Subtype.property _)
    1 ⟨k, hk⟩ e (F (y * k))
  have hl := (B.mem_formsC.1 hF).2 1 y ⟨k, hle hk⟩
  rw [(Bridge.ratF S).map_one, one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply] at hl
  rw [show (GlobalTheory.FlatVecSum.princ B).act = B.act from rfl, inv_one, OneMemClass.coe_one, map_one,
    Module.End.one_apply, hlam k hk] at hm
  rw [hl] at hm ⊢
  rw [LinearMap.map_smul, LinearMap.map_smul, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at hm
  rw [LinearMap.map_smul]
  exact congrFun hm g

theorem terms_inv : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ F ∈ B.formsC ψ, ∀ g : GA D T,
      (∀ (γ : GQ S) (y : Bridge.Gf S),
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
          (F (Bridge.ratF S γ * y)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g) ∧
      ∀ k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ, ∀ y : Bridge.Gf S,
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
          (F (y * k)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g :=
  fun B hB hS ψ hψ hQ ω hω _ hF g =>
    ⟨fun γ y => left_inv B hB hS ψ hψ hQ ω hω hF g γ y, fun k hk y => right_inv B hB hS ψ hψ hQ ω hω hF g k hk y⟩

end GlobalTheory.PrincClassSum
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSumTerms_invariant_principalLevel : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ F ∈ B.formsC ψ, ∀ g : GA D T,
      (∀ (γ : GQ S) (y : Bridge.Gf S),
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
          (F (Bridge.ratF S γ * y)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g) ∧
      ∀ k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ, ∀ y : Bridge.Gf S,
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
          (F (y * k)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  atlas_forward_decl GlobalTheory.PrincClassSum.terms_inv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LevTransl

variable {D : D7} {S T : HSp D}

open GlobalTheory.ExportSeries.DualType Matrix

def fE (u : Bridge.Gf S) : GL (Fin S.rank) (Lev.EAf D) :=
  Lev.finE S (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S)

theorem finPt_symm (u : Bridge.Gf S) :
    finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S) = u :=
  (GlobalTheory.ClassRegroup.finEquiv S).apply_symm_apply u

theorem finE_eq (g : GA D S) : Lev.finE S g = Formalism.UG.bc (Lev.swapAE D) (finPt S g).1 := rfl

theorem fE_finPt {g : GA D S} : fE (finPt S g) = Lev.finE S g := by
  unfold fE
  rw [finE_eq, finE_eq g, finPt_symm]

theorem fE_mul (u v : Bridge.Gf S) : fE (u * v) = fE u * fE v := by
  unfold fE
  rw [map_mul, Subgroup.coe_mul, map_mul]

theorem fE_inv (u : Bridge.Gf S) : fE u⁻¹ = (fE u)⁻¹ := by
  unfold fE
  rw [map_inv, Subgroup.coe_inv, map_inv]

theorem mem_levJ_iff (B : Base S T) (ψ : Twist D Circle) (u : Bridge.Gf S) :
    u ∈ B.levJ ψ ↔ fE u ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ) := by
  have hk := ((GlobalTheory.ClassRegroup.finEquiv S).symm u).2
  have e := finPt_symm u
  constructor
  · intro h
    rw [← e] at h
    exact ((B.finPt_mem_levJ ψ hk).1 h).2
  · intro h
    rw [← e]
    exact (B.finPt_mem_levJ ψ hk).2 ⟨hk, h⟩

theorem mem_lev_princ (B : Base S T) (ψ : Twist D Circle) (x : GL (Fin S.rank) (Lev.EAf D)) :
    x ∈ lev D.sp.cm S.gram B.F.βS ((GlobalTheory.FlatVecSum.princ B).levS ψ) ↔
      x ∈ parLev D.sp.cm S.gram B.F.βS (B.levS ψ) ∧ rTup B.F.βS (B.levS ψ) x = 1 := by
  show x ∈ parLev D.sp.cm S.gram B.F.βS (B.levS ψ) ∧ rTup B.F.βS (B.levS ψ) x ∈ (⊥ : Subgroup (G0 B.G.Pg T.rank)) ↔ _
  exact and_congr_right fun _ => Subgroup.mem_bot

section Group

variable {B : Base S T} {ψ : Twist D Circle}

theorem parLev_of_levJ {u : Bridge.Gf S} (h : u ∈ B.levJ ψ) : fE u ∈ parLev D.sp.cm S.gram B.F.βS (B.levS ψ) :=
  lev_le_parLev ((mem_levJ_iff B ψ u).1 h)

theorem tup_eq_of_mem {u v : Bridge.Gf S} (hu : u ∈ B.levJ ψ) (hv : v ∈ B.levJ ψ)
    (h : u⁻¹ * v ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ) :
    rTup B.F.βS (B.levS ψ) (fE u) = rTup B.F.βS (B.levS ψ) (fE v) := by
  have h1 := ((mem_lev_princ B ψ _).1 ((mem_levJ_iff _ ψ _).1 h)).2
  rw [fE_mul, fE_inv, rTup_mul (inv_mem (parLev_of_levJ hu)) (parLev_of_levJ hv), rTup_inv (parLev_of_levJ hu)] at h1
  exact inv_mul_eq_one.1 h1

theorem mem_princ_of_tup {u v : Bridge.Gf S} (hu : u ∈ B.levJ ψ) (hv : v ∈ B.levJ ψ)
    (h : rTup B.F.βS (B.levS ψ) (fE u) = rTup B.F.βS (B.levS ψ) (fE v)) : u⁻¹ * v ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ := by
  refine (mem_levJ_iff _ ψ _).2 ((mem_lev_princ B ψ _).2 ⟨?_, ?_⟩)
  · rw [fE_mul, fE_inv]
    exact mul_mem (inv_mem (parLev_of_levJ hu)) (parLev_of_levJ hv)
  · rw [fE_mul, fE_inv, rTup_mul (inv_mem (parLev_of_levJ hu)) (parLev_of_levJ hv), rTup_inv (parLev_of_levJ hu), h,
      inv_mul_cancel]

variable {F : Finset (Bridge.Gf S)} (hF : ∀ u ∈ F, u ∈ B.levJ ψ)
  (hU : ∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ)
include hF hU

theorem tup_inj {u v : Bridge.Gf S} (hu : u ∈ F) (hv : v ∈ F)
    (h : rTup B.F.βS (B.levS ψ) (fE u) = rTup B.F.βS (B.levS ψ) (fE v)) : u = v := by
  obtain ⟨w, -, hw⟩ := hU v (hF v hv)
  have e1 := hw v ⟨hv, by rw [inv_mul_cancel]; exact one_mem _⟩
  have e2 := hw u ⟨hu, mem_princ_of_tup (hF u hu) (hF v hv) h⟩
  exact e2.trans e1.symm

theorem tup_surj (hB : B.Good) (hQ : B.admitted ψ.Q) {p : G0 B.G.Pg T.rank} (hp : p ∈ B.G.P.H) :
    ∃ u ∈ F, rTup B.F.βS (B.levS ψ) (fE u) = p := by
  obtain ⟨N, hN⟩ := GlobalTheory.TypeSupportLift.exists_isBaseFrame hB.frame.frS hB.frame.sdS
  obtain ⟨R, h1, h2, hR⟩ := hQ.1.split
  obtain ⟨-, κ, -, hall⟩ := GlobalTheory.ParahoricLift.exists_lift_prod S B.F.βS (B.levS ψ) B.F.ΛS N hN
    (fun PP hP PP' hP' => GlobalTheory.ExportType.not_isConjPl_of_splitSet hR (h1 hP) (by rcases hP' with h | h; exacts [h1 h, h2 h]))
    hQ.1.disj p
  obtain ⟨hκ, -⟩ := hall Finset.univ.toList (Finset.nodup_toList _) fun PP => Finset.mem_toList.2 (Finset.mem_univ PP)
  have hkJ : finPt S (List.map κ Finset.univ.toList).prod ∈ B.levJ ψ :=
    (B.finPt_mem_levJ ψ hκ.1).2 ⟨hκ.1, hκ.2.1, by rw [hκ.2.2]; exact hp⟩
  obtain ⟨u, ⟨huF, hu⟩, -⟩ := hU _ hkJ
  refine ⟨u, huF, ?_⟩
  rw [tup_eq_of_mem (hF u huF) hkJ hu, fE_finPt, hκ.2.2]

end Group

section Datum

theorem low_top_left {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) {K : GL (Fin n) κ} (hK : K ∈ blockTri (blk2 r))
    (u : Matrix (Fin n) (Fin r) κ) :
    LowZero r ((K⁻¹).val * u) ∧ topL r ((K⁻¹).val * u) = 1 ↔ LowZero r u ∧ (upperLeftBlock hr K).val = topL r u := by
  have eK : (K⁻¹).val * u = (K⁻¹).val * u * ((1 : GL (Fin r) κ)).val := by rw [Units.val_one, Matrix.mul_one]
  rw [eK, GlobalTheory.AdjDatumMove.lowZero_mul_iff (inv_mem hK)]
  refine and_congr_right fun hu => ?_
  rw [GlobalTheory.AdjDatumMove.topL_mul hr (inv_mem hK) _ hu, Units.val_one, Matrix.mul_one,
    show upperLeftBlock hr K⁻¹ = (upperLeftBlock hr K)⁻¹ from extendOne_inv _ hK, Units.inv_mul_eq_one]

open Classical in
theorem omegaK_left {n r : ℕ} (hr : r ≤ n) (Pg : Finset (Pl D.host.E)) (K : ∀ PP : Pl D.host.E, GL (Fin n) (kP PP))
    (hK : ∀ PP ∈ Pg, K PP ∈ blockTri (blk2 r)) (y : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaK Pg (fun PP => ((K PP)⁻¹).val * y PP) =
      if (∀ PP ∈ Pg, LowZero r (y PP)) ∧ ∀ PP : ↥Pg, (upperLeftBlock hr (K PP.1)).val = topL r (y PP.1) then 1 else 0 := by
  unfold omegaK
  congr 1
  refine propext ⟨fun h => ⟨fun PP hP => ((low_top_left hr (hK PP hP) _).1 (h PP hP)).1,
    fun PP => ((low_top_left hr (hK PP.1 PP.2) _).1 (h PP.1 PP.2)).2⟩, fun h PP hP => ?_⟩
  exact (low_top_left hr (hK PP hP) _).2 ⟨h.1 PP hP, h.2 ⟨PP, hP⟩⟩

theorem flat_mul_right {k R : Type} [CommRing k] [CommRing R] {n r : ℕ} (hr : r ≤ n) (ν : kˣ →* Rˣ) {K : GL (Fin n) k}
    (hK : K ∈ blockTri (blk2 r)) (y : Matrix (Fin r) (Fin n) k) :
    flat ν (y * K.val) = (ν (GeneralLinearGroup.det (upperLeftBlock hr K)) : R) * flat ν y := by
  have e : K = (K⁻¹)⁻¹ := (inv_inv K).symm
  rw [e, flat_mul_inv hr ν (inv_mem hK), show upperLeftBlock hr K⁻¹ = (upperLeftBlock hr K)⁻¹ from extendOne_inv _ hK, map_inv, map_inv, inv_inv,
    ← e]

open Classical in
theorem locFn_right (B : Base S T) (ψ : Twist D Circle) (K : ∀ PP : Pl D.host.E, GL (Fin S.rank) (kP PP))
    (hK : ∀ PP ∈ B.de.Q ∪ ψ.Q, K PP ∈ blockTri (blk2 T.rank)) (y : Reds D T.rank S.rank) :
    B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) (fun PP => y PP * (K PP).val) =
      (((∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (K PP)))) *
        ∏ PP ∈ ψ.Q, ψ.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (K PP))) : ℂˣ) : ℂ) *
        B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y := by
  unfold Base.locFn
  rw [Finset.prod_congr rfl fun PP hP => flat_mul_right B.hr _ (hK PP (Finset.mem_union_left _ hP)) (y PP),
    Finset.prod_congr (s₁ := Finset.univ) rfl fun (PP : ↥ψ.Q) _ => flat_mul_right B.hr _ (hK PP.1 (Finset.mem_union_right _ PP.2)) (y PP.1),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Finset.prod_coe_sort ψ.Q]
  simp only [Units.val_mul, Units.coe_prod]
  ring

end Datum

theorem alg4 {G : Type} [CommGroup G] (a b c d : G) : a * b * (c⁻¹ * d⁻¹) * (c * d) = a * b := by
  rw [← mul_inv, inv_mul_cancel_right]

open Classical in
theorem term_eq (B : Base S T) {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) {g : GA D S}
    (hk : Lev.finE S g ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ)) (y : Reds D S.rank T.rank) (y' : Reds D T.rank S.rank) :
    ((levFn B.F.βS (B.levS ψ) (Lev.finE S g) * vacC B ψ g 1 : ℂˣ) : ℂ) *
      (omegaK B.G.Pg (fun PP => (redFn B.F.βS PP (Lev.finE S g⁻¹)).val * y PP * ((redFn B.F.βT PP (Lev.finE T 1))⁻¹).val) *
        B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1))
          (fun PP => (redFn B.F.βT PP (Lev.finE T 1)).val * y' PP * ((redFn B.F.βS PP (Lev.finE S g⁻¹))⁻¹).val)) =
    (if (∀ PP ∈ B.G.Pg, LowZero T.rank (y PP)) ∧
        ∀ PP : ↥B.G.Pg, (upperLeftBlock B.hr (redFn B.F.βS PP.1 (Lev.finE S g))).val = topL T.rank (y PP.1) then
      ((B.G.P.chi ⟨_, hk.2⟩ : ℂˣ) : ℂ) *
        ∏ PP : ↥B.G.Pg, ((B.G.muC PP.1 (GeneralLinearGroup.det (rTup B.F.βS (B.levS ψ) (Lev.finE S g) PP)) : ℂˣ) : ℂ)⁻¹
      else 0) * B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y' := by
  have hp := lev_le_parLev hk
  have ri : ∀ PP, redFn B.F.βS PP (Lev.finE S g⁻¹) = (redFn B.F.βS PP (Lev.finE S g))⁻¹ := fun PP => by
    rw [map_inv, redFn_inv (parLev_St hp)]
  simp only [finE_one, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul, ri, inv_inv]
  rw [omegaK_left B.hr B.G.Pg _ (fun PP hP => blockTri_blkOf_le _ _ (parLev_g hp hP)) y,
    locFn_right B ψ _ (fun PP hP => parLev_q hp hP) y']
  have hs := dualTypeVacuumScalar_div_levelScalar hQ hk
  have e1 : levFn B.F.βS (B.levS ψ) (Lev.finE S g) * vacC B ψ g 1 = srcC B ψ g hk := by
    rw [mul_inv_eq_iff_eq_mul] at hs
    rw [hs, mul_inv_cancel_left]
  rw [e1]
  split_ifs with h
  · have e2 : srcC B ψ g hk * ((∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (redFn B.F.βS PP (Lev.finE S g))))) *
        ∏ PP ∈ ψ.Q, ψ.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (redFn B.F.βS PP (Lev.finE S g))))) =
        B.G.P.chi ⟨_, hk.2⟩ * ∏ PP ∈ B.G.Pg, (B.G.muC PP (blkA B g PP))⁻¹ := by
      unfold srcC
      rw [Finset.prod_inv_distrib (s := B.de.Q), Finset.prod_inv_distrib (s := ψ.Q)]
      exact alg4 _ _ _ _
    calc _ = ((srcC B ψ g hk * ((∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (redFn B.F.βS PP (Lev.finE S g))))) *
        ∏ PP ∈ ψ.Q, ψ.resC PP (GeneralLinearGroup.det (upperLeftBlock B.hr (redFn B.F.βS PP (Lev.finE S g))))) : ℂˣ) : ℂ) *
          B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y' := by
          simp only [Units.val_mul]; ring
      _ = _ := by
          rw [e2, Units.val_mul, Units.coe_prod, ← Finset.prod_coe_sort B.G.Pg]
          simp only [Units.val_inv_eq_inv_val]
          rfl
  · simp

open Classical in

theorem datum_sum (B : Base S T) {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) {ι : Type} [Fintype ι] (g : ι → GA D S)
    (hk : ∀ i, Lev.finE S (g i) ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ))
    (inj : ∀ i j, rTup B.F.βS (B.levS ψ) (Lev.finE S (g i)) = rTup B.F.βS (B.levS ψ) (Lev.finE S (g j)) → i = j)
    (surj : ∀ p ∈ B.G.P.H, ∃ i, rTup B.F.βS (B.levS ψ) (Lev.finE S (g i)) = p) (x : WO S T) :
    B.F.datumFn B.G (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) x =
      ∑ i, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g i)) * vacC B ψ (g i) 1 : ℂˣ) : ℂ) *
        B.F.datumFn (GlobalTheory.FlatVecSum.princG B.G) (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1))
          (actO S T (g i)⁻¹ 1 x) := by
  have st : ∀ i, Lev.finE S (g i)⁻¹ ∈ St B.F.βS := fun i => by
    rw [map_inv]; exact inv_mem (parLev_St (lev_le_parLev (hk i)))
  have hO := fun i => frMapO_act B.F (st i) (one_mem_St T B.F.βT) x
  have hJ := fun i => frMapAdj_act B.F (st i) (one_mem_St T B.F.βT) x
  have hH : ∀ i, IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) (actO S T (g i)⁻¹ 1 x) ↔ IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) x :=
    fun i => ⟨GlobalTheory.ThetaMove.isHalf_of_act _ _, GlobalTheory.AdjDatumMove.isHalf_actO' _ _⟩
  unfold Frame.datumFn
  simp only [GlobalTheory.FlatVecSum.omegaG_princ, show (GlobalTheory.FlatVecSum.princG B.G).Pg = B.G.Pg from rfl, hH, fun i => (hO i).1,
    fun i => (hJ i).1]
  by_cases c1 : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) x ∧ IsIntM (frMapAdj S T B.F.βS B.F.βT x)
  swap
  · simp only [if_neg c1, zero_mul, mul_zero, Finset.sum_const_zero]
  by_cases c2 : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) x ∧ IsIntM (frMapO S T B.F.βS B.F.βT x)
  swap
  · simp only [if_neg c2, mul_zero, Finset.sum_const_zero]
  simp only [if_pos c1, if_pos c2]
  symm
  calc _ = ∑ i, (if (∀ PP ∈ B.G.Pg, LowZero T.rank (redM PP (frMapAdj S T B.F.βS B.F.βT x))) ∧
        ∀ PP : ↥B.G.Pg, (upperLeftBlock B.hr (redFn B.F.βS PP.1 (Lev.finE S (g i)))).val =
          topL T.rank (redM PP.1 (frMapAdj S T B.F.βS B.F.βT x)) then
        ((B.G.P.chi ⟨_, (hk i).2⟩ : ℂˣ) : ℂ) *
          ∏ PP : ↥B.G.Pg, ((B.G.muC PP.1 (GeneralLinearGroup.det (rTup B.F.βS (B.levS ψ) (Lev.finE S (g i)) PP)) : ℂˣ) : ℂ)⁻¹
        else 0) * B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) (fun PP => redM PP (frMapO S T B.F.βS B.F.βT x)) :=
        Finset.sum_congr rfl fun i _ => by
          rw [funext ((hO i).2 c2.2), funext ((hJ i).2 c1.2)]
          exact term_eq B hQ (hk i) _ _
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      by_cases hy : (∀ PP ∈ B.G.Pg, LowZero T.rank (redM PP (frMapAdj S T B.F.βS B.F.βT x))) ∧
          ∃ g0 : G0 B.G.Pg T.rank, (∀ PP : ↥B.G.Pg, (g0 PP).val = topL T.rank (redM PP.1 (frMapAdj S T B.F.βS B.F.βT x))) ∧
            g0 ∈ B.G.P.H
      · obtain ⟨h0, g0, hg0, hH0⟩ := hy
        obtain ⟨i, rfl⟩ := surj g0 hH0
        rw [omegaG_levT_of B.G h0 _ hg0 hH0, Finset.sum_eq_single i]
        · rw [if_pos ⟨h0, fun PP => hg0 PP⟩]
          rfl
        · intro j _ hj
          rw [if_neg]
          intro hc
          exact hj (inj j i (funext fun PP => Units.ext ((hc.2 PP).trans (hg0 PP).symm)))
        · exact fun h => absurd (Finset.mem_univ _) h
      · rw [omegaG_levT_zero B.G hy]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [if_neg]
        rintro ⟨h0, h1⟩
        exact hy ⟨h0, _, h1, (hk i).2⟩

open Classical in

theorem om_princ_move {B : Base S T} (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q)
    {ω : PairRep S T} (hω : B.IsWeil ψ.chi ω) {g : GA D S} (hg : g ∈ GfC S) (sg : Lev.finE S g ∈ St B.F.βS) :
    ω (g, 1) ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) = (((vacC B ψ g 1 : ℂˣ) : ℂ) * 1) •
      B.F.placeMap (halfIdem B.G.Pg (B.de.Q ∪ ψ.Q)) (fun x => B.F.datumFn (GlobalTheory.FlatVecSum.princG B.G) (B.de.Q ∪ ψ.Q)
        (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) (actO S T g⁻¹ 1 x)) := by
  have hF := hB.frame
  have hsq := hQ.1.isOrthSum.1.idem
  have hinf := hQ.1.isOrthSum.1.infPart_eq
  have hM := Frame.isPlaceModel_placeMap (G := B.G) hF hQ.1
  have hΛ : ∀ a : GA D S, Lev.finE S a ∈ St B.F.βS → ∀ u, u ∈ B.F.lat ↔ actO S T a 1 u ∈ B.F.lat := fun a ha =>
    GlobalTheory.VecInv.mem_latO_iff hF.frS hF.frT ha (one_mem_St T _)
  have hω' : ∀ y y', (∀ PP ∈ B.de.Q ∪ ψ.Q, y PP = y' PP) →
      B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y = B.locFn ψ.Q (fun PP => flat (ψ.resC PP.1)) y' := fun y y' hy => by
    unfold Base.locFn
    rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)],
      Finset.prod_congr (s₁ := Finset.univ) rfl fun PP _ => by rw [hy PP.1 (Finset.mem_union_right _ PP.2)]]
  have hsb := Frame.isSBHalf_datumFn (G := GlobalTheory.FlatVecSum.princG B.G) hF hQ.1 hω'
  have hθ := Frame.isThetaAt_vec (G := GlobalTheory.FlatVecSum.princG B.G) hF hQ.1 hω'
  have sg' : Lev.finE S g⁻¹ ∈ St B.F.βS := by rw [map_inv]; exact inv_mem sg
  have s := GlobalTheory.ThetaMove.isSBHalf_comp _ _ (hΛ g⁻¹ sg') hsb
  refine om_theta_move hω (fun Tm hT Ψ hΨ => GlobalTheory.SchrTheta.isTheta_placeModel D _ hF.vac.1 S T _ _ hF.sdS hF.sdT _ hsq hinf _
    hF.vac.2.theta Tm hT Ψ hΨ) ⟨⟨_, hM⟩, fun _ h₂ => GlobalTheory.PlaceVec.placeModel_unique hF.vac.1 hF.sdS hF.sdT hsq hinf hM h₂ s⟩ hθ
    (hΛ _ sg) (Units.ne_zero _) (om_vac_base hB hS hψ hQ hω hg (one_mem _) sg (one_mem_St T _)) fun x => ?_
  have := GlobalTheory.SplitHecke.actO_inv_actO g (1 : GA D T) x
  rw [inv_one] at this
  rw [one_mul, this]

open Classical in

theorem vec_sum {B : Base S T} (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q)
    {ω : PairRep S T} (hω : B.IsWeil ψ.chi ω) {ι : Type} [Fintype ι] (g : ι → GA D S) (hg : ∀ i, g i ∈ GfC S)
    (hk : ∀ i, Lev.finE S (g i) ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ))
    (inj : ∀ i j, rTup B.F.βS (B.levS ψ) (Lev.finE S (g i)) = rTup B.F.βS (B.levS ψ) (Lev.finE S (g j)) → i = j)
    (surj : ∀ p ∈ B.G.P.H, ∃ i, rTup B.F.βS (B.levS ψ) (Lev.finE S (g i)) = p) :
    ∑ i, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g i)) : ℂˣ) : ℂ) • ω (g i, 1) ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) =
      B.vecFlat ψ := by
  have e : B.F.datumFn B.G (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) =
      ∑ i, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g i)) * vacC B ψ (g i) 1 : ℂˣ) : ℂ) • fun x =>
        B.F.datumFn (GlobalTheory.FlatVecSum.princG B.G) (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1))
          (actO S T (g i)⁻¹ 1 x) := by
    funext x
    rw [datum_sum B hQ g hk inj surj x, Finset.sum_apply]
    rfl
  conv_rhs => rw [Base.vecFlat, Base.vecAt, Frame.vec, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [om_princ_move hB hS hψ hQ hω (hg i) (parLev_St (lev_le_parLev (hk i))), smul_smul, map_smul, mul_one, Units.val_mul]

theorem levLam_eq (B : Base S T) (ψ : Twist D Circle) (u : Bridge.Gf S) (h : u ∈ B.levJ ψ) :
    ((B.levLam ψ ⟨u, h⟩ : ℂˣ) : ℂ) = ((levFn B.F.βS (B.levS ψ) (fE u) : ℂˣ) : ℂ) := by
  have h' : finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S) ∈ B.levJ ψ := (finPt_symm u).symm ▸ h
  have e : (⟨u, h⟩ : B.levJ ψ) = ⟨_, h'⟩ := Subtype.ext (finPt_symm u).symm
  rw [e, B.levLam_finPt ψ h']
  rfl

theorem om_fock {B : Base S T} (hB : B.Good) {ν : (AE D)ˣ →* Circle} {ω : PairRep S T} (hω : B.IsWeil ν ω) {g : GA D S}
    (hg : g ∈ GfC S) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f) (P : Links.PolF D T.rank S.rank) :
    ω (g, 1) (B.F.fock f P) = B.F.fock (ω (g, 1) f) P :=
  (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hB.frame.vac.2.inf _ _ _ _ _ _ _ _ g 1
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hg])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hg])
    (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)]) f hf P).2

theorem sum_om_fock_princ : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (F : Finset (Bridge.Gf S)) (hF : ∀ u ∈ F, u ∈ B.levJ ψ),
    (∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ) →
    ∃ κ : ℂ, ∀ P : Links.PolF D T.rank S.rank,
      ∑ u ∈ F.attach, ((B.levLam ψ ⟨u.1, hF u.1 u.2⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S), 1) (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) P) =
      κ • B.F.fock (B.vecFlat ψ) P := by
  intro D S T B hB hS ψ hψ hQ ω hω F hF hU
  refine ⟨1, fun P => ?_⟩
  have hB0 := GlobalTheory.FlatVecSum.princ_good hB
  have hQ0 : (GlobalTheory.FlatVecSum.princ B).admitted ψ.Q := hQ
  have hf0 : IsThetaFunO B.F.ψ S T ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB0.frame.vac.1 hB0.frame.vac.2.inf (Base.isThetaAt_vecAt hB0 hQ0 _) hB0.frame.vac.2.theta
  let g : {x // x ∈ F} → GA D S := fun u => (((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S)
  have hg : ∀ u, g u ∈ GfC S := fun u => ((GlobalTheory.ClassRegroup.finEquiv S).symm u.1).2
  have hk : ∀ u, Lev.finE S (g u) ∈ lev D.sp.cm S.gram B.F.βS (B.levS ψ) := fun u => (mem_levJ_iff B ψ u.1).1 (hF u.1 u.2)
  have inj : ∀ u v, rTup B.F.βS (B.levS ψ) (Lev.finE S (g u)) = rTup B.F.βS (B.levS ψ) (Lev.finE S (g v)) → u = v :=
    fun u v h => Subtype.ext (tup_inj hF hU u.2 v.2 h)
  have surj : ∀ p ∈ B.G.P.H, ∃ u, rTup B.F.βS (B.levS ψ) (Lev.finE S (g u)) = p := fun p hp => by
    obtain ⟨u, hu, e⟩ := tup_surj hF hU hB hQ hp
    exact ⟨⟨u, hu⟩, e⟩
  have hv := vec_sum hB hS hψ hQ hω g hg hk inj surj
  have hth : ∀ u ∈ (Finset.univ : Finset {x // x ∈ F}), IsThetaFunO B.F.ψ S T (ω (g u, 1) ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)) :=
    fun u _ => hω.om_pres _ _ hf0
  rw [one_smul, ← Finset.univ_eq_attach]
  calc _ = ∑ u, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g u)) : ℂˣ) : ℂ) •
        B.F.fock (ω (g u, 1) ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)) P :=
        Finset.sum_congr rfl fun u _ => by
          rw [levLam_eq B ψ u.1 (hF u.1 u.2)]
          exact congrArg₂ (· • ·) rfl (om_fock hB hω (hg u) hf0 P)
    _ = B.F.fock (∑ u, ((levFn B.F.βS (B.levS ψ) (Lev.finE S (g u)) : ℂˣ) : ℂ) •
        ω (g u, 1) ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)) P :=
        (GlobalTheory.SpecFac.pureTensorO_sum hB.frame.vac.1 hB.frame.vac.2.inf _ _ _ _ _ _ _ hth P).symm
    _ = _ := by rw [hv]

end GlobalTheory.LevTransl
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_twistedSum_fockVectors_principalDatum : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (F : Finset (Bridge.Gf S)) (hF : ∀ u ∈ F, u ∈ B.levJ ψ),
    (∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ) →
    ∃ κ : ℂ, ∀ P : Links.PolF D T.rank S.rank,
      ∑ u ∈ F.attach, ((B.levLam ψ ⟨u.1, hF u.1 u.2⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S), 1) (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) P) =
      κ • B.F.fock (B.vecFlat ψ) P := by
  first | exact @GlobalTheory.LevTransl.sum_om_fock_princ | exact GlobalTheory.LevTransl.sum_om_fock_princ | (intros; apply GlobalTheory.LevTransl.sum_om_fock_princ <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

namespace GlobalTheory.ClassSumPrinc

theorem ratF_injective {D : D7} (S : HSp D) : Function.Injective (Bridge.ratF S) := by
  refine (injective_iff_map_eq_one _).2 fun γ hγ => ?_
  have h1 : GlobalTheory.ClassRegroup.finPt S (γ : GA D S) = 1 := by
    show (GlobalTheory.ClassRegroup.finEquiv S).symm ((finHom S).rangeRestrict (γ : GA D S)) = 1
    have : (finHom S).rangeRestrict (γ : GA D S) = 1 := hγ
    rw [this, map_one]
  exact Subtype.ext (GlobalTheory.ClassRegroup.eq_one_of_finPt S γ.2 h1)

end GlobalTheory.ClassSumPrinc

namespace GlobalTheory.ClassSumPrinc

theorem symm_finPt {D : D7} (S : HSp D) {k : GA D S} (hk : k ∈ GfC S) :
    (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S k) : GfC S) : GA D S) = k := by
  have : (GlobalTheory.ClassRegroup.finEquiv S) ⟨k, hk⟩ = finPt S k := rfl
  rw [← this, MulEquiv.symm_apply_apply]

theorem inner_sum {D : D7} {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) (ω : PairRep S T)
    {Fs : Finset (Bridge.Gf S)} (hF : ∀ u ∈ Fs, u ∈ B.levJ ψ) {κ : ℂ}
    (hκ : ∀ P : Links.PolF D T.rank S.rank,
      ∑ u ∈ Fs.attach, ((B.levLam ψ ⟨u.1, hF u.1 u.2⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S), 1) (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) P) =
      κ • B.F.fock (B.vecFlat ψ) P)
    {F : Bridge.Gf S → Links.PolF D T.rank S.rank} (hlaw : B.HasLaw ψ F) {x : GA D S} (hx : x ∈ GfC S) (g : GA D T) :
    ∑ u ∈ Fs, series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)
        (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) (F (finPt S x * u)) g =
      κ * series B.F ω (B.vecFlat ψ) x (F (finPt S x)) g := by
  have hu : ∀ u (hu : u ∈ Fs), series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)
      (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) (F (finPt S x * u)) g =
      ω (x, g) (((B.levLam ψ ⟨u, hF u hu⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), 1)
          (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (F (finPt S x)))) 0 := by
    intro u hu
    have e1 : F (finPt S x * u) = ((B.levLam ψ ⟨u, hF u hu⟩ : ℂˣ) : ℂ) • F (finPt S x) := by
      have := hlaw 1 (finPt S x) ⟨u, hF u hu⟩
      rw [map_one, one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply] at this
      exact this
    have e2 : (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) =
        x * (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S) := by
      have e3 := map_mul (GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x) u
      rw [e3, Subgroup.coe_mul, symm_finPt S hx]
    rw [series_apply, e2]
    simp only [e1, map_smul]
    have e4 : ω (x * (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), g) =
        ω (x, g) * ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    have e5 := LinearMap.congr_fun e4 (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (F (finPt S x)))
    rw [Module.End.mul_apply] at e5
    simp only [e5]
  rw [← Finset.sum_attach Fs, Finset.sum_congr rfl fun u _ => hu u.1 u.2]
  rw [← Finset.sum_apply, ← map_sum, hκ, map_smul, Pi.smul_apply, smul_eq_mul, series_apply]

theorem classSum_princ_eq : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (m : ℕ) (h₀ : Fin m → GA D S), IsClassSystem S ((GlobalTheory.FlatVecSum.princ B).levJ ψ) h₀ →
    ∀ (I : Type) [Fintype I] (h : I → GA D S), IsClassSystem S (B.levJ ψ) h →
    ∃ κ : ℂ, ∀ F ∈ B.formsC ψ, (GlobalTheory.FlatVecSum.princ B).classSum ω ψ h₀ F = κ • B.classSum ω ψ h F := by
  intro D S T B hB hS ψ hψ hQ ω hω m h₀ hC₀ I _ h hC
  obtain ⟨hle, -⟩ := GlobalTheory.T.principalLevel_le_level_characters_agree B hB ψ hQ
  obtain ⟨Fs, hF, hFu⟩ := GlobalTheory.T.finite_coset_representatives_level B hB ψ hQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_const_twistedSum_fockVectors_principalDatum B hB hS ψ hψ hQ ω hω Fs hF hFu
  refine ⟨κ, fun F hFm => ?_⟩
  have hinv := GlobalTheory.T.classSumTerms_invariant_principalLevel B hB hS ψ hψ hQ ω hω F hFm
  have hlaw := ((B.mem_formsC).1 hFm).2
  funext g
  rw [Base.classSum_apply, Base.classSum_apply, Finset.sum_apply, Pi.smul_apply, Finset.sum_apply]
  have key := GlobalTheory.T.classSum_regroup_finerLevel_cosets (Bridge.ratF S) (ratF_injective S) hle hF hFu (fun i => finPt S (h₀ i)) hC₀.reps
    (fun i => finPt S (h i)) hC.reps
    (fun y => series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g)
    (fun γ y => (hinv g).1 γ y) (fun k hk y => (hinv g).2 k hk y)
  simp only [symm_finPt S (hC₀.fin _), inner_sum B ψ ω hF hκ hlaw (hC.fin _)] at key
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, show (GlobalTheory.FlatVecSum.princ B).F = B.F from rfl]
  rw [key, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.ClassSumPrinc
end
end
