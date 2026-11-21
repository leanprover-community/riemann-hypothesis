import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExistsHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicPartEqSpanScaledFrameUnitriangular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedUnimodularLatticeIffLocalCompletions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary
import BuildAid.ForwardExisting
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob
import Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfLocalDiscriminant
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver

section
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.StdDual

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section Form

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map ((M.L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_zero_right (x : V) : H.h x 0 = 0 := by
  have := h_smul_right H 0 x 0
  simpa using this

theorem h_neg_left (x y : V) : H.h (-x) y = - H.h x y := by
  have := H.h_smul_left (-1) x y
  simpa using this

theorem h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, H.h_add_left, h_neg_left, ← sub_eq_add_neg]

theorem h_neg_right (x y : V) : H.h x (-y) = - H.h x y := by
  have := h_smul_right H (-1) x y
  simpa using this

theorem h_sub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [sub_eq_add_neg, h_add_right, h_neg_right, ← sub_eq_add_neg]

theorem h_sum_left {ι : Type*} (s : Finset ι) (c : ι → E) (u : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • u i) y = ∑ i ∈ s, c i * H.h (u i) y := by
  refine Finset.induction_on s ?_ ?_
  · simpa using H.h_zero_left y
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

theorem h_sum_right {ι : Type*} (s : Finset ι) (c : ι → E) (u : ι → V) (x : V) :
    H.h x (∑ i ∈ s, c i • u i) = ∑ i ∈ s, M.L.cj (c i) * H.h x (u i) := by
  refine Finset.induction_on s ?_ ?_
  · simpa using h_zero_right H x
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_right, h_smul_right, ih]

theorem int_span_right (x : V) (S : Set V) (hS : ∀ y ∈ S, H.h x y ∈ M.L.O) :
    ∀ y ∈ Submodule.span M.L.O S, H.h x y ∈ M.L.O := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => exact hS y h
  | zero => rw [h_zero_right]; exact M.L.O.zero_mem
  | add y z _ _ h1 h2 => rw [h_add_right]; exact M.L.O.add_mem h1 h2
  | smul c y _ h =>
    rw [show (c • y : V) = (c : E) • y from rfl, h_smul_right]
    exact M.L.O.mul_mem (cj_mem c.2) h

theorem int_span_left (S : Set V) (y : V) (hS : ∀ x ∈ S, H.h x y ∈ M.L.O) :
    ∀ x ∈ Submodule.span M.L.O S, H.h x y ∈ M.L.O := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact hS x h
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add x z _ _ h1 h2 => rw [H.h_add_left]; exact M.L.O.add_mem h1 h2
  | smul c x _ h =>
    rw [show (c • x : V) = (c : E) • x from rfl, H.h_smul_left]
    exact M.L.O.mul_mem c.2 h

end Form

section Frame

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
  (Fr : LocNG.FrameD H r)

theorem h_e_e (a b : Fin r) : H.h (Fr.e a) (Fr.e b) = 0 :=
  Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)

theorem h_e_es (a b : Fin r) : H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := Fr.h_es a b

theorem h_es_e (a b : Fin r) : H.h (Fr.es b) (Fr.e a) = if a = b then 1 else 0 := by
  rw [H.h_herm, h_e_es]; split_ifs <;> simp

theorem h_prF_e (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.e b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp [h_e_e, h_es_e]

theorem h_prF_es (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.es b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp [h_e_es, Fr.h_ss]

theorem h_e_prF (v : V) (b : Fin r) : H.h (Fr.e b) (Fr.prF v) = 0 := by
  rw [H.h_herm, h_prF_e, map_zero]

theorem h_es_prF (v : V) (b : Fin r) : H.h (Fr.es b) (Fr.prF v) = 0 := by
  rw [H.h_herm, h_prF_es, map_zero]

theorem decomp (v : V) :
    v = ∑ a, H.h v (Fr.es a) • Fr.e a + Fr.prF v + ∑ a, H.h v (Fr.e a) • Fr.es a := by
  unfold FrameD.prF; abel

theorem h_left_prF (v u : V) : H.h v (Fr.prF u) = H.h (Fr.prF v) (Fr.prF u) := by
  conv_lhs => rw [decomp Fr v]
  rw [H.h_add_left, H.h_add_left, h_sum_left, h_sum_left]
  simp [h_e_prF, h_es_prF]

theorem h_prF_right (w y : V) (h1 : ∀ a, H.h w (Fr.e a) = 0) (h2 : ∀ a, H.h w (Fr.es a) = 0) :
    H.h w (Fr.prF y) = H.h w y := by
  unfold FrameD.prF
  rw [h_sub_right, h_sub_right, h_sum_right, h_sum_right]
  simp [h1, h2]

theorem h_expand (v u : V) : H.h v u = ∑ a, M.L.cj (H.h u (Fr.es a)) * H.h v (Fr.e a) +
    H.h v (Fr.prF u) + ∑ a, M.L.cj (H.h u (Fr.e a)) * H.h v (Fr.es a) := by
  conv_lhs => rw [decomp Fr u]
  rw [h_add_right, h_add_right, h_sum_right, h_sum_right]

theorem prF_mem_perp (v : V) : Fr.prF v ∈ H.perp (H.X Fr.f) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨a, rfl⟩ := h; exact h_prF_e Fr v a
  | zero => exact h_zero_right H _
  | add x z _ _ h1 h2 => rw [h_add_right, h1, h2, add_zero]
  | smul c x _ h => rw [h_smul_right, h, mul_zero]

theorem prF_prF (v : V) : Fr.prF (Fr.prF v) = Fr.prF v := by
  show Fr.prF v - ∑ a, H.h (Fr.prF v) (Fr.es a) • Fr.e a - ∑ a, H.h (Fr.prF v) (Fr.e a) • Fr.es a = Fr.prF v
  simp [h_prF_e, h_prF_es]

def gen (L : Submodule M.L.O (H.Wb Fr.f)) : Set V :=
  {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
    ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L}

theorem lamStd_eq (L : Submodule M.L.O (H.Wb Fr.f)) : Fr.LamStd L = Submodule.span M.L.O (gen Fr L) := rfl

theorem e_mem (L : Submodule M.L.O (H.Wb Fr.f)) (j : Fin r) : Fr.e j ∈ gen Fr L := by
  have hp : Fr.prF (Fr.e j) = 0 := by
    unfold FrameD.prF
    simp [h_e_es, h_e_e]
  refine ⟨fun a => ?_, fun a => ?_, 0, by simp [hp], by simp⟩
  · rw [h_e_es]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  · rw [h_e_e]; exact M.L.O.zero_mem

theorem es_mem (L : Submodule M.L.O (H.Wb Fr.f)) (j : Fin r) : Fr.es j ∈ gen Fr L := by
  have hp : Fr.prF (Fr.es j) = 0 := by
    unfold FrameD.prF
    simp [h_es_e, Fr.h_ss]
  refine ⟨fun a => ?_, fun a => ?_, 0, by simp [hp], by simp⟩
  · rw [Fr.h_ss]; exact M.L.O.zero_mem
  · rw [h_es_e]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem

theorem prF_gen (L : Submodule M.L.O (H.Wb Fr.f)) (y : ↥(H.perp (H.X Fr.f))) (hy : H.mkW Fr.f y ∈ L) :
    Fr.prF y ∈ gen Fr L := by
  have hy0 : ∀ a, H.h y (Fr.e a) = 0 := fun a => y.2 _ (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF y, prF_mem_perp Fr y⟩, (prF_prF Fr y).symm, ?_⟩
  · rw [h_prF_es]; exact M.L.O.zero_mem
  · rw [h_prF_e]; exact M.L.O.zero_mem
  · have hd : Fr.prF (y : V) - y = -(∑ a, H.h y (Fr.es a) • Fr.e a) := by
      unfold FrameD.prF
      simp [hy0]
    have heq : H.mkW Fr.f ⟨Fr.prF y, prF_mem_perp Fr y⟩ = H.mkW Fr.f y := by
      unfold HermSp.mkW
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      show Fr.prF (y : V) - y ∈ H.X Fr.f
      rw [hd]
      exact neg_mem (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    rw [heq]; exact hy

end Frame

section SelfDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
  (Fr : LocNG.FrameD H r)

theorem gen_pair (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L) {v u : V}
    (hv : v ∈ gen Fr L) (hu : u ∈ gen Fr L) : H.h v u ∈ M.L.O := by
  obtain ⟨hv1, hv2, wv, hwv, hwvL⟩ := hv
  obtain ⟨hu1, hu2, wu, hwu, hwuL⟩ := hu
  rw [h_expand Fr, h_left_prF, ← hwv, ← hwu]
  refine M.L.O.add_mem (M.L.O.add_mem ?_ ((hL.2.1 wv).1 hwvL wu hwuL)) ?_
  · exact M.L.O.sum_mem fun a _ => M.L.O.mul_mem (cj_mem (hu1 a)) (hv2 a)
  · exact M.L.O.sum_mem fun a _ => M.L.O.mul_mem (cj_mem (hu2 a)) (hv1 a)

theorem lamStd_selfDual (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L) (x : V) :
    x ∈ Fr.LamStd L ↔ ∀ y ∈ Fr.LamStd L, H.h x y ∈ M.L.O := by
  rw [lamStd_eq]
  constructor
  · intro hx y hy
    refine int_span_left H _ y ?_ x hx
    intro x' hx'
    exact int_span_right H x' _ (fun y' hy' => gen_pair Fr L hL hx' hy') y hy
  · intro h
    apply Submodule.subset_span
    refine ⟨fun a => h _ (Submodule.subset_span (es_mem Fr L a)),
      fun a => h _ (Submodule.subset_span (e_mem Fr L a)), ⟨Fr.prF x, prF_mem_perp Fr x⟩, rfl, ?_⟩
    rw [hL.2.1]
    intro y hy
    have := h _ (Submodule.subset_span (prF_gen Fr L y hy))
    rwa [h_left_prF, h_prF_right Fr _ _ (h_prF_e Fr x) (h_prF_es Fr x)] at this

theorem img_selfDual (g : V ≃ₗ[E] V) (hg : IsUnitary H g) (Λ : Submodule M.L.O V)
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, H.h x y ∈ M.L.O) (x : V) :
    x ∈ img g Λ ↔ ∀ y ∈ img g Λ, H.h x y ∈ M.L.O := by
  have hm : ∀ z, z ∈ img g Λ ↔ g.symm z ∈ Λ := by
    intro z
    unfold img
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hz
      exact ⟨g.symm z, hz, by simp⟩
  rw [hm, hΛ]
  constructor
  · intro h y hy
    rw [hm] at hy
    have := h _ hy
    rwa [← hg, g.apply_symm_apply, g.apply_symm_apply] at this
  · intro h y hy
    rw [← hg (g.symm x) y, g.apply_symm_apply]
    exact h (g y) (by rw [hm]; simpa using hy)

theorem N_unitary {g : V ≃ₗ[E] V} (hg : g ∈ Fr.N) : IsUnitary H g := by
  induction hg using Subgroup.closure_induction with
  | mem g h => exact h.1
  | one => intro x y; rfl
  | mul a b _ _ ha hb =>
    intro x y
    show H.h (a (b x)) (a (b y)) = H.h x y
    rw [ha, hb]
  | inv a _ ha =>
    intro x y
    show H.h (a.symm x) (a.symm y) = H.h x y
    rw [← ha (a.symm x) (a.symm y)]
    simp

theorem img_lamStd_selfDual {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) (x : V) :
    x ∈ img n (Fr.LamStd L) ↔ ∀ y ∈ img n (Fr.LamStd L), H.h x y ∈ M.L.O :=
  img_selfDual n (N_unitary Fr hn) _ (lamStd_selfDual Fr L hL) x

end SelfDual

section Global

variable {D : D7}

theorem mem_iff_local (Z : LocDat D) (Λ : LV D) (hΛ : Submodule.IsLattice D.host.E Λ) (x : (VS D).V) :
    x ∈ Λ ↔ ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Λ := by
  have r := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) (LatLoc.isLattice_map _ _ hΛ)).1
    (LatLoc.cE D x)
  simp only [← LatLoc.localLattice_eq, ← LatLoc.baseChange_eq] at r
  refine Iff.trans ?_ r
  unfold LatLoc.cL
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := (LatLoc.cE D).injective hyx
    rwa [← this]

theorem unimodular_of_local : ∀ (D : D7) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS) (Λ : LV D), Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  intro D Z A Λ hΛ hloc
  have hsd : ∀ p x, x ∈ lattice₂ D Z.M p Λ ↔ ∀ y ∈ lattice₂ D Z.M p Λ, LocFacts₂ Z.M p x y ∈ (Z.M p).L.O := by
    intro p
    obtain ⟨n, hn, L, hL, he⟩ := hloc p
    rw [he]
    exact img_lamStd_selfDual (A p) hn L hL
  have hsub : ∀ p, ∀ x ∈ Λ, baseChange₂ D p x ∈ lattice₂ D Z.M p Λ := fun p x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  have hform : ∀ p x y, LocFacts₂ Z.M p (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) :=
    fun p x y => baseChangeAt_form Z.M p (Z.hcj p) x y
  unfold Formalism.HermitianLatticesTheory.IsUnimodular
  ext x
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  constructor
  · intro hx
    rw [mem_iff_local Z Λ hΛ]
    intro p
    rw [hsd]
    refine int_span_right (locH Z p) _ _ ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨o, ho⟩ := hx y hy
    show LocFacts₂ Z.M p (baseChange₂ D p x) (baseChange₂ D p y) ∈ _
    rw [hform, ← ho]
    exact GlobalTheory.HL.PlacesRec.int_mem (GlobalTheory.HL.placesOf Z) p o
  · intro hx y hy
    obtain ⟨o, ho⟩ := ((GlobalTheory.HL.PlacesInt.integers_local (GlobalTheory.HL.placesOf Z)).1 ((VS D).hT y x)).1
      (fun p => by
        have := (hsd p (baseChange₂ D p x)).1 (hsub p x hx) (baseChange₂ D p y) (hsub p y hy)
        rwa [hform] at this)
    exact ⟨o, ho⟩

end Global

end GlobalTheory.Unfold.StdDual
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnimodular_of_local_standardLattice_translates : ∀ (D : D7) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS) (Λ : LV D), Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  atlas_forward_decl GlobalTheory.Unfold.StdDual.unimodular_of_local
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.IsotropicLift

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def kerR (H : HermSp M V) (w : V) : Submodule E V where
  carrier := {v | H.h v w = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [H.h_add_left, ha, hb, add_zero]
  zero_mem' := H.h_zero_left w
  smul_mem' c v hv := by
    simp only [Set.mem_setOf_eq] at *
    rw [H.h_smul_left, hv, mul_zero]

theorem h_swap_zero (H : HermSp M V) {x y : V} (h : H.h x y = 0) : H.h y x = 0 := by
  rw [H.h_herm, h]; simp

theorem X_le_perp (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, rfl⟩
  intro x hx
  have hk : H.X Fr.f ≤ kerR H (Fr.f b.castSucc) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Fr.h_iso a.castSucc b.castSucc (Or.inl (Fin.castSucc_ne_last a))
  exact h_swap_zero H (hk hx)

theorem sub_mem_X_of_mem_N (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    {v : V} (hv : v ∈ H.perp (H.X Fr.f)) : n v - v ∈ H.X Fr.f := by
  have hXP := X_le_perp H Fr
  suffices key : ∀ g ∈ Fr.N, ∀ v ∈ H.perp (H.X Fr.f), g v - v ∈ H.X Fr.f ∧ g.symm v - v ∈ H.X Fr.f from
    (key n hn v hv).1
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨hu, -, hperp⟩ := hg
    intro v hv
    refine ⟨hperp v hv, ?_⟩
    have hw : g.symm v ∈ H.perp (H.X Fr.f) := by
      intro x hx
      have hgx : g x ∈ H.X Fr.f := by
        have := hperp x (hXP hx)
        have e : g x = (g x - x) + x := by abel
        rw [e]; exact Submodule.add_mem _ this hx
      rw [← hu (g.symm v) x, LinearEquiv.apply_symm_apply]
      exact hv _ hgx
    have h1 := hperp _ hw
    rw [LinearEquiv.apply_symm_apply] at h1
    have e : g.symm v - v = -(v - g.symm v) := by abel
    rw [e]; exact Submodule.neg_mem _ h1
  | one =>
    intro v _
    exact ⟨by simp, by show v - v ∈ _; simp⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    intro v hv
    have hm : ∀ x, (g₁ * g₂) x = g₁ (g₂ x) := fun _ => rfl
    have hms : ∀ x, (g₁ * g₂).symm x = g₂.symm (g₁.symm x) := fun _ => rfl
    obtain ⟨a2, b2⟩ := ih₂ v hv
    obtain ⟨a1, b1⟩ := ih₁ v hv
    have hv2 : g₂ v ∈ H.perp (H.X Fr.f) := by
      have e : g₂ v = (g₂ v - v) + v := by abel
      rw [e]; exact Submodule.add_mem _ (hXP a2) hv
    have hv1 : g₁.symm v ∈ H.perp (H.X Fr.f) := by
      have e : g₁.symm v = (g₁.symm v - v) + v := by abel
      rw [e]; exact Submodule.add_mem _ (hXP b1) hv
    refine ⟨?_, ?_⟩
    · rw [hm]
      have e : g₁ (g₂ v) - v = (g₁ (g₂ v) - g₂ v) + (g₂ v - v) := by abel
      rw [e]; exact Submodule.add_mem _ (ih₁ _ hv2).1 a2
    · rw [hms]
      have e : g₂.symm (g₁.symm v) - v = (g₂.symm (g₁.symm v) - g₁.symm v) + (g₁.symm v - v) := by abel
      rw [e]; exact Submodule.add_mem _ (ih₂ _ hv1).2 b1
  | inv g _ ih =>
    intro v hv
    exact ⟨(ih v hv).2, (ih v hv).1⟩

theorem z_mem_LamStd (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)}
    (hL : Fr.IsInner L) : Fr.z ∈ Fr.LamStd L := by
  obtain ⟨-, -, xz, hxz, hxzL, -⟩ := hL
  have hs : ∀ a, H.h Fr.z (Fr.es a) = 0 := fun a => h_swap_zero H (Fr.h_sz a)
  have he : ∀ a, H.h Fr.z (Fr.e a) = 0 := fun a =>
    Fr.h_iso (Fin.last r) a.castSucc (Or.inr (Fin.castSucc_ne_last a))
  refine Submodule.subset_span ⟨fun a => ?_, fun a => ?_, xz, ?_, hxzL⟩
  · rw [hs a]; exact zero_mem _
  · rw [he a]; exact zero_mem _
  · rw [hxz]
    simp [FrameD.prF, hs, he]

end Gen

variable {D : D7}

theorem exists_add_mem : ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D)
    (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS),
    (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D,
    Submodule.IsLattice D.host.E Λ →
    (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) →
    ∃ x ∈ G.fl.X, G.fl.z + x ∈ Λ := by
  intro D T G Z A hA Λ hΛ hloc
  obtain ⟨π, hπX, hπmem⟩ : ∃ π : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ x ∈ G.fl.X, π x = x) ∧ ∀ x, π x ∈ G.fl.X := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective G.fl.X.subtype (Submodule.ker_subtype _)
    refine ⟨G.fl.X.subtype ∘ₗ g, fun x hx => ?_, fun x => (g x).2⟩
    have := congrArg (fun f => ((f ⟨x, hx⟩ : G.fl.X) : (VS D).V)) hg
    exact this
  obtain ⟨Λ₁, hΛ₁⟩ : ∃ N : LV D, N = Λ ⊔ Submodule.span (𝓞 D.host.E) {G.fl.z} := ⟨_, rfl⟩
  obtain ⟨Λ₂, hΛ₂⟩ : ∃ N : LV D, N = Λ ⊔ Λ₁.map (π.restrictScalars (𝓞 D.host.E)) := ⟨_, rfl⟩
  have hfg : Λ₂.FG := by
    rw [hΛ₂, hΛ₁]; exact hΛ.fg.sup ((hΛ.fg.sup (Submodule.fg_span_singleton _)).map _)
  have hz : G.fl.z ∈ Λ₂ := by
    refine GlobalTheory.GenMass.GlueLoc.mem_of_bcP Z hfg fun p => ?_
    obtain ⟨n, hn, L, hL, hlat⟩ := hloc p
    have hzp : (A p).z = baseChange₂ D p G.fl.z := by
      show (A p).f (Fin.last _) = _
      rw [hA p]
      simp [frFac, frame, FlagG.fvec]
    have hperp : (A p).z ∈ (locH Z p).perp ((locH Z p).X (A p).f) := by
      obtain ⟨-, -, xz, hxz, -, -⟩ := hL
      rw [← hxz]; exact xz.2
    have hnz : n (A p).z ∈ lattice₂ D Z.M p Λ := by
      rw [hlat]
      exact Submodule.mem_map_of_mem (z_mem_LamStd _ (A p) hL)
    have hxX := sub_mem_X_of_mem_N _ (A p) hn hperp
    have hfix : (locH Z p).X (A p).f ≤ LinearMap.eqLocus (GlobalTheory.LocExt.locEnd p π) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      show (GlobalTheory.LocExt.locEnd p π) ((A p).f a.castSucc) = (A p).f a.castSucc
      rw [hA p]
      rw [map_smul, GlobalTheory.LocExt.locEnd_bcP, GlobalTheory.LocExt.frame_castSucc,
        hπX _ (Submodule.subset_span ⟨a, rfl⟩)]
      show _ = frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)
      rw [GlobalTheory.LocExt.frame_castSucc]
    have hx1 : n (A p).z - (A p).z ∈ lattice₂ D Z.M p Λ₁ := by
      rw [hΛ₁]
      refine Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz) ?_
      rw [hzp]
      exact Submodule.subset_span ⟨G.fl.z, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), rfl⟩
    have hx2 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) ∈ lattice₂ D Z.M p (Λ₁.map (π.restrictScalars (𝓞 D.host.E))) := by
      rw [GlobalTheory.FrameProj.localLattice_map Z p π (GlobalTheory.LocExt.locEnd p π) (fun x => (GlobalTheory.LocExt.locEnd_bcP p π x).symm) Λ₁]
      exact Submodule.mem_map_of_mem hx1
    have hx3 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) = n (A p).z - (A p).z := hfix hxX
    rw [hx3] at hx2
    have e : baseChange₂ D p G.fl.z = n (A p).z - (n (A p).z - (A p).z) := by rw [hzp]; abel
    rw [e, hΛ₂]
    exact Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz)
      (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_right hx2)
  rw [hΛ₂] at hz
  obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.1 hz
  obtain ⟨w, -, rfl⟩ := hy
  refine ⟨-(π w), Submodule.neg_mem _ (hπmem w), ?_⟩
  have e : G.fl.z + -(π w) = l := by
    rw [← hly]; simp
  rw [e]; exact hl

end GlobalTheory.IsotropicLift
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_add_isotropicSpan_mem_locallyStandardLattice : ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ x ∈ G.fl.X, G.fl.z + x ∈ Λ := by
  atlas_forward_decl GlobalTheory.IsotropicLift.exists_add_mem
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FramePrim

section Quad

open ValuativeRel Polynomial

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E)

theorem exists_quad (L : Formalism.MainNotions.S.Loc.LocE F E) (d : E) : ∃ t n : F, d * d - algebraMap F E t * d + algebraMap F E n = 0 := by
  haveI := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  set f : E →ₗ[F] E := Algebra.lmul F E d with hf
  have hmon : f.charpoly.Monic := LinearMap.charpoly_monic f
  have hdeg : f.charpoly.natDegree = 2 := by rw [LinearMap.charpoly_natDegree, L.rank]
  have h0 : aeval d f.charpoly = 0 := by
    have h1 := LinearMap.aeval_self_charpoly f
    have h2 : aeval f f.charpoly = Algebra.lmul F E (aeval d f.charpoly) := by
      rw [hf, Polynomial.aeval_algHom_apply]
    rw [h2] at h1
    have h3 := LinearMap.congr_fun h1 1
    simpa using h3
  have hs := hmon.as_sum
  rw [hdeg] at hs
  rw [hs] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, pow_zero, pow_one, mul_one] at h0
  refine ⟨-f.charpoly.coeff 1, f.charpoly.coeff 0, ?_⟩
  rw [map_neg]
  linear_combination h0

theorem mem_O_of_quad (x : E) (a b : F) (h : x * x - algebraMap F E a * x + algebraMap F E b = 0)
    (ha : valuation F a ≤ 1) (hb : valuation F b ≤ 1) : x ∈ L.O := by
  rw [L.O_def]
  set a' : (valuation F).integer := ⟨a, (Valuation.mem_integer_iff _ _).2 ha⟩
  set b' : (valuation F).integer := ⟨b, (Valuation.mem_integer_iff _ _).2 hb⟩
  refine ⟨X ^ 2 - C a' * X + C b', ?_, ?_⟩
  · monicity!
  · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X]
    have ea : algebraMap (valuation F).integer E a' = algebraMap F E a := rfl
    have eb : algebraMap (valuation F).integer E b' = algebraMap F E b := rfl
    rw [ea, eb]
    linear_combination h

theorem inv_mem_O_of_quad (u : E) (t n : F) (h : u * u - algebraMap F E t * u + algebraMap F E n = 0)
    (hn : 1 ≤ valuation F n) (ht : valuation F t ≤ valuation F n) : ∃ w ∈ L.O, u * w = 1 := by
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0, map_zero] at hn; exact absurd hn (not_le.2 zero_lt_one)
  have hvn : valuation F n ≠ 0 := by rw [Ne, map_eq_zero]; exact hn0
  refine ⟨algebraMap F E n⁻¹ * (algebraMap F E t - u), ?_, ?_⟩
  · refine mem_O_of_quad L _ (t * n⁻¹) n⁻¹ ?_ ?_ ?_
    · have e : algebraMap F E n * algebraMap F E n⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hn0, map_one]
      simp only [map_mul]
      linear_combination (algebraMap F E n⁻¹ * algebraMap F E n⁻¹) * h - algebraMap F E n⁻¹ * e
    · rw [map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ ht zero_le'
    · rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn
  · have e : algebraMap F E n * algebraMap F E n⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hn0, map_one]
    linear_combination (-(algebraMap F E n⁻¹)) * h + e

theorem exists_shift_inv : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (d : E), d ∉ L.O →
    ∃ s ∈ L.O, ∃ w ∈ L.O, (d + s) * w = 1 := by
  intro F _ _ _ E _ _ _ L d hd
  obtain ⟨t, n, h⟩ := exists_quad L d
  have hnot : ¬ (valuation F t ≤ 1 ∧ valuation F n ≤ 1) := fun hh => hd (mem_O_of_quad L d t n h hh.1 hh.2)
  by_cases hc : 1 ≤ valuation F n ∧ valuation F t ≤ valuation F n
  · obtain ⟨w, hw, hdw⟩ := inv_mem_O_of_quad L d t n h hc.1 hc.2
    exact ⟨0, L.O.zero_mem, w, hw, by rw [add_zero]; exact hdw⟩
  · have ht1 : 1 < valuation F t ∧ valuation F n < valuation F t := by
      by_cases h1 : 1 ≤ valuation F n
      · have h2 : valuation F n < valuation F t := not_le.1 (fun hh => hc ⟨h1, hh⟩)
        exact ⟨not_le.1 (fun hh => hnot ⟨hh, le_trans h2.le hh⟩), h2⟩
      · have h1' : valuation F n < 1 := not_le.1 h1
        have h3 : 1 < valuation F t := not_le.1 (fun hh => hnot ⟨hh, h1'.le⟩)
        exact ⟨h3, lt_trans h1' h3⟩
    have hv2 : valuation F (2 : F) ≤ 1 := by
      have : (2 : F) = 1 + 1 := by norm_num
      rw [this]
      exact le_trans (Valuation.map_add _ _ _) (by simp)
    have hn1 : valuation F (n + 1) < valuation F t :=
      lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ht1.2 (by simpa using ht1.1))
    have hn' : valuation F (t + (n + 1)) = valuation F t := Valuation.map_add_eq_of_lt_left _ hn1
    have ht' : valuation F (t + 2) ≤ valuation F t :=
      le_trans (Valuation.map_add _ _ _) (max_le le_rfl (le_trans hv2 ht1.1.le))
    have hq : (d + 1) * (d + 1) - algebraMap F E (t + 2) * (d + 1) + algebraMap F E (t + (n + 1)) = 0 := by
      simp only [map_add, map_one, map_ofNat]
      linear_combination h
    obtain ⟨w, hw, hdw⟩ := inv_mem_O_of_quad L (d + 1) (t + 2) (t + (n + 1)) hq
      (by rw [hn']; exact ht1.1.le) (by rw [hn']; exact ht')
    exact ⟨1, L.O.one_mem, w, hw, hdw⟩

end Quad

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V]
  [Module E V] (H : HermSp M V)

theorem h_add_right' (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

theorem h_smul_right' (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_zero_right' (x : V) : H.h x 0 = 0 := by
  rw [H.h_herm 0 x, H.h_zero_left, map_zero]

end Herm

theorem mkW_mem_of_mem_img : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V]
    [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)) (n : V ≃ₗ[E] V), n ∈ Fr.N →
    ∀ v : ↥(H.perp (H.X Fr.f)), (v : V) ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L) → H.mkW Fr.f v ∈ L := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr L n hn v hv
  obtain ⟨u, hu, hnu⟩ := Submodule.mem_map.1 hv
  have hnu' : n u = v := hnu
  have hnS := Formalism.MainNotions.BridgeLemma.NSet_inv Fr (Formalism.MainNotions.BridgeLemma.mem_NSet_of_mem_N Fr hn)
  have h1 : n.symm (v : V) - v ∈ H.X Fr.f := hnS.2.2 v v.2
  rw [← hnu', LinearEquiv.symm_apply_apply, hnu'] at h1
  have hprF_add : ∀ a b : V, Fr.prF (a + b) = Fr.prF a + Fr.prF b := by
    intro a b
    unfold FrameD.prF
    simp only [H.h_add_left, add_smul, Finset.sum_add_distrib]
    abel
  have hprF_smul : ∀ (c : E) (a : V), Fr.prF (c • a) = c • Fr.prF a := by
    intro c a
    unfold FrameD.prF
    simp only [H.h_smul_left, smul_sub, Finset.smul_sum, mul_smul]
  have hes_e : ∀ c b : Fin r, H.h (Fr.es c) (Fr.e b) = if b = c then 1 else 0 := by
    intro c b
    rw [H.h_herm (Fr.e b) (Fr.es c)]
    show M.L.cj (H.h (Fr.f b.castSucc) (Fr.es c)) = _
    rw [Fr.h_es]
    split_ifs <;> simp
  have hprF_perp : ∀ a : V, Fr.prF a ∈ H.perp (H.X Fr.f) := by
    intro a y hy
    unfold HermSp.X at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      show H.h (Fr.prF a) (Fr.e b) = 0
      unfold FrameD.prF
      rw [Formalism.MainNotions.BridgeLemma.h_sub_left, Formalism.MainNotions.BridgeLemma.h_sub_left, Formalism.MainNotions.BridgeLemma.h_sum_left,
        Formalism.MainNotions.BridgeLemma.h_sum_left]
      have z1 : ∑ i, H.h a (Fr.es i) * H.h (Fr.e i) (Fr.e b) = 0 :=
        Finset.sum_eq_zero (fun i _ => by
          rw [show H.h (Fr.e i) (Fr.e b) = 0 from Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last i).ne), mul_zero])
      have z2 : ∑ i, H.h a (Fr.e i) * H.h (Fr.es i) (Fr.e b) = H.h a (Fr.e b) := by
        simp only [hes_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [Finset.sum_ite_eq]; simp
      rw [z1, z2]; ring
    | zero => exact h_zero_right' H _
    | add y y' _ _ ih ih' => rw [h_add_right', ih, ih', add_zero]
    | smul t y _ ih => rw [h_smul_right', ih, mul_zero]
  have hcls : ∀ a ∈ Fr.LamStd L, ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF a ∧ H.mkW Fr.f w ∈ L := by
    intro a ha
    unfold FrameD.LamStd at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact ha.2.2
    | zero =>
      refine ⟨0, ?_, by rw [map_zero]; exact L.zero_mem⟩
      unfold FrameD.prF; simp [H.h_zero_left]
    | add a b _ _ iha ihb =>
      obtain ⟨w, hw, hwL⟩ := iha
      obtain ⟨w', hw', hwL'⟩ := ihb
      exact ⟨w + w', by rw [Submodule.coe_add, hw, hw', hprF_add], by rw [map_add]; exact L.add_mem hwL hwL'⟩
    | smul c a _ iha =>
      obtain ⟨w, hw, hwL⟩ := iha
      refine ⟨(c : E) • w, ?_, ?_⟩
      · rw [Submodule.coe_smul, hw]
        exact (hprF_smul (c : E) a).symm
      · rw [map_smul]
        exact L.smul_mem c hwL
  obtain ⟨w, hw, hwL⟩ := hcls u hu
  have hup : u ∈ H.perp (H.X Fr.f) := by
    have e : u = (u - v) + v := by abel
    rw [e]
    exact Submodule.add_mem _ (Formalism.MainNotions.BridgeLemma.X_le_perp Fr h1) v.2
  have h2 : u - Fr.prF u ∈ H.X Fr.f := by
    have e : u - Fr.prF u = ∑ a, H.h u (Fr.es a) • Fr.e a := by
      unfold FrameD.prF
      have : ∑ a, H.h u (Fr.e a) • Fr.es a = 0 :=
        Finset.sum_eq_zero (fun a _ => by
          rw [show H.h u (Fr.e a) = 0 from hup _ (Submodule.subset_span ⟨a, rfl⟩), zero_smul])
      rw [this]; abel
    rw [e]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  have hvw : H.mkW Fr.f v = H.mkW Fr.f w := by
    unfold HermSp.mkW
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show (v : V) - w ∈ H.X Fr.f
    have e : (v : V) - w = -(u - v) + (u - Fr.prF u) := by rw [hw]; abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.neg_mem _ h1) h2
  rw [hvw]
  exact hwL

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V]
  [Module E V] {H : HermSp M V} {r : ℕ}

theorem coef_mem_O (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L)
    (n : V ≃ₗ[E] V) (hn : n ∈ Fr.N) (d : E) (x : V) (hx : x ∈ H.X Fr.f)
    (h : d • Fr.z + x ∈ img n (Fr.LamStd L)) : d ∈ M.L.O := by
  obtain ⟨xz, hxz, hxzL, hprim⟩ := hL.2.2
  have hvp : d • Fr.z + x ∈ H.perp (H.X Fr.f) :=
    Submodule.add_mem _ (Submodule.smul_mem _ d (Formalism.MainNotions.BridgeLemma.z_mem_perp Fr))
      (Formalism.MainNotions.BridgeLemma.X_le_perp Fr hx)
  have hB := mkW_mem_of_mem_img Fr L n hn ⟨_, hvp⟩ h
  have e : H.mkW Fr.f ⟨_, hvp⟩ = d • H.mkW Fr.f xz := by
    rw [← map_smul]
    unfold HermSp.mkW
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show ((d • Fr.z + x) - d • (xz : V)) ∈ H.X Fr.f
    rw [hxz, add_sub_cancel_left]
    exact hx
  by_contra hd
  obtain ⟨s, hs, w, hw, hsw⟩ := exists_shift_inv M.L d hd
  have hyL : H.mkW Fr.f ((d + s) • xz) ∈ L := by
    rw [map_smul, add_smul, ← e]
    exact L.add_mem hB (L.smul_mem (⟨s, hs⟩ : M.L.O) hxzL)
  have hmk : H.mkW Fr.f xz = ((⟨w, hw⟩ : M.L.O) : E) • H.mkW Fr.f ((d + s) • xz) := by
    rw [map_smul, smul_smul, mul_comm, hsw, one_smul]
  obtain ⟨b, hb⟩ := (hprim ⟨w, hw⟩ ((d + s) • xz) hyL hmk).exists_right_inv
  have hb' : w * (b : E) = 1 := by simpa using congrArg Subtype.val hb
  have hds : d + s = (b : E) := by
    calc d + s = (d + s) * (w * (b : E)) := by rw [hb', mul_one]
      _ = ((d + s) * w) * (b : E) := by ring
      _ = (b : E) := by rw [hsw, one_mul]
  apply hd
  have : d = (b : E) - s := by rw [← hds]; ring
  rw [this]
  exact M.L.O.sub_mem b.2 hs

end Local

theorem coef_integral : ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∀ c : D.host.E, c • G.fl.z ∈ Lsub Λ G → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  intro D T G Z A hA Λ _ hloc c hc
  obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 (Submodule.mem_inf.1 hc).1
  have hlΛ : l ∈ Λ := (Submodule.mem_inf.1 hl).1
  have hxX : x ∈ Xsp G := hx
  have key : ∀ p, (D.s.atP p).ιE c ∈ (D.s.atP p).O := by
    intro p
    obtain ⟨n, hn, L, hL, hlat⟩ := hloc p
    have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
    have hf : (A p).f = GlobalTheory.LocOver.scaled Z p (frame G) := hA p
    have hz : (A p).z = baseChange₂ D p G.fl.z := by
      show (A p).f (Fin.last D.R.rS) = _
      rw [hA p]
      simp [frFac, frame, FlagG.fvec]
    have hxp : baseChange₂ D p x ∈ (locH Z p).X (A p).f := by
      rw [hf]; exact GlobalTheory.LocExt.bcP_Xsp_mem Z p G hxX
    have hmem : (D.s.atP p).ιE c • (A p).z + -(baseChange₂ D p x) ∈ img n ((A p).LamStd L) := by
      rw [← hlat, hz, ← baseChange_smul₂, ← hlx, map_add]
      have : baseChange₂ D p l + baseChange₂ D p x + -(baseChange₂ D p x) = baseChange₂ D p l := by abel
      rw [this]
      exact Submodule.subset_span ⟨l, hlΛ, rfl⟩
    rw [← hO]
    exact coef_mem_O (A p) L hL n hn _ _ (Submodule.neg_mem _ hxp) hmem
  exact ⟨⟨c, Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc c key⟩, rfl⟩

end GlobalTheory.FramePrim
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropicFrameVector_primitive_in_innerLattice : ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∀ c : D.host.E, c • G.fl.z ∈ Lsub Λ G → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  atlas_forward_decl GlobalTheory.FramePrim.coef_integral
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MkFlag

variable {Ef : Type} [Field Ef] [NumberField Ef] [StarRing Ef] {H : HSpace Ef} {r : ℕ} {T : Ef}

theorem Xa_le_X (F : FlagG H r T) (a : ℕ) : F.Xa a ≤ F.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem orth_of_mem_X (F : FlagG H r T) {w : H.V} (hw : ∀ a, H.hT (F.e a) w = 0)
    {u : H.V} (hu : u ∈ F.X) : H.hT u w = 0 := by
  unfold FlagG.X at hu
  induction hu using Submodule.span_induction with
  | mem v hv => obtain ⟨a, rfl⟩ := hv; exact hw a
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem iso_X (F : FlagG H r T) {x y : H.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : H.hT x y = 0 := by
  refine orth_of_mem_X F (fun a => ?_) hx
  have hle : F.X ≤ LinearMap.ker (H.hT (F.e a)) := by
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact F.e_iso a b
  exact hle hy

theorem span_eq (F : FlagG H r T) (e' : Fin r → H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val) :
    Submodule.span Ef (Set.range e') = F.X := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hsplit : e' a = (e' a - F.e a) + F.e a := by abel
    rw [hsplit]
    exact Submodule.add_mem _ (Xa_le_X F a.val (h a)) (Submodule.subset_span ⟨a, rfl⟩)
  · have key : ∀ n : ℕ, ∀ a : Fin r, a.val < n → F.e a ∈ Submodule.span Ef (Set.range e') := by
      intro n
      induction n with
      | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
      | succ n ih =>
        intro a ha
        have hXa : F.Xa a.val ≤ Submodule.span Ef (Set.range e') := by
          rw [FlagG.Xa, Submodule.span_le]
          rintro _ ⟨b, hb, rfl⟩
          have hb' : b.val < a.val := hb
          exact ih b (by omega)
        have hsplit : F.e a = e' a - (e' a - F.e a) := by abel
        rw [hsplit]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, rfl⟩) (hXa (h a))
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact key (a.val + 1) a (Nat.lt_succ_self _)

theorem indep (F : FlagG H r T) (e' : Fin r → H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val) :
    LinearIndependent Ef e' := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_eq F e' h, FlagG.X,
    finrank_span_eq_card F.e_indep]

theorem herm_zero {u v : H.V} (h : H.hT u v = 0) : H.hT v u = 0 := by
  have h2 := H.herm.eq u v
  rw [← h2, h, map_zero]

def change (F : FlagG H r T) (e' : Fin r → H.V) (x : H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val)
    (hx : x ∈ F.X) : FlagG H r T where
  e := e'
  z := F.z + x
  e_indep := indep F e' h
  e_iso a b := by
    have hX : ∀ c, e' c ∈ F.X := fun c => span_eq F e' h ▸ Submodule.subset_span ⟨c, rfl⟩
    exact iso_X F (hX a) (hX b)
  z_orth a := by
    have hX : e' a ∈ F.X := span_eq F e' h ▸ Submodule.subset_span ⟨a, rfl⟩
    have h1 : H.hT (e' a) F.z = 0 := orth_of_mem_X F F.z_orth hX
    rw [map_add, h1, iso_X F hX hx, add_zero]
  z_norm := by
    have h1 : H.hT x F.z = 0 := orth_of_mem_X F F.z_orth hx
    have h2 : H.hT F.z x = 0 := herm_zero h1
    simp only [map_add, LinearMap.add_apply, h1, h2, iso_X F hx hx, F.z_norm]
    ring

theorem change_X (F : FlagG H r T) (e' : Fin r → H.V) (x : H.V) (h : ∀ a, e' a - F.e a ∈ F.Xa a.val)
    (hx : x ∈ F.X) : (change F e' x h hx).X = F.X :=
  span_eq F e' h

theorem mkflag : ∀ (D : D7) (T : D.host.E) (G : FlagG (VS D) D.R.rS T) (e' : Fin D.R.rS → (VS D).V) (x : (VS D).V), (∀ a, e' a - G.e a ∈ G.Xa a.val) → x ∈ G.X → ∃ G' : FlagG (VS D) D.R.rS T, G'.e = e' ∧ G'.z = G.z + x ∧ G'.X = G.X := by
  intro D T G e' x h hx
  exact ⟨change G e' x h hx, rfl, rfl, change_X G e' x h hx⟩

end GlobalTheory.MkFlag
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_of_unitriangular_isotropic_shift : ∀ (D : D7) (T : D.host.E) (G : FlagG (VS D) D.R.rS T) (e' : Fin D.R.rS → (VS D).V) (x : (VS D).V), (∀ a, e' a - G.e a ∈ G.Xa a.val) → x ∈ G.X → ∃ G' : FlagG (VS D) D.R.rS T, G'.e = e' ∧ G'.z = G.z + x ∧ G'.X = G.X := by
  atlas_forward_decl GlobalTheory.MkFlag.mkflag
end

section
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatTransport

variable {D : D7}

theorem mem_gmap_inv (g : GV D) (Λ : LV D) (x : (VS D).V) : x ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ↔ g x ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g x, h, by simp⟩

variable {T : D.host.E} {F0 G' : FlagG (VS D) D.R.rS T} {g : GV D}

theorem e_eq (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (a : Fin D.R.rS) : g (F0.e a) = G'.e a := by
  have h := hfr a.castSucc
  simpa [FlagG.fvec, Fin.snoc_castSucc] using h

theorem z_eq (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) : g F0.z = G'.z := by
  have h := hfr (Fin.last _)
  simpa [FlagG.fvec, Fin.snoc_last] using h

theorem map_X (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) :
    F0.X.map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = G'.X := by
  unfold FlagG.X
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext a
  exact e_eq hfr a

theorem mem_X (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) : v ∈ F0.X ↔ g v ∈ G'.X := by
  rw [← map_X hfr]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := g.injective hwv
    exact this ▸ hw

theorem mem_orth (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) :
    v ∈ orth (VS D) F0.X ↔ g v ∈ orth (VS D) G'.X := by
  have hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h y hy
    have hy' : g.symm y ∈ F0.X := by
      rw [mem_X hfr]
      simpa using hy
    have := h _ hy'
    rw [← hiso] at this
    simpa using this
  · intro h x hx
    rw [← hiso]
    exact h _ ((mem_X hfr x).1 hx)

theorem mem_XS (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) : v ∈ XS D F0 ↔ g v ∈ XS D G' := by
  have hmap : (XS D F0).map ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) = XS D G' := by
    unfold XS
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨a, x, hx, rfl⟩, rfl⟩
      refine ⟨a, x, hx, ?_⟩
      simp [e_eq hfr a]
    · rintro ⟨a, x, hx, rfl⟩
      refine ⟨x • F0.e a, ⟨a, x, hx, rfl⟩, ?_⟩
      simp [e_eq hfr a]
  rw [← hmap]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := g.injective hwv
    exact this ▸ hw

theorem mem_dual (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (Λ : LV D) (x : (VS D).V) :
    x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ↔ g x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
  have hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]
  constructor
  · intro h y hy
    have hy' : g.symm y ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ := by
      rw [mem_gmap_inv]
      simpa using hy
    have := h _ hy'
    rw [← hiso] at this
    simpa using this
  · intro h y hy
    rw [← hiso]
    exact h _ ((mem_gmap_inv g Λ y).1 hy)

theorem isLattice_inv (g : GV D) {Λ : LV D} (hL : Submodule.IsLattice D.host.E Λ) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  refine ⟨hL.fg.map _, ?_⟩
  have e : ((Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ : LV D) : Set (VS D).V) =
      ((g⁻¹ : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λ : Set (VS D).V) := rfl
  rw [e, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact (g⁻¹ : GV D).surjective

theorem mem_Lsub (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (Λ : LV D)
    (v : (VS D).V) (hv : v ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0)) : g v ∈ Lsub Λ (lf D G') := by
  obtain ⟨hs, ho⟩ := hv
  refine ⟨?_, (mem_orth hg hfr v).1 ho⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hs
  obtain ⟨hyΛ, hyo⟩ := hy
  rw [map_add]
  refine Submodule.add_mem_sup ⟨(mem_gmap_inv g Λ y).1 hyΛ, (mem_orth hg hfr y).1 hyo⟩ ?_
  exact (mem_X hfr w).1 hw

end GlobalTheory.RowLatTransport

namespace GlobalTheory.RowLatTransport

theorem rowLat_transport : ∀ (D : D7) (T : D.host.E) (F0 G' : FlagG (VS D) D.R.rS T) (g : GV D), g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, g (F0.fvec a) = G'.fvec a) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → G'.z ∈ Λ → XLam Λ (lf D G') = XS D G' → (∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) → Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 ∧ Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ F0.z ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∧ XLam (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) = XS D F0 ∧ (∀ c : D.host.E, c • F0.z ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) := by
  intro D T F0 G' g hg hfr Λ hL hU hz hX hprim
  have hL' := isLattice_inv g hL
  have hU' : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
    unfold Formalism.HermitianLatticesTheory.IsUnimodular
    ext x
    rw [mem_dual hg, mem_gmap_inv]
    have hU0 : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
    rw [hU0]
  refine ⟨Formalism.MainNotions.BridgeRowsGenus.unimodular_mem_genus Formalism.L2.SG.Pf.Cnt.local_unimodular_holds D.sp.cm (VS D) _ hL' hU',
    hL', hU', ?_, ?_, ?_⟩
  · rw [mem_gmap_inv, z_eq hfr]
    exact hz
  · ext v
    change v ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ⊓ toO (VS D) F0.X ↔ v ∈ XS D F0
    rw [mem_XS hfr, ← hX]
    change _ ↔ g v ∈ Λ ⊓ toO (VS D) G'.X
    simp only [Submodule.mem_inf, toO, Submodule.restrictScalars_mem]
    rw [mem_gmap_inv, mem_X hfr]
  · intro c hc
    apply hprim c
    have := mem_Lsub hg hfr Λ _ hc
    rw [map_smul, z_eq hfr] at this
    exact this

end GlobalTheory.RowLatTransport
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLattice_properties_transport_by_isometry : ∀ (D : D7) (T : D.host.E) (F0 G' : FlagG (VS D) D.R.rS T) (g : GV D), g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, g (F0.fvec a) = G'.fvec a) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → G'.z ∈ Λ → XLam Λ (lf D G') = XS D G' → (∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) → Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 ∧ Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ F0.z ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∧ XLam (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) = XS D F0 ∧ (∀ c : D.host.E, c • F0.z ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) := by
  atlas_forward_decl GlobalTheory.RowLatTransport.rowLat_transport
end

section
noncomputable section

open scoped TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.FrameIntegral

theorem ef_one_of_split (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] (p : ℕ)
    (hall : ∀ W : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ W.asIdeal →
      W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1)
    (Q : Ideal (𝓞 E)) (hQp : Q.IsPrime) (hQb : Q ≠ ⊥) (hpQ' : ((p : ℕ) : 𝓞 E) ∈ Q) :
    Q.ramificationIdx ℤ = 1 ∧ Q.inertiaDeg ℤ = 1 := by
  have hinjEL : Function.Injective (algebraMap (𝓞 E) (𝓞 L)) :=
    FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L)
  obtain ⟨W, -, hWp, hWQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) Q ⊥
    (by rw [Ideal.comap_bot_of_injective _ hinjEL]; exact bot_le)
  have hWb : W ≠ ⊥ := by
    intro h0; apply hQb; rw [← hWQ, h0, Ideal.comap_bot_of_injective _ hinjEL]
  have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
    have : algebraMap (𝓞 E) (𝓞 L) ((p : ℕ) : 𝓞 E) ∈ W := by
      rw [← Ideal.mem_comap, hWQ]; exact hpQ'
    simpa using this
  obtain ⟨h1, h2⟩ := hall ⟨W, hWp, hWb⟩ hpW
  have : W.LiesOver Q := ⟨hWQ.symm⟩
  have h1' : W.ramificationIdx ℤ = 1 := h1
  have h2' : W.inertiaDeg ℤ = 1 := h2
  rw [Ideal.ramificationIdx_tower (R := ℤ) Q W] at h1'
  rw [Ideal.inertiaDeg_tower (R := ℤ) Q W] at h2'
  exact ⟨(mul_eq_one.mp h1').1, (mul_eq_one.mp h2').1⟩

theorem not_dvd_absNorm_different (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (hram : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1) :
    ¬ p ∣ Ideal.absNorm (differentIdeal ℤ (𝓞 K)) := by
  have key : ∀ I : Ideal (𝓞 K), I ∣ differentIdeal ℤ (𝓞 K) → ¬ p ∣ Ideal.absNorm I := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro h
      exact absurd (zero_dvd_iff.1 h) (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))
    | h₂ x hx =>
      intro _
      rw [Ideal.isUnit_iff.1 hx, Ideal.absNorm_top]
      exact hp.not_dvd_one
    | h₃ a P ha hP ih =>
      intro hdvd hpd
      rw [map_mul] at hpd
      rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
      · have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
        have hPb : P ≠ ⊥ := hP.ne_zero
        have hPm : P.IsMaximal := Ideal.IsPrime.isMaximal hPp hPb
        have hfin : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPb
        have hcard : Ideal.absNorm P = Nat.card (𝓞 K ⧸ P) := by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
        rw [hcard] at h
        have : Fact p.Prime := ⟨hp⟩
        obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p h
        let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
        have hx0 : x ≠ 0 := by
          rintro rfl; rw [addOrderOf_zero] at hx; exact hp.one_lt.ne hx
        have hpx : (p : 𝓞 K ⧸ P) * x = 0 := by
          rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
        have hp0 : (p : 𝓞 K ⧸ P) = 0 := (mul_eq_zero.1 hpx).resolve_right hx0
        have hpP : ((p : ℕ) : 𝓞 K) ∈ P := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hp0
        have he := hram P hPp hPb hpP
        have hun : Algebra.IsUnramifiedAt ℤ P := Ideal.ramificationIdx_eq_one_iff.mp he
        exact (not_dvd_differentIdeal_iff.2 hun) (dvd_of_mul_right_dvd hdvd)
      · exact ih (dvd_of_mul_left_dvd hdvd) h
  exact key _ dvd_rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem coprime_gi (i : Fin 2) : Nat.Coprime (Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F))) (D.host.g i) := by
  have hall : ∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal →
      W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1 := fun W hW =>
    (GlobalTheory.unramified_degree_one_of_ncard_placesOver D.host.E _ (D.host.g_prime i) (D.nd.g_split i) W hW).2
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (D.host.g_prime i)).2 ?_)
  refine not_dvd_absNorm_different D.host.F _ (D.host.g_prime i) fun P hPp hPb hpP => ?_
  exact (ef_one_of_split D.host.F D.host.E _ hall P hPp hPb hpP).1

end GlobalTheory.FrameIntegral
end
end

section
namespace GlobalTheory.LocalGenerators

theorem local_gen {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ ⊥) :
    ∃ d ∈ J, d ≠ (0 : R) ∧ ∃ s ∉ P.asIdeal, ∀ y ∈ J, ∃ o : R, s * y = o * d := by
  have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : ¬ J ≤ J * P.asIdeal := by
    intro h
    have heq : J * P.asIdeal = J * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h
    exact hP (mul_left_cancel₀ hJ heq)
  obtain ⟨d, hdJ, hdn⟩ := SetLike.not_le_iff_exists.mp hlt
  have hd0 : d ≠ 0 := by
    rintro rfl; exact hdn (Submodule.zero_mem _)
  have hdvd : J ∣ Ideal.span {d} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hdJ)
  obtain ⟨K, hK⟩ := hdvd
  have hKP : ¬ K ≤ P.asIdeal := by
    intro h
    apply hdn
    have : Ideal.span {d} ≤ J * P.asIdeal := hK ▸ Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self d)
  obtain ⟨s, hsK, hsP⟩ := SetLike.not_le_iff_exists.mp hKP
  refine ⟨d, hdJ, hd0, s, hsP, ?_⟩
  intro y hy
  have hm : s * y ∈ Ideal.span {d} := by
    rw [hK, mul_comm s y]; exact Ideal.mul_mem_mul hy hsK
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨o, ho.symm⟩

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (J : Ideal (NumberField.RingOfIntegers E)), J ≠ ⊥ →
    ∃ d ∈ J, d ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∃ s ∉ IsDedekindDomain.HeightOneSpectrum.asIdeal P, ∀ y ∈ J,
        ∃ (o : NumberField.RingOfIntegers E), s * y = o * d := by
  intro E _ _ P J hJ
  exact local_gen P J hJ

end GlobalTheory.LocalGenerators
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

noncomputable section

namespace GlobalTheory.FixConvRow

theorem loc_gen {E : Type} [Field E] [NumberField E] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    ∃ d ∈ J, d ≠ 0 ∧ ∃ s, s ∉ P.asIdeal ∧ ∀ y ∈ J, ∃ o : 𝓞 E, s * y = o * d := by
  first
  | exact @_root_.GlobalTheory.LocalGenerators.main
  | exact _root_.GlobalTheory.LocalGenerators.main
  | (apply _root_.GlobalTheory.LocalGenerators.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalGenerators.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalGenerators.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalGenerators.main ..)

end GlobalTheory.FixConvRow

namespace GlobalTheory.FixConvRow

open IsDedekindDomain

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem locS_le_of_le {V : Type} [AddCommGroup V] [Module (𝓞 E) V] (M : Submonoid (𝓞 E)) {A B : Submodule (𝓞 E) V}
    (h : A ≤ Formalism.HermitianLatticesTheory.locS M B) : Formalism.HermitianLatticesTheory.locS M A ≤ Formalism.HermitianLatticesTheory.locS M B := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, htx⟩ := h hx
  exact ⟨t * s, M.mul_mem ht hs, by rw [mul_smul]; exact htx⟩

theorem locS_span_eq {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (M : Submonoid (𝓞 E)) {r : ℕ} (e : Fin r → V) (I : Fin r → Set E) (c : Fin r → E)
    (h1 : ∀ a, ∃ s ∈ M, algebraMap (𝓞 E) E s * c a ∈ I a)
    (h2 : ∀ a, ∀ x ∈ I a, ∃ s ∈ M, ∃ o : 𝓞 E, algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E o * c a) :
    Formalism.HermitianLatticesTheory.locS M (Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ I a ∧ y = x • e a}) =
      Formalism.HermitianLatticesTheory.locS M (Submodule.span (𝓞 E) (Set.range fun a => c a • e a)) := by
  have key : ∀ (s : 𝓞 E) (x : E) (v : V), s • (x • v) = (algebraMap (𝓞 E) E s * x) • v := by
    intro s x v
    rw [← smul_assoc, Algebra.smul_def]
  apply le_antisymm
  · apply locS_le_of_le
    rw [Submodule.span_le]
    rintro _ ⟨a, x, hx, rfl⟩
    obtain ⟨s, hs, o, ho⟩ := h2 a x hx
    refine ⟨s, hs, ?_⟩
    rw [key, ho, ← key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · apply locS_le_of_le
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨s, hs, hsc⟩ := h1 a
    refine ⟨s, hs, ?_⟩
    rw [key]
    exact Submodule.subset_span ⟨a, _, hsc, rfl⟩

theorem inv_gen (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    ∃ c : E, c ≠ 0 ∧ (∃ s ∈ P.asIdeal.primeCompl,
      algebraMap (𝓞 E) E s * c ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹)) ∧
      ∀ x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹), ∃ s ∈ P.asIdeal.primeCompl, ∃ o : 𝓞 E,
        algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E o * c := by
  obtain ⟨d, hdJ, hd0, s, hsP, hs⟩ := loc_gen P J hJ
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hJ
  have hd0' : algebraMap (𝓞 E) E d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)]
  refine ⟨(algebraMap (𝓞 E) E d)⁻¹, inv_ne_zero hd0', ⟨s, hsP, ?_⟩, fun x hx => ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩⟩
  · rw [FractionalIdeal.mem_inv_iff hJ0]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    obtain ⟨o, ho⟩ := hs y' hy'
    rw [FractionalIdeal.mem_one_iff _]
    refine ⟨o, ?_⟩
    have e : algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E y' = algebraMap (𝓞 E) E o * algebraMap (𝓞 E) E d := by
      rw [← map_mul, ← map_mul, ho]
    field_simp
    exact e.symm
  · rw [FractionalIdeal.mem_inv_iff hJ0] at hx
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hdJ, rfl⟩))
    refine ⟨o, ?_⟩
    rw [ho, map_one, one_mul]
    field_simp

theorem inv_one (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (t : 𝓞 E) (htJ : t ∈ J)
    (htP : t ∉ P.asIdeal) :
    (∃ s ∈ P.asIdeal.primeCompl,
      algebraMap (𝓞 E) E s * 1 ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹)) ∧
      ∀ x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹), ∃ s ∈ P.asIdeal.primeCompl, ∃ o : 𝓞 E,
        algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E o * 1 := by
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hJ
  refine ⟨⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩, fun x hx => ⟨t, htP, ?_⟩⟩
  · rw [FractionalIdeal.mem_inv_iff hJ0]
    intro y hy
    obtain ⟨y', -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [FractionalIdeal.mem_one_iff _]
    exact ⟨y', by simp⟩
  · rw [FractionalIdeal.mem_inv_iff hJ0] at hx
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨t, htJ, rfl⟩))
    exact ⟨o, by rw [ho, mul_one, mul_comm]⟩

end Gen

end GlobalTheory.FixConvRow

namespace GlobalTheory.FixConvRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ddS_zpow_eq (D : D7) (a : Fin D.R.rS) :
    (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) =
      ((↑((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^
        (D.R.rS - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  rw [FractionalIdeal.coeIdeal_pow, ← Nat.cast_sub a.2.le, zpow_neg, zpow_natCast]
  rfl

theorem absNorm_different_not_mem (D : D7) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro hNP
  rw [gS, Nat.cast_mul] at hg
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    rcases P.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hc := Nat.isCoprime_iff_coprime.2 (GlobalTheory.FrameIntegral.coprime_gi (D := D) i)
  obtain ⟨u, v, huv⟩ := hc.map (Int.castRingHom (𝓞 D.host.E))
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  simp only [eq_intCast, Int.cast_natCast]
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hNP) (P.asIdeal.mul_mem_left _ hi)

theorem isFixedConv_of_XLam_eq : ∀ (D : D7) (T : D.host.E) (F : FlagG (VS D) D.R.rS T) (Λ : LV D),
    XLam Λ (lf D F) = XS D F → (∀ c : D.host.E, c • F.z ∈ Lsub Λ (lf D F) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) →
    IsFixedConv Λ (gS D) (lf D F) := by
  intro D T F Λ hX hprim
  refine ⟨fun P => ?_, hprim⟩
  have hJd0 : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 D.host.F))
  have hJm : ∀ m : ℕ, Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ^ m ≠ ⊥ :=
    fun m => pow_ne_zero m hJd0
  have goal : ∀ c : Fin D.R.rS → D.host.E,
      (∀ a : Fin D.R.rS, ∃ s ∈ P.asIdeal.primeCompl, algebraMap (𝓞 D.host.E) D.host.E s * c a ∈
        (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) →
      (∀ a : Fin D.R.rS, ∀ x ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
        ∃ s ∈ P.asIdeal.primeCompl, ∃ o : 𝓞 D.host.E,
          algebraMap (𝓞 D.host.E) D.host.E s * x = algebraMap (𝓞 D.host.E) D.host.E o * c a) →
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D F)) =
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • (lf D F).fl.e a))) := by
    intro c h1 h2
    rw [hX]
    exact locS_span_eq _ F.e
      (fun a => ((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Set D.host.E)) c h1 h2
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · have hN : ((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) : ℕ) : 𝓞 D.host.E) ∈
        Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) := by
      have h := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
        (Ideal.absNorm_mem (differentIdeal ℤ (𝓞 D.host.F)))
      simpa using h
    have hNP := absNorm_different_not_mem D P hg
    have hone := fun a : Fin D.R.rS => inv_one P _ (hJm (D.R.rS - (a : ℕ))) _ (Ideal.pow_mem_pow hN _)
      (fun h => hNP (P.isPrime.mem_of_pow_mem _ h))
    refine ⟨fun _ => 1, fun _ => one_ne_zero, fun _ _ => rfl, goal _ ?_ ?_⟩
    · intro a; rw [ddS_zpow_eq]; exact (hone a).1
    · intro a; rw [ddS_zpow_eq]; exact (hone a).2
  · choose c hc0 hc1 hc2 using fun a : Fin D.R.rS => inv_gen P _ (hJm (D.R.rS - (a : ℕ)))
    refine ⟨c, hc0, fun h => absurd h hg, goal c ?_ ?_⟩
    · intro a; rw [ddS_zpow_eq]; exact hc1 a
    · intro a; rw [ddS_zpow_eq]; exact hc2 a

end GlobalTheory.FixConvRow
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_conv_of_integral_flag_lattice : ∀ (D : D7) (T : D.host.E) (F : FlagG (VS D) D.R.rS T) (Λ : LV D), XLam Λ (lf D F) = XS D F → (∀ c : D.host.E, c • F.z ∈ Lsub Λ (lf D F) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) → IsFixedConv Λ (gS D) (lf D F) := by
  atlas_forward_decl GlobalTheory.FixConvRow.isFixedConv_of_XLam_eq
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatAdapt

theorem witt_flag (D : D7) (T : D.host.E) (hT : T ≠ 0) (F F' : FlagG (VS D) D.R.rS T) :
    ∃ g : GV D, g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ ∀ a, g (F.fvec a) = F'.fvec a := by
  have hind : ∀ G : FlagG (VS D) D.R.rS T, LinearIndependent D.host.E G.fvec := by
    intro G
    unfold FlagG.fvec
    rw [linearIndependent_fin_snoc]
    refine ⟨G.e_indep, fun hz => hT ?_⟩
    have h0 : ∀ x ∈ Submodule.span D.host.E (Set.range G.e), (VS D).hT x G.z = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact G.z_orth a
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
    have := h0 _ hz
    rw [G.z_norm] at this
    exact neg_eq_zero.1 this
  have hgram : ∀ G : FlagG (VS D) D.R.rS T, ∀ i j, (VS D).hT (G.fvec i) (G.fvec j) =
      if i = Fin.last _ ∧ j = Fin.last _ then -T else 0 := by
    intro G i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_norm]
      | cast b =>
        simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
        rw [← (VS D).herm.eq (G.e b) G.z, G.z_orth b, map_zero]
        simp [Fin.castSucc_ne_last]
    | cast a =>
      induction j using Fin.lastCases with
      | last => simp [FlagG.fvec, G.z_orth, Fin.castSucc_ne_last]
      | cast b => simp [FlagG.fvec, G.e_iso, Fin.castSucc_ne_last]
  obtain ⟨g, hg, hgi⟩ := GlobalTheory.St.WittT.witt_family F.fvec F'.fvec (hind F) (hind F')
    (fun i j => by rw [hgram F, hgram F'])
  exact ⟨g, hg, hgi⟩

theorem iso_X {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) :
    ∀ y ∈ G.X, ∀ x ∈ G.X, (VS D).hT y x = 0 := by
  intro y hy x hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    induction hy using Submodule.span_induction with
    | mem v hv => obtain ⟨a, rfl⟩ := hv; exact G.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem xa_last {D : D7} {T : D.host.E} (G : FlagG (VS D) D.R.rS T) : G.Xa D.R.rS = G.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  simp

theorem lsub_eq {D : D7} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (h : F.fl.X = F'.fl.X) (Λ : LV D) : Lsub Λ F = Lsub Λ F' := by
  simp only [Lsub, Lrep, Xsp, h]

theorem xlam_eq {D : D7} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (h : F.fl.X = F'.fl.X) (Λ : LV D) : XLam Λ F = XLam Λ F' := by
  simp only [XLam, Xsp, h]

theorem row_lattice_of_local_standard : ∀ (D : D7) (Tn : ℕ), Tn ≠ 0 → ∀ (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (G : LFlag (VS D) D.R.rS (Tn : D.host.E)) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ g, Adapt g (lf D F0) G ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  intro D Tn hTn F0 G Z A hA Λ hΛ hloc
  have hU := GlobalTheory.T.isUnimodular_of_local_standardLattice_translates
  have hX := GlobalTheory.T.isotropicPart_eq_span_scaledFrame_unitriangular
  have hZ := GlobalTheory.T.exists_add_isotropicSpan_mem_locallyStandardLattice
  have hP := GlobalTheory.T.anisotropicFrameVector_primitive_in_innerLattice
  have hM := GlobalTheory.T.exists_flag_of_unitriangular_isotropic_shift
  have hTr := GlobalTheory.T.rowLattice_properties_transport_by_isometry
  have hC := GlobalTheory.T.fixed_conv_of_integral_flag_lattice
  have hu := hU D Z A Λ hΛ hloc
  obtain ⟨e', he', hXe⟩ := hX D _ G Z A hA Λ hΛ hloc
  obtain ⟨x, hx, hzx⟩ := hZ D _ G Z A hA Λ hΛ hloc
  have hpr := hP D _ G Z A hA Λ hΛ hloc
  obtain ⟨G', hGe, hGz, hGX⟩ := hM D _ G.fl e' x he' hx
  have hT0 : ((Tn : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hTn
  obtain ⟨g, hg, hga⟩ := witt_flag D _ hT0 F0 G'
  have hX' : XLam Λ (lf D G') = XS D G' := by
    rw [xlam_eq (lf D G') G hGX, hXe, XS, hGe]
  have hpr' : ∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
    intro c hc
    rw [lsub_eq (lf D G') G hGX] at hc
    refine hpr c ?_
    have hcx : c • G.fl.z = c • G'.z - c • x := by rw [hGz, smul_add]; abel
    rw [hcx]
    refine Submodule.sub_mem _ hc ?_
    have hxX : c • x ∈ (Xsp G : Submodule D.host.E (VS D).V) := Submodule.smul_mem _ c hx
    refine ⟨Submodule.mem_sup_right hxX, ?_⟩
    show c • x ∈ orth (VS D) (Xsp G)
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro y hy
    exact iso_X G.fl y hy _ hxX
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hTr D _ F0 G' g hg hga Λ hΛ hu (hGz ▸ hzx) hX' hpr'
  refine ⟨g, ⟨hg, fun a => ?_⟩, h1, ⟨h2, h3, ⟨h4, rfl⟩, hC D _ F0 _ h5 h6⟩, h5⟩
  show g (F0.fvec a) - G.fl.fvec a ∈ G.fl.Xa a.val
  rw [hga a]
  induction a using Fin.lastCases with
  | last =>
    simp only [FlagG.fvec, Fin.snoc_last, Fin.val_last, hGz, xa_last]
    simpa using hx
  | cast b =>
    simp only [FlagG.fvec, Fin.snoc_castSucc, Fin.coe_castSucc, hGe]
    exact he' b

end GlobalTheory.RowLatAdapt
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLattice_of_locally_standard_frame : ∀ (D : D7) (Tn : ℕ), Tn ≠ 0 → ∀ (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (G : LFlag (VS D) D.R.rS (Tn : D.host.E)) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ g, Adapt g (lf D F0) G ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  atlas_forward_decl GlobalTheory.RowLatAdapt.row_lattice_of_local_standard
end
