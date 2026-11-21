import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramesTriangularChangeStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false

namespace GlobalTheory.FlagCell

theorem uniR_lowerTri {R : Type} [CommRing R] {m : ℕ} (n : Low m → R) :
    (uniR n).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := hij
  simp only [uniR_apply]
  rw [dif_neg (not_lt.mpr hij'.le), if_neg (ne_of_lt hij')]

theorem uniR_diag {R : Type} [CommRing R] {m : ℕ} (n : Low m → R) (i : Fin m) :
    uniR n i i = 1 := by
  simp [uniR_apply]

theorem uniR_det {R : Type} [CommRing R] {m : ℕ} (n : Low m → R) : (uniR n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (uniR_lowerTri n)]
  simp [uniR_diag]

theorem uniR_unique_of_mul_eq (R : Type) [CommRing R] (m : ℕ) (n n' : Low m → R)
    (M M' : Matrix (Fin m) (Fin m) R) (hM : M.BlockTriangular id) (hM' : M'.BlockTriangular id)
    (hdet : IsUnit M.det) (h : uniR n * M = uniR n' * M') : n = n' := by
  set L := uniR n
  set L' := uniR n'
  have hL' : IsUnit L'.det := by rw [uniR_det]; exact isUnit_one
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hdet
  letI : Invertible L' := Matrix.invertibleOfIsUnitDet L' hL'
  have hP : L'⁻¹ * L = M' * M⁻¹ := by
    calc L'⁻¹ * L = L'⁻¹ * (L * M) * M⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = L'⁻¹ * (L' * M') * M⁻¹ := by rw [h]
      _ = M' * M⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hL', Matrix.one_mul]
  have hlow : (L'⁻¹ * L).BlockTriangular OrderDual.toDual :=
    (Matrix.blockTriangular_inv_of_blockTriangular (uniR_lowerTri n')).mul (uniR_lowerTri n)
  have hup : (M' * M⁻¹).BlockTriangular id :=
    hM'.mul (Matrix.blockTriangular_inv_of_blockTriangular hM)
  set P := L'⁻¹ * L with hPdef
  have hdiag : P = Matrix.diagonal (fun j => P j j) := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hij)]
      exact hlow hij
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hij), hP]
      exact hup hij
  have hLP : L = L' * P := by
    rw [hPdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hL', Matrix.one_mul]
  have hP1 : ∀ j, P j j = 1 := by
    intro j
    have := congrFun (congrFun hLP j) j
    rw [hdiag, Matrix.mul_diagonal] at this
    simpa [L, L', uniR_diag] using this.symm
  have hLL : L = L' := by
    rw [hLP, hdiag]
    simp [hP1]
  funext s
  have := congrFun (congrFun hLL s.1.1) s.1.2
  simpa [L, L', uniR_apply, s.2] using this

end GlobalTheory.FlagCell
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_triangular_factor_unique : ∀ (R : Type) [CommRing R] (m : ℕ) (n n' : Low m → R) (M M' : Matrix (Fin m) (Fin m) R), M.BlockTriangular id → M'.BlockTriangular id → IsUnit M.det → uniR n * M = uniR n' * M' → n = n' := by
  first | exact @GlobalTheory.FlagCell.uniR_unique_of_mul_eq | exact GlobalTheory.FlagCell.uniR_unique_of_mul_eq | (intros; apply GlobalTheory.FlagCell.uniR_unique_of_mul_eq <;> assumption)
end

section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.FlagFibre (Low)

namespace GlobalTheory.FlagCell

theorem low_eq_of_spans_pullCol (X B : Scheme.{0}) (g : X ⟶ B) (E : B.Modules) (m : ℕ) (hE : IsVB E m)
    (U : B.Opens) (e : Fin m → Γ(E, U)) (he : IsFrame e)
    (fl : Vert.Flag ((Scheme.Modules.pullback g).obj E) m) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U)
    (n n' : Low m → Γ(X, V)) (h : Spans fl V (pullCol g e hV (uniR n)))
    (h' : Spans fl V (pullCol g e hV (uniR n'))) : n = n' := by
  classical
  haveI := hE.isQuasicoherent
  obtain ⟨M, hM, hdet, hMv⟩ := GlobalTheory.T.flag_frames_triangular_change X _ m fl V _ _ h h'
  have hinj := ((he.pullback g) V hV).1
  have e1 : (fun i => GlobalTheory.Twist.resM ((Scheme.Modules.pullback g).obj E) hV
      (QCoh.pullbackSections g E (le_refl (g ⁻¹ᵁ U)) (e i))) =
      fun i => QCoh.pullbackSections g E hV (e i) :=
    funext fun i => QCoh.res_pullbackSections _ _ _ _ _
  rw [e1] at hinj
  have key : uniR n * M = uniR n' * 1 := by
    rw [Matrix.mul_one]
    refine Matrix.ext fun l j => ?_
    have := hinj (a₁ := fun l => (uniR n * M) l j) (a₂ := fun l => uniR n' l j) (by
      simp only [Fintype.linearCombination_apply]
      have h1 := hMv j
      simp only [pullCol] at h1
      rw [h1]
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm])
    exact congrFun this l
  exact GlobalTheory.T.unipotent_triangular_factor_unique _ m n n' M 1 hM Matrix.blockTriangular_one hdet key

end GlobalTheory.FlagCell
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_unipotent_frame_unique : ∀ (X B : Scheme.{0}) (g : X ⟶ B) (E : B.Modules) (m : ℕ), IsVB E m → ∀ (U : B.Opens) (e : Fin m → Γ(E, U)), IsFrame e → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback g).obj E) m) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (n n' : Low m → Γ(X, V)), Spans fl V (pullCol g e hV (uniR n)) → Spans fl V (pullCol g e hV (uniR n')) → n = n' := by
  first | exact @GlobalTheory.FlagCell.low_eq_of_spans_pullCol | exact GlobalTheory.FlagCell.low_eq_of_spans_pullCol | (intros; apply GlobalTheory.FlagCell.low_eq_of_spans_pullCol <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover exists_sec_of_cover)
open GlobalTheory.LB (exists_fun_of_cover)

theorem pullCol_res {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} {m : ℕ}
    (e : Fin m → Γ(E, U)) {V V' : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) (h : V' ≤ V)
    (M : Matrix (Fin m) (Fin m) Γ(Y, V)) (j : Fin m) :
    resM _ h (pullCol π e hV M j) = pullCol π e (h.trans hV) (M.map (resG Y h)) j := by
  simp only [pullCol, map_sum, resM_smul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact congrArg (resG Y h (M l j) • ·) (QCoh.res_pullbackSections π E hV h (e l))

theorem Spans.res {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {V V' : X.Opens}
    {v : Fin m → Γ(F, V)} (hs : Spans fl V v) (h : V' ≤ V) :
    Spans fl V' fun j => resM F h (v j) := fun l => by
  obtain ⟨s, hfr, hv⟩ := hs l
  exact ⟨fun j => resM _ h (s j), hfr.res h, fun j => by rw [app_resM, hv]⟩

def IsCellCoord {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} {r : ι → ℕ} {E : ι → B.Modules}
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) {U : B.Opens}
    (eU : ∀ a, Fin (r a) → Γ(E a, U)) (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (n : (Σ a, Low (r a)) → Γ(Y, V)) : Prop :=
  ∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n ⟨a, s⟩))

theorem IsCellCoord.res {B Y : Scheme.{0}} {π : Y ⟶ B} {ι : Type} {r : ι → ℕ} {E : ι → B.Modules}
    {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} {U : B.Opens}
    {eU : ∀ a, Fin (r a) → Γ(E a, U)} {V V' : Y.Opens} {hV : V ≤ π ⁻¹ᵁ U}
    {n : (Σ a, Low (r a)) → Γ(Y, V)} (hn : IsCellCoord π fl eU V hV n) (h : V' ≤ V) :
    IsCellCoord π fl eU V' (h.trans hV) fun s => resG Y h (n s) := fun a => by
  have e : (fun j => resM _ h (pullCol π (eU a) hV (uniR fun s => n ⟨a, s⟩) j)) =
      pullCol π (eU a) (h.trans hV) (uniR fun s => resG Y h (n ⟨a, s⟩)) :=
    funext fun j => by rw [pullCol_res, map_uniR]
  exact e ▸ (hn a).res h

theorem exists_cellLocus : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens) (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, W)), (∀ a, Spans (fl a) W (pullCol π (eU a) hW (uniR fun s => n ⟨a, s⟩))) ∧ ∀ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n' : (Σ a, Low (r a)) → Γ(Y, V)), (∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n' ⟨a, s⟩))) → ∃ hVW : V ≤ W, ∀ s, Y.presheaf.map (homOfLE hVW).op (n s) = n' s := by
  intro B Y π ι r E fl hE U eU heU
  have uniq : ∀ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n₁ n₂ : (Σ a, Low (r a)) → Γ(Y, V)),
      IsCellCoord π fl eU V hV n₁ → IsCellCoord π fl eU V hV n₂ → n₁ = n₂ := by
    intro V hV n₁ n₂ h₁ h₂
    funext ⟨a, s⟩
    exact congrFun (GlobalTheory.T.pullback_unipotent_frame_unique Y B π (E a) (r a) (hE a) U (eU a) (heU a) (fl a) V hV _ _
      (h₁ a) (h₂ a)) s
  let K := {V : Y.Opens // ∃ (hV : V ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, V)),
    IsCellCoord π fl eU V hV n}
  choose hK nK gK using fun k : K => k.2
  have hWk : ∀ k : K, k.1 ≤ ⨆ k : K, k.1 := fun k => le_iSup (fun k : K => k.1) k
  have hW : (⨆ k : K, k.1) ≤ π ⁻¹ᵁ U := iSup_le hK
  have compat : ∀ (k l : K) s, resG Y (inf_le_left : k.1 ⊓ l.1 ≤ k.1) (nK k s) =
      resG Y (inf_le_right : k.1 ⊓ l.1 ≤ l.1) (nK l s) := fun k l s =>
    congrFun (uniq _ (inf_le_left.trans (hK k)) _ _ ((gK k).res inf_le_left)
      ((gK l).res inf_le_right)) s
  choose N hN using fun s => exists_fun_of_cover (fun k : K => k.1) hWk le_rfl
    (fun k => nK k s) fun k l => compat k l s
  have resN : ∀ k : K, (fun s => resG Y (hWk k) (N s)) = nK k := fun k => funext fun s => hN s k
  have good : IsCellCoord π fl eU (⨆ k : K, k.1) hW N := by
    intro a l
    have hv : ∀ k : K, pullCol π (eU a) (hK k) (uniR fun s => nK k ⟨a, s⟩) =
        fun j => resM _ (hWk k) (pullCol π (eU a) hW (uniR fun s => N ⟨a, s⟩) j) := by
      intro k; funext j; rw [pullCol_res, map_uniR, ← resN k]
    choose sK hsK hιK using fun k : K => gK k a l
    have compS : ∀ (k k' : K) j, resM _ (inf_le_left : k.1 ⊓ k'.1 ≤ k.1) (sK k j) =
        resM _ (inf_le_right : k.1 ⊓ k'.1 ≤ k'.1) (sK k' j) := by
      intro k k' j
      apply QCoh.injective_app_of_mono ((fl a).ι l)
      rw [app_resM, app_resM, hιK, hιK]
      simp only [hv, resM_resM]
    choose t ht using fun j => exists_sec_of_cover (F := (fl a).F l) (fun k : K => k.1) hWk le_rfl
      (fun k => sK k j) fun k k' => compS k k' j
    refine ⟨t, ?_, fun j => ?_⟩
    · refine isFrame_of_forall_exists fun V' h y hy => ?_
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show y ∈ ⨆ k : K, k.1 from h hy)
      refine ⟨V' ⊓ k.1, inf_le_left, ⟨hy, hk⟩, ?_⟩
      have e : (fun j => resM _ ((inf_le_left : V' ⊓ k.1 ≤ V').trans h) (t j)) =
          fun j => resM _ (inf_le_right : V' ⊓ k.1 ≤ k.1) (sK k j) := by
        funext j; rw [← ht j k, resM_resM]
      rw [e]
      exact hsK k _ inf_le_right
    · refine sec_ext_of_cover (fun k : K => k.1) hWk le_rfl fun k => ?_
      rw [← app_resM, ht, hιK]
      simp only [hv]
  refine ⟨⨆ k : K, k.1, hW, N, good, fun V hV n' hn' => ⟨hWk ⟨V, hV, n', hn'⟩, fun s => ?_⟩⟩
  exact (hN s _).trans (congrFun (uniq V hV _ _ (gK ⟨V, hV, n', hn'⟩) hn') s)

end GlobalTheory.FlagCell
end
