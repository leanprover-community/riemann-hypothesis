import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Counterexamples.TransversalityLocal.FramePairFixatorUnitaryAndFixesFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace GlobalTheory.LocOver.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

theorem tri_refl {K W : Type} [Semiring K] [AddCommMonoid W] [Module K W] {n : ℕ} (f : Fin n → W) : Tri K f f := by
  refine ⟨1, ⟨fun a b h => Matrix.one_apply_ne (ne_of_gt h), fun a => Matrix.one_apply_eq a⟩, fun b => ?_⟩
  simp [Matrix.one_apply]


end Mat

section Loc

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.NonGenericLocalCheck

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem img_mul' (g h : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * h) Λ = img g (img h Λ) := by
  unfold img; rw [← Submodule.map_comp]; rfl

theorem img_one' (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x; simp [img]

theorem move_one (t : Term V M r) : move 1 t = t := by
  cases t; simp [move, img_one']

theorem move_mul (g h : V ≃ₗ[E] V) (t : Term V M r) : move (g * h) t = move g (move h t) := by
  simp [move, img_mul']

theorem over_of_isTermOver {H : HermSp M V} (P : FPair H r) (d : Datum P) (t : Term V M r)
    (h : IsTermOver P d t) : Over P d t := by
  refine ⟨1, fun _ _ => rfl, d, ⟨1, one_mem _, ?_, ?_, ?_⟩, by rwa [move_one]⟩
  · intro x y hy; rw [show y = x from Subtype.ext hy]
  · intro x y hy; rw [show y = x from Subtype.ext hy]
  · intro x' y' x y hy' hy; rw [show y = x from Subtype.ext hy, show y' = x' from Subtype.ext hy']

theorem over_move_iff {H : HermSp M V} (P : FPair H r) (d : Datum P) (t : Term V M r) (g : V ≃ₗ[E] V)
    (hg : IsUnitary H g) : Over P d (move g t) ↔ Over P d t := by
  constructor
  · rintro ⟨h, hh, d', hd, ht⟩
    exact ⟨h * g, fun x y => (hh _ _).trans (hg x y), d', hd, by rwa [move_mul]⟩
  · rintro ⟨h, hh, d', hd, ht⟩
    refine ⟨h * g⁻¹, fun x y => (hh _ _).trans ?_, d', hd, ?_⟩
    · rw [← hg]; simp
    · rwa [← move_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem norms_of_over {H : HermSp M V} {P : FPair H r} {d : Datum P} {t : Term V M r} (h : Over P d t) :
    t.T = P.A.T ∧ t.T' = P.B.T := by
  obtain ⟨g, -, d', -, h1, h2, -⟩ := h
  exact ⟨h1, h2⟩


theorem NU_eq_NSet {H : HermSp M V} (Fr : FrameD H r) : NU H Fr.f = Fr.NSet := by
  ext n
  refine and_congr_right fun _ => and_congr_left fun _ => ⟨fun h j _ v hv => ?_, fun h a => ?_⟩
  · induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, rfl⟩ := hv
      refine Submodule.span_mono ?_ (h a)
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨b, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq] at ha hb ⊢
      have : b.val < a.val := hb
      omega
    | zero => simp
    | add x y _ _ hx hy =>
      have := add_mem hx hy
      convert this using 1; rw [map_add]; abel
    | smul c x _ hx =>
      have := Submodule.smul_mem _ c hx
      convert this using 1; rw [map_smul, smul_sub]
  · have := h (a.val + 1) a.2 (Fr.e a) (Submodule.subset_span ⟨a, by simp, rfl⟩)
    rw [Nat.add_sub_cancel] at this
    exact this

theorem NU_zero (H : HermSp M V) (f : Fin 1 → V) : NU (r := 0) H f = {1} := by
  have hX : H.X (r := 0) f = ⊥ := by simp [HermSp.X]
  ext n
  constructor
  · rintro ⟨-, -, h⟩
    ext v
    have := h v (by intro x hx; rw [hX, Submodule.mem_bot] at hx; subst hx
                    rw [H.h_herm, H.h_zero_left, map_zero])
    rw [hX, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  · rintro rfl
    exact ⟨fun _ _ => rfl, fun a => a.elim0, fun v _ => by simp⟩



theorem cong_zero (H : HermSp M V) (Λ : Submodule M.L.O V) (f f' : Fin 1 → V) (x : V) :
    Cong (r := 0) H Λ f f' x ↔ x ∈ H.smulLat (algebraMap F E (theta M)) Λ := by
  have hX : ∀ f : Fin 1 → V, H.X (r := 0) f = ⊥ := fun f => by simp [HermSp.X]
  unfold Cong
  simp only [hX, Submodule.mem_bot]
  exact ⟨fun ⟨a, ha, b, _, c, _, hb, hc, hx⟩ => by simpa [hx, hb, hc] using ha,
    fun hx => ⟨x, hx, 0, zero_mem _, 0, zero_mem _, rfl, rfl, by simp⟩⟩

theorem inhabited (M : Model F E) (hM : M.OK) (m : ℕ) :
    (pair M m).RelG (theta M) ∧ Over (pair M m) (datum M m) (move (LinearEquiv.neg E) (term M m)) ∧
      (∀ d, ¬ IsTermOver (pair M m) d (move (LinearEquiv.neg E) (term M m))) ∧
      ∀ d, ¬ Over (pair M m) d { term M m with T := 0 } := by
  haveI := hM.char0
  haveI : Nontrivial E := by
    have := M.L.rank
    exact Module.nontrivial_of_finrank_pos (R := F) (by omega)
  refine ⟨relG M m, (over_move_iff _ _ _ _ fun x y => ?_).2 (over_of_isTermOver _ _ _ (isTermOver M m)), ?_, ?_⟩
  · simp [NonGenericLocalCheck.stdH]
  · rintro d ⟨-, -, ⟨n, hn, hf, -⟩, -⟩
    have hN : (pair M m).A.N = ⊥ := by
      unfold FrameD.N
      rw [← NU_eq_NSet, NU_zero]; simp
    rw [hN, Subgroup.mem_bot] at hn
    subst hn
    have h0 := congrFun (congrFun hf 0) 0
    simp [move, term, pair, GlobalTheory.NonGenericLocalCheck.frame, vec_zero] at h0
    have h2 : algebraMap F E 2 = 0 := by
      rw [map_ofNat]; linear_combination -h0
    exact ((two_ne_zero' F).isUnit.map (algebraMap F E)).ne_zero h2
  · intro d h
    have := (norms_of_over h).1
    simp [pair, GlobalTheory.NonGenericLocalCheck.frame] at this

end Loc

section Glob

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs

variable {D : D7}


theorem ext_one (p : PlF D) : Ext p (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) 1 := fun _ => rfl

theorem ext_unique (p : PlF D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
    (h : Ext p γ g) (h' : Ext p γ g') : g = g' := by
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on_range (span_baseChange_eq_top p) fun x => ?_
  exact (h x).trans (h' x).symm

variable {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}


theorem locF_eq (p : PlF D) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) :
    locF Y p F = scaled (zOf Y) p (frame F) := rfl



end Glob

end GlobalTheory.LocOver.Check
