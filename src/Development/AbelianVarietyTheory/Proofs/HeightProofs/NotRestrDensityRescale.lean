import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FrameNormRestrictedDensity
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjCmHostRootNeSelf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LowerBoundCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity

variable {D : D7} {T : Core D}

theorem conjEmb_invol {E : Type} [Field E] (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [conjEmb]

theorem wtA_conj_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  have h1 : ∀ t', conjEmb (DV.tauEmb D t) ≠ DV.tauEmb D t' := fun t' h =>
    GlobalTheory.LeafCompare.tauEmb_ne_conj Q hp t' t h.symm
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [h1]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h =>
      ht' (GlobalTheory.LeafCompare.tauEmb_inj (by
        rw [← conjEmb_invol (DV.tauEmb D t'), ← h, conjEmb_invol]))
    simp [h1, this]
  · simp

theorem wt_ext (Q : Par D) (hp : Q.PinHost) {j : ℕ} {w w' : WeightFamilies.Wt D j} (hA : wtA w = wtA w') (hn : w.n = w'.n) :
    w = w' := by
  have hP : w.aP = w'.aP := by
    funext t i
    have := congrFun hA (DV.tauEmb D t, i.1)
    rw [GlobalTheory.LeafCompare.wtA_tau Q hp, GlobalTheory.LeafCompare.wtA_tau Q hp] at this
    simpa [ext0, i.2] using this
  have hM : w.aM = w'.aM := by
    funext t i
    have := congrFun hA (conjEmb (DV.tauEmb D t), i.1)
    rw [wtA_conj_tau Q hp, wtA_conj_tau Q hp] at this
    simpa [ext0, i.2] using this
  cases w
  cases w'
  simp only at hP hM hn
  subst hP hM hn
  rfl

theorem wtA_wsmul_apply {j : ℕ} (k : ℕ) (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA (WeightAlgebra.wsmul k w) x = k * wtA w x := by
  have h0 : ∀ {p : ℕ} (f : Fin p → ℕ) (i : ℕ), ext0 (fun s => k * f s) i = k * ext0 f i := by
    intro p f i
    unfold ext0
    split_ifs <;> simp
  simp only [wtA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((WeightAlgebra.wsmul k w).aP t) x.2 = k * ext0 (w.aP t) x.2 := h0 _ _
  have h2 : ext0 ((WeightAlgebra.wsmul k w).aM t) x.2 = k * ext0 (w.aM t) x.2 := h0 _ _
  rw [h1, h2]
  split_ifs <;> simp [mul_add]

theorem eq_wsmul_iff (h : LawsCore T) {j : ℕ} (ka wL : WeightFamilies.Wt D j) (n : ℕ) :
    wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n ↔ ka = WeightAlgebra.wsmul n wL := by
  constructor
  · intro H
    refine wt_ext T.Q h.pins.1 (funext fun x => ?_) ?_
    · have : (wtA ka x : ℤ) = n • (wtA wL x : ℤ) := congrFun (congrArg Prod.fst H) x
      rw [nsmul_eq_mul] at this
      rw [wtA_wsmul_apply]
      exact_mod_cast this
    · have : (ka.n : ℤ) = n • (wL.n : ℤ) := congrArg Prod.snd H
      rw [nsmul_eq_mul] at this
      show ka.n = n * wL.n
      exact_mod_cast this
  · rintro rfl
    refine Prod.ext (funext fun x => ?_) ?_
    · simp only [wtZ, Prod.smul_fst, Pi.smul_apply, nsmul_eq_mul, wtA_wsmul_apply]
      push_cast
      rfl
    · simp only [wtZ, Prod.smul_snd, nsmul_eq_mul]
      show ((n * wL.n : ℕ) : ℤ) = _
      push_cast
      rfl

theorem prod_iff (h : LawsCore T) (j : ℕ) (ka wL : WeightFamilies.Wt D j) {N : ℕ} (w : Fin (N + 1) → T.R j) (n : ℕ)
    (hka : wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n) :
    ProdInLat h j ka w n ↔ ProdInLattice h j wL w n := by
  obtain rfl := (eq_wsmul_iff h ka wL n).1 hka
  exact Iff.rfl

theorem const_iff (large₂ : SizeData₂ D) {j : ℕ} (ka wL : WeightFamilies.Wt D j) (C A P : ℝ) (n : ℕ) :
    LamConst j large₂ C A ka P n wL.size ↔ ConstBound large₂ ka C A P n wL := Iff.rfl

def DensityWith (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j)
    (yP : GenericFrames T j) (ka : WeightFamilies.Wt D j) (R : Comp (T.Q.Xo j) T.Q.c → T.R j → T.R j → Prop) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (F : (recB h).Cusp j ka), F ∈ (recB h).Mlat j ka → evC hG Z (F : T.R j) ≠ 0 →
    ∃ F' ∈ (recB h).Mlat j ka, F' ≠ 0 ∧ R Z (F : T.R j) (F' : T.R j) ∧
      ∀ σ : T.Q.c.F →+* ℂ, (recB h).supN j ka σ F' ≤ genSup hG fn yP ka (F : T.R j) Z σ

section Density

variable (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j) (yP : GenericFrames T j)
  (ka : WeightFamilies.Wt D j)

theorem DensityWith.mono {R R' : Comp (T.Q.Xo j) T.Q.c → T.R j → T.R j → Prop}
    (hR : ∀ Z f f', R Z f f' → R' Z f f') (H : DensityWith h j hG fn yP ka R) : DensityWith h j hG fn yP ka R' := by
  intro Z F hF hZ
  obtain ⟨F', h1, h2, h3, h4⟩ := H Z F hF hZ
  exact ⟨F', h1, h2, hR _ _ _ h3, h4⟩




end Density

section Separate

variable {j : ℕ}

def rescale (fn : FrameNorms T j) (a : T.Q.c.F) : FrameNorms T j := fun σ y i =>
  match i with
  | none => fn σ y none / ‖σ a‖
  | some u => fn σ y (some u)







end Separate



end GlobalTheory.LowerBoundCompare
