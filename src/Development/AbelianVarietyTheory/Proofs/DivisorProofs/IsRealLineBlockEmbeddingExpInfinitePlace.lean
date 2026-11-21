import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGLiAddSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfIsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative

section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
open Formalism.UG (cT)
open scoped TensorProduct Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockForms.LeviLoc

section Lin

variable (R : Type) [CommRing R] {l d n : ℕ}

def blkId (hld : l + d ≤ n) : Matrix (Fin n) (Fin d) R :=
  fun i j => if i.val = l + j.val then 1 else 0

theorem blkId_map {S : Type} [CommRing S] (f : R →+* S) (hld : l + d ≤ n) : (blkId R hld).map f = blkId S hld := by
  ext i j
  simp [blkId, apply_ite f]

theorem tripPlace_val (hld : l + d ≤ n) (a : Fin 3) (i : Fin (tripSizes l d n a)) :
    (tripPlace hld ⟨a, i⟩).val = ![0, l, l + d] a + i.val := by
  simp only [tripPlace, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  congr 1
  fin_cases a <;> simp [tripSizes, Fin.sum_univ_succ]

theorem blkId_ne (hld : l + d ≤ n) (a : Fin 3) (ha : a ≠ 1) (i : Fin (tripSizes l d n a)) (j : Fin d) :
    blkId R hld (tripPlace hld ⟨a, i⟩) j = 0 := by
  have hi := i.2
  have hj := j.2
  rw [blkId, if_neg]
  rw [tripPlace_val]
  fin_cases a
  · simp [tripSizes] at hi ⊢; omega
  · exact absurd rfl ha
  · simp; omega

theorem blkId_one (hld : l + d ≤ n) (i : Fin d) (j : Fin d) :
    blkId R hld (tripPlace hld ⟨1, i⟩) j = if i = j then 1 else 0 := by
  have e : (tripPlace hld ⟨1, i⟩).val = l + i.val := tripPlace_val hld 1 i
  rw [blkId, e]
  simp [Fin.ext_iff]

theorem blkId_mid (hld : l + d ≤ n) (A : Matrix (Fin d) (Fin d) R) (i j : Fin d) (a b : Fin n)
    (ha : ∀ k, blkId R hld a k = if i = k then 1 else 0) (hb : ∀ k, blkId R hld b k = if j = k then 1 else 0) :
    (blkId R hld * A * (blkId R hld)ᵀ) a b = A i j := by
  simp [Matrix.mul_apply, ha, hb]

theorem leviEmb_midHom (hld : l + d ≤ n) (g : GL (Fin d) R) :
    (GlobalTheory.SmGL.leviEmb R (tripPlace hld) (midHom R l d n g)).1 = 1 + blkId R hld * (g.1 - 1) * (blkId R hld)ᵀ := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (tripPlace hld).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (tripPlace hld).surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases ha : a = 1
    · subst ha
      have e : midHom R l d n g 1 = g :=
        Pi.mulSingle_eq_same (M := fun j : Fin 3 => GL (Fin (tripSizes l d n j)) R) 1 g
      rw [e, Matrix.add_apply, blkId_mid R hld _ i j _ _ (blkId_one R hld i) (blkId_one R hld j)]
      have e2 : (1 : Matrix (Fin n) (Fin n) R) (tripPlace hld ⟨1, i⟩) (tripPlace hld ⟨1, j⟩) =
          (1 : Matrix (Fin (tripSizes l d n 1)) (Fin (tripSizes l d n 1)) R) i j := by
        simp [Matrix.one_apply]
      rw [e2]
      exact (add_sub_cancel _ _).symm
    · have e : midHom R l d n g a = 1 := Pi.mulSingle_eq_of_ne ha _
      rw [e]
      simp [Matrix.mul_apply, blkId_ne R hld a ha, Matrix.one_apply]
  · rw [leviEmb_apply_ne _ _ _ hab]
    have h1 : (1 : Matrix (Fin n) (Fin n) R) (tripPlace hld ⟨a, i⟩) (tripPlace hld ⟨b, j⟩) = 0 :=
      Matrix.one_apply_ne fun e => hab (congrArg Sigma.fst ((tripPlace hld).injective e))
    rw [Matrix.add_apply, h1, zero_add]
    by_cases ha : a = 1
    · have hb : b ≠ 1 := fun e => hab (ha.trans e.symm)
      simp [Matrix.mul_apply, blkId_ne R hld b hb]
    · simp [Matrix.mul_apply, blkId_ne R hld a ha]

variable {R}

theorem map_formula {T : Type} [CommRing T] (p : R →+* T) (s : R →+* R) (X Y : Matrix (Fin n) (Fin d) R)
    (X' Y' : Matrix (Fin d) (Fin n) R) (P Q : Matrix (Fin d) (Fin d) R) (hQ : Q.map (p.comp s) = 1) :
    (1 + X * (P - 1) * Y' + Y * (cT s Q - 1) * X').map p = 1 + X.map p * (P.map p - 1) * Y'.map p := by
  have h1 : (cT s Q).map p = 1 := by
    rw [← Matrix.transpose_one, ← hQ]; rfl
  rw [Matrix.map_add _ (map_add p), Matrix.map_add _ (map_add p), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub p), Matrix.map_sub _ (map_sub p), h1,
    Matrix.map_one _ (map_zero p) (map_one p), Matrix.map_one _ (map_zero p) (map_one p)]
  simp

theorem conj_leviEmb (hld : l + d ≤ n) (B : GL (Fin n) R) (g : GL (Fin d) R) {X : Matrix (Fin n) (Fin d) R}
    {Y' : Matrix (Fin d) (Fin n) R} (h1 : B.1 * blkId R hld = X) (h2 : Y' * B.1 = (blkId R hld)ᵀ) :
    1 + X * (g.1 - 1) * Y' = (B * GlobalTheory.SmGL.leviEmb R (tripPlace hld) (midHom R l d n g) * B⁻¹).1 := by
  have h3 : Y' = (blkId R hld)ᵀ * (B⁻¹).1 := by rw [← h2, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [Units.val_mul, Units.val_mul, leviEmb_midHom, h3, ← h1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Units.mul_inv]
  simp only [Matrix.mul_assoc]

end Lin

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
  {C : GL (Fin n) E} {l d : ℕ}

theorem yx_eq_one (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    cT (σ : E →+* E) Y * J * X = 1 := by
  ext i j
  have h := congrArg σ (congrFun₂ hW.xy j i)
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, RingHom.coe_coe,
    cm_conj_conj hσ, hJ.1, Matrix.one_apply, apply_ite σ, map_one, map_zero, Finset.sum_mul] at h ⊢
  rw [Finset.sum_comm, if_congr eq_comm rfl rfl, ← h]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

omit [NumberField F] [NumberField E] in
theorem mul_blkId (hC : IsAdapted σ J X Y C) (h : l + d ≤ r) (hld : l + d ≤ n) :
    C.1 * blkId E hld = blkCols h X := by
  ext k j
  have hj := j.2
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨l + j.val, by omega⟩ : Fin n)]
  · simp only [blkId, if_true, mul_one]
    exact hC.colX _ _ rfl k
  · intro b _ hb
    rw [blkId, if_neg fun e => hb (Fin.ext e), mul_zero]
  · simp

theorem dual_mul (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (hC : IsAdapted σ J X Y C)
    (h : l + d ≤ r) (hld : l + d ≤ n) :
    cT (σ : E →+* E) (blkCols h Y) * J * C.1 = (blkId E hld)ᵀ := by
  ext j i
  have hj := j.2
  have hi := i.2
  have hr := hC.le
  have e : (cT (σ : E →+* E) (blkCols h Y) * J * C.1) j i =
      ((cT (σ : E →+* E) Y * J) *ᵥ (fun k => C.1 k i)) ⟨l + j.val, by omega⟩ := rfl
  rw [e, Matrix.transpose_apply, blkId]
  by_cases h1 : i.val < r
  · have e1 : (fun k => C.1 k i) = fun k => X k ⟨i.val, h1⟩ := funext (hC.colX _ _ rfl)
    rw [e1]
    refine (congrFun₂ (yx_eq_one hσ hJ hW) ⟨l + j.val, by omega⟩ ⟨i.val, h1⟩).trans ?_
    simp [Matrix.one_apply, eq_comm]
  · rw [if_neg (by omega)]
    by_cases h2 : i.val + r < n
    · rw [hC.perpY i (by omega) h2]; rfl
    · have e1 : (fun k => C.1 k i) = fun k => Y k ⟨n - 1 - i.val, by omega⟩ :=
        funext (hC.columnBlock _ _ (by simp; omega))
      rw [e1]
      exact congrFun₂ hW.yy ⟨l + j.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩

end Frame

section Adele

theorem gl_entry {R : Type} [CommRing R] {d : ℕ} {x y : GL (Fin d) R} (h : x = y) (a b : Fin d) : x.1 a b = y.1 a b := by
  rw [h]

open GlobalTheory.LFun GlobalTheory.CuspRep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compFin_eq (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u z = Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E) (finTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

omit [NumberField E] in
theorem compFin_sigR (σ : E →ₐ[F] E) (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u (sigR _ σ z) = sigR _ σ (compFin F E u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

omit [NumberField E] in
theorem infTens_sigR (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    infTens F E (sigR _ σ z) = sigR _ σ (infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem toCompl_compFin {u : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = u)
    (z : AF F ⊗[F] E) : toCompl h (compFin F E u z) = pLoc E w (finAdEquiv F E (finTens F E z)) := by
  rw [compFin_eq, ← finAdEquiv_apply]; rfl

theorem compFin_eq_zero (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = u → pLoc E w (finAdEquiv F E (finTens F E z)) = 0) :
    compFin F E u z = 0 := by
  have h1 : ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E)) * finTens F E z = 0 := by
    refine (finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun w => ?_)
    rw [map_mul, map_zero]
    change pLoc E w (_ * _) = pLoc E w 0
    rw [map_mul, map_zero]
    by_cases hw : w.under (𝓞 F) = u
    · rw [hz w hw, mul_zero]
    · have e : pLoc E w (finAdEquiv F E ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) = 0 := by
        refine Eq.trans (b := toCompl (rfl : w.under (𝓞 F) = _) _)
          (finAdEquiv_apply rfl ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) ?_
        rw [Algebra.TensorProduct.map_tmul, evalV_singleFin_ne hw, TensorProduct.zero_tmul, map_zero]
      rw [e, zero_mul]
  have h2 := congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E)) h1
  rwa [map_mul, map_zero, Algebra.TensorProduct.map_tmul, evalV_singleFin_self, map_one,
    ← Algebra.TensorProduct.one_def, one_mul, ← compFin_eq] at h2

omit [Algebra F E] [NumberField F] [Field F] in
theorem pFin_finGL {d : ℕ} (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) (a b : Fin d) : pFin E ((finGL E d k).1 a b) = k.1 a b :=
  gl_entry (map_cornerGL_of_hom (sFin E) (pFin E) (RingHom.id _) (fun _ => rfl) k) a b

omit [Algebra F E] [NumberField F] [Field F] in
theorem fst_finGL {d : ℕ} (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) (a b : Fin d) :
    RingHom.fst (InfiniteAdeleRing E) (GlobalTheory.CuspRep.Af E) ((finGL E d k).1 a b) =
      (1 : Matrix (Fin d) (Fin d) (InfiniteAdeleRing E)) a b :=
  gl_entry ((map_cornerGL_of_zero (S := Ad E) (sFin E)
    (RingHom.fst (InfiniteAdeleRing E) (GlobalTheory.CuspRep.Af E)) (fun _ => rfl) k)) a b

variable {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
  (hΦ : ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z))) {d : ℕ}
include hΦ

theorem fin_symm (a : Ad E) : finAdEquiv F E (finTens F E (Φ.symm a)) = pFin E a :=
  (congrArg Prod.snd (hΦ (Φ.symm a))).symm.trans (congrArg (pFin E) (Φ.apply_symm_apply a))

theorem map_infTens (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) : ((finGL E d k).1.map Φ.symm).map (infTens F E) = 1 := by
  refine Matrix.ext fun a b => ?_
  refine j.injective (((congrArg Prod.fst (hΦ (Φ.symm _))).symm.trans
    (congrArg Prod.fst (Φ.apply_symm_apply _))).trans ((fst_finGL k a b).trans ?_))
  simp [Matrix.one_apply, apply_ite j]

theorem map_compFin_ne {u : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hu : w.under (𝓞 F) ≠ u)
    (k : GL (Fin d) (w.adicCompletion E)) :
    ((finGL E d (locGL E d w k)).1.map Φ.symm).map (compFin F E u) = 1 := by
  refine Matrix.ext fun a b => ?_
  have h1 := compFin_eq_zero u (Φ.symm ((finGL E d (locGL E d w k)).1 a b) - (1 : Matrix (Fin d) (Fin d) _) a b)
    fun w' hw' => by
      have hne : w' ≠ w := fun e => hu (e ▸ hw')
      have h2 : pLoc E w' ((locGL E d w k).1 a b) = (1 : Matrix (Fin d) (Fin d) _) a b :=
        gl_entry (pLoc_locGL_of_ne hne k) a b
      rw [map_sub, map_sub, map_sub, fin_symm hΦ, pFin_finGL, h2, sub_eq_zero]
      by_cases e : a = b
      · subst e; simp only [Matrix.one_apply_eq, map_one]
      · simp only [Matrix.one_apply_ne e, map_zero]
  rw [map_sub, sub_eq_zero] at h1
  refine h1.trans ?_
  by_cases e : a = b
  · subst e; simp only [Matrix.one_apply_eq, map_one]
  · simp only [Matrix.one_apply_ne e, map_zero]

theorem complMap_splitProj {v : HeightOneSpectrum (𝓞 F)} (t : E →ₐ[F] Fv F v) (k : GL (Fin d) (GlobalTheory.CuspRep.Af E))
    (a b : Fin d) : complMap (splitPrime_under t) (splitProj t (compFin F E v (Φ.symm ((finGL E d k).1 a b)))) =
      pLoc E (splitPrime t) (k.1 a b) := by
  rw [← toCompl_eq_complMap, toCompl_compFin, fin_symm hΦ, pFin_finGL]

theorem map_split_self {v : HeightOneSpectrum (𝓞 F)} (t : E →ₐ[F] Fv F v) (g : GL (Fin d) (Fv F v)) :
    ((finGL E d (locGL E d (splitPrime t) (glEquiv d (complEquiv t (splitPrime_under t)) g))).1.map Φ.symm).map
      ((splitProj t : Fv F v ⊗[F] E →+* Fv F v).comp (compFin F E v)) = g.1 := by
  refine Matrix.ext fun a b => ?_
  refine (complMap_bijective t (splitPrime_under t)).1 ((complMap_splitProj hΦ t _ a b).trans ?_)
  exact gl_entry (pLoc_locGL (splitPrime t) _) a b

theorem map_split_ne {v : HeightOneSpectrum (𝓞 F)} (t : E →ₐ[F] Fv F v) {w : HeightOneSpectrum (𝓞 E)}
    (hw : splitPrime t ≠ w) (k : GL (Fin d) (w.adicCompletion E)) :
    ((finGL E d (locGL E d w k)).1.map Φ.symm).map
      ((splitProj t : Fv F v ⊗[F] E →+* Fv F v).comp (compFin F E v)) = 1 := by
  refine Matrix.ext fun a b => ?_
  refine (complMap_bijective t (splitPrime_under t)).1 ((complMap_splitProj hΦ t _ a b).trans ?_)
  refine (gl_entry (pLoc_locGL_of_ne hw k) a b).trans ?_
  by_cases e : a = b
  · subst e; simp only [Units.val_one, Matrix.one_apply_eq, map_one]
  · simp only [Units.val_one, Matrix.one_apply_ne e, map_zero]

end Adele

open GlobalTheory.LFun GlobalTheory.CuspRep in

theorem blockEmb_locGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (C : GL (Fin n) E), GlobalTheory.BlockForms.IsAdapted σ J Xf Yf C →
    ∀ (l d : ℕ) (h : l + d ≤ r) (hld : l + d ≤ n) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ g : GL (Fin d) (Fv F v), ∃ x : GLoc σ J v,
        IsCompAt σ J t (Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) C)
          (GlobalTheory.SmGL.leviEmb (Fv F v) (tripPlace hld) (midHom (Fv F v) l d n g)) x ∧
        emb σ J v x = ι (GlobalTheory.CuspRep.finGL E d (GlobalTheory.CuspRep.locGL E d (splitPrime t)
          (glEquiv d (complEquiv t (splitPrime_under t)) g))) := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW v t C hC l d h hld ι hι g
  obtain ⟨Φ, j, -, -, -, hΦ, hM⟩ := hι
  set H := glEquiv d (complEquiv t (splitPrime_under t)) g with hH
  have hM' := hM (finGL E d (locGL E d (splitPrime t) H))
  rw [← map_inv, ← map_inv] at hM'
  refine ⟨proj σ J v (ι (finGL E d (locGL E d (splitPrime t) H))), ?_, ?_⟩
  · let p : AF F ⊗[F] E →+* Fv F v := (splitProj t : Fv F v ⊗[F] E →+* Fv F v).comp (compFin F E v)
    have hp : ∀ {a b : Type} (Z : Matrix a b E), (adMat F Z).map p = Z.map (t : E →+* Fv F v) := fun Z =>
      Matrix.ext fun a b => by
        change splitProj t (Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (Z a b))) = t (Z a b)
        simp
    have hs : p.comp (sigR (AF F) σ) = (splitProj (t.comp σ) : Fv F v ⊗[F] E →+* Fv F v).comp (compFin F E v) :=
      RingHom.ext fun z => by
        change splitProj t (compFin F E v (sigR _ σ z)) = splitProj (t.comp σ) (compFin F E v z)
        rw [compFin_sigR, splitProj_comp]
    change (matHom _ σ J (ι (finGL E d (locGL E d (splitPrime t) H)))).1.map p = _
    rw [hM', map_formula p _ _ _ _ _ _ _ (by rw [hs]; exact map_split_ne hΦ _ (splitPrime_comp_ne hσ t) _),
      map_split_self hΦ t g, hp, hp]
    set B := Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) C with hB
    have hBv : B.1 = C.1.map (t : E →+* Fv F v) := rfl
    have h1 : B.1 * blkId _ hld = (blkCols h X).map (t : E →+* Fv F v) := by
      rw [hBv, ← mul_blkId hC h hld, ← blkId_map E (t : E →+* Fv F v) hld]
      exact Matrix.map_mul.symm
    have h2 : (cT (σ : E →+* E) (blkCols h Y) * J).map (t : E →+* Fv F v) * B.1 = (blkId _ hld)ᵀ := by
      rw [hBv, ← Matrix.map_mul, dual_mul hσ hJ hW hC h hld, ← blkId_map E (t : E →+* Fv F v) hld]
      rfl
    exact conj_leviEmb hld B g h1 h2
  · refine ext_inf_fin σ J ?_ (GFin_ext σ J fun u => ?_)
    · rw [projInf_emb]
      refine matHom_injective _ σ J (Units.ext ?_)
      change 1 = (matHom _ σ J (ι (finGL E d (locGL E d (splitPrime t) H)))).1.map (infTens F E)
      rw [hM', map_formula _ _ _ _ _ _ _ _ ?_, map_infTens hΦ]
      · simp
      · have e : (infTens F E).comp (sigR (AF F) σ) = (sigR _ σ).comp (infTens F E) := RingHom.ext (infTens_sigR σ)
        rw [e, RingHom.coe_comp, ← Matrix.map_map, map_infTens hΦ, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [projFinLoc_projFin, projFinLoc_projFin]
      by_cases hu : u = v
      · subst hu; rw [proj_emb_self]
      · have hu' : (splitPrime t).under (𝓞 F) ≠ u := fun e => hu (e.symm.trans (splitPrime_under t))
        rw [proj_emb_ne σ J hu]
        refine matHom_injective _ σ J (Units.ext ?_)
        change 1 = (matHom _ σ J (ι (finGL E d (locGL E d (splitPrime t) H)))).1.map (compFin F E u)
        rw [hM', map_formula _ _ _ _ _ _ _ _ ?_, map_compFin_ne hΦ hu']
        · simp
        · have e : (compFin F E u).comp (sigR (AF F) σ) = (sigR _ σ).comp (compFin F E u) :=
            RingHom.ext (compFin_sigR σ u)
          rw [e, RingHom.coe_comp, ← Matrix.map_map, map_compFin_ne hΦ hu', Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.BlockForms.LeviLoc

end
end

section
namespace GlobalTheory.SpectralLemmaSecond

open Matrix

theorem main : (let d1 : {m k : Type} → [Fintype m] → [Fintype k] → Matrix m k ℂ → ℝ := @(fun {m k : Type} [Fintype m] [Fintype k] (M : Matrix m k ℂ) ↦ ∑ i : m, ∑ j : k, ‖M i j‖); ∀ {m k p : Type} [inst : Fintype m] [inst_1 : Fintype k] [inst_2 : Fintype p] (M : Matrix m k ℂ) (N : Matrix k p ℂ), d1 (M * N) ≤ d1 M * d1 N) := by
  intro d1 m k p _ _ _ M N
  simp only [d1]
  have hB : ∀ l : k, ∑ j : p, ‖N l j‖ ≤ ∑ l' : k, ∑ j : p, ‖N l' j‖ := fun l =>
    Finset.single_le_sum (f := fun l' => ∑ j : p, ‖N l' j‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ l)
  calc ∑ i : m, ∑ j : p, ‖(M * N) i j‖
      ≤ ∑ i : m, ∑ j : p, ∑ l : k, ‖M i l‖ * ‖N l j‖ := by
        gcongr with i _ j _
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans ?_
        gcongr with l _
        exact (norm_mul _ _).le
    _ = ∑ i : m, ∑ l : k, ‖M i l‖ * ∑ j : p, ‖N l j‖ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ i : m, ∑ l : k, ‖M i l‖ * ∑ l' : k, ∑ j : p, ‖N l' j‖ := by
        gcongr with i _ l _
        exact hB l
    _ = (∑ i : m, ∑ l : k, ‖M i l‖) * ∑ l' : k, ∑ j : p, ‖N l' j‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]

end GlobalTheory.SpectralLemmaSecond
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.BlockForms.CuspGrowth

section Esum

variable {m k p : Type} [Fintype m] [Fintype k] [Fintype p]

def esum (M : Matrix m k ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

theorem esum_nonneg (M : Matrix m k ℂ) : 0 ≤ esum M := by unfold esum; positivity

theorem esum_add_le (M N : Matrix m k ℂ) : esum (M + N) ≤ esum M + esum N := by
  unfold esum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem esum_sub_le (M N : Matrix m k ℂ) : esum (M - N) ≤ esum M + esum N := by
  unfold esum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_sub_le _ _

theorem esum_mul_le (M : Matrix m k ℂ) (N : Matrix k p ℂ) : esum (M * N) ≤ esum M * esum N := by
  first
  | exact @_root_.GlobalTheory.SpectralLemmaSecond.main
  | exact _root_.GlobalTheory.SpectralLemmaSecond.main
  | (apply _root_.GlobalTheory.SpectralLemmaSecond.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpectralLemmaSecond.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpectralLemmaSecond.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpectralLemmaSecond.main ..)

theorem esum_le_of_entry (M : Matrix m k ℂ) {c : ℝ} (h : ∀ i j, ‖M i j‖ ≤ c) :
    esum M ≤ Fintype.card m * (Fintype.card k * c) := by
  unfold esum
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j).trans ?_
  simp

theorem esum_one_le [DecidableEq m] : esum (1 : Matrix m m ℂ) ≤ Fintype.card m * (Fintype.card m * 1) :=
  esum_le_of_entry _ fun i j => by
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]

theorem opNorm_le_esum [DecidableEq m] (A : Matrix m m ℂ) : (GlobalTheory.AdelicU.opNorm A : ℝ) ≤ esum A := by
  change ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A‖ ≤ _
  refine ContinuousLinearMap.opNorm_le_bound _ (esum_nonneg A) fun x => ?_
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨mul_nonneg (esum_nonneg A) (norm_nonneg _), ?_⟩
  refine (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _).trans ?_
  unfold esum
  gcongr
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A x) i = ∑ j, A i j * x j := rfl
  rw [this, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  gcongr
  exact PiLp.norm_apply_le x j

end Esum

end GlobalTheory.BlockForms.CuspGrowth

namespace GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.CuspRep (Ad Cinf sInf infEq continuous_infEq infGL toL)

section Entries

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem exists_bound_sInf (f : Ad E →+* ℂ) (hf : Continuous f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z : Cinf E, ‖f (sInf E z)‖ ≤ L * ‖z‖ := by
  let g : Cinf E →+ ℂ :=
    { toFun := fun z => f (sInf E z)
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hg : Continuous g := hf.comp ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × GlobalTheory.CuspRep.Af E))
  let L := g.toRealLinearMap hg
  exact ⟨‖L‖, norm_nonneg _, fun z => L.le_opNorm z⟩

theorem exists_entry_bound (f : Ad E →+* ℂ) (hf : Continuous f) (d : ℕ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (y : GL (Fin d) (Cinf E)) (a b : Fin d), ‖f ((infGL E d y).1 a b)‖ ≤ c * GlobalTheory.CuspRep.height y := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_sInf f hf
  refine ⟨1 + L, by linarith, fun y a b => ?_⟩
  have e : (infGL E d y).1 a b =
      (1 : Matrix (Fin d) (Fin d) (Ad E)) a b - sInf E ((1 : Matrix (Fin d) (Fin d) (Cinf E)) a b) + sInf E (y.1 a b) := rfl
  have h1 : ‖f ((1 : Matrix (Fin d) (Fin d) (Ad E)) a b)‖ ≤ 1 := by
    by_cases h : a = b
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have h2 : ‖((1 : Matrix (Fin d) (Fin d) (Cinf E)) a b)‖ ≤ 1 := by
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    · simp [Matrix.one_apply_ne h]
  have h3 : ‖y.1 a b‖ ≤ ‖toL y.val‖ :=
    (norm_le_pi_norm (toL y.val a) b).trans (norm_le_pi_norm (toL y.val) a)
  have h4 : 0 ≤ ‖toL (y⁻¹).val‖ := norm_nonneg _
  rw [e, map_add, map_sub]
  calc ‖f ((1 : Matrix (Fin d) (Fin d) (Ad E)) a b) - f (sInf E ((1 : Matrix (Fin d) (Fin d) (Cinf E)) a b)) +
        f (sInf E (y.1 a b))‖
      ≤ 1 + L * 1 + L * ‖toL y.val‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add h1 ?_)) ?_)
        · exact (hL _).trans (mul_le_mul_of_nonneg_left h2 hL0)
        · exact (hL _).trans (mul_le_mul_of_nonneg_left h3 hL0)
    _ ≤ (1 + L) * GlobalTheory.CuspRep.height y := by
        unfold GlobalTheory.CuspRep.height
        nlinarith [norm_nonneg (toL y.val)]

theorem height_inv' {d : ℕ} (y : GL (Fin d) (Cinf E)) : GlobalTheory.CuspRep.height y⁻¹ = GlobalTheory.CuspRep.height y := by
  unfold GlobalTheory.CuspRep.height; rw [inv_inv]; ring

end Entries

end GlobalTheory.BlockForms.CuspGrowth

namespace GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.CuspRep (Ad Cinf sInf infEq continuous_infEq infGL toL pFin_infGL)
open GlobalTheory.BlockForms.LeviLoc (gl_entry fin_symm compFin_eq_zero compFin_sigR map_formula)

section Block

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]

theorem map_one_add_two_rank_perturbation {R T : Type} [CommRing R] [CommRing T] (p : R →+* T) {n d : ℕ}
    (A C : Matrix (Fin n) (Fin d) R) (B D : Matrix (Fin d) (Fin n) R) (P Q : Matrix (Fin d) (Fin d) R) :
    (1 + A * (P - 1) * B + C * (Q - 1) * D).map p =
      1 + A.map p * (P.map p - 1) * B.map p + C.map p * (Q.map p - 1) * D.map p := by
  simp [Matrix.map_add, Matrix.map_mul, Matrix.map_sub, Matrix.map_one]

variable {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
  (hΦ : ∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z)))
include hΦ

theorem map_compFin_infGL (u : HeightOneSpectrum (𝓞 F)) {d : ℕ} (y : GL (Fin d) (Cinf E)) :
    ((infGL E d y).1.map Φ.symm).map (compFin F E u) = 1 := by
  refine Matrix.ext fun a b => ?_
  have h1 := compFin_eq_zero u (Φ.symm ((infGL E d y).1 a b) - (1 : Matrix (Fin d) (Fin d) _) a b)
    fun w' _ => by
      have h2 : GlobalTheory.CuspRep.pFin E ((infGL E d y).1 a b) = (1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Af E)) a b :=
        gl_entry (pFin_infGL y) a b
      rw [map_sub, map_sub, map_sub, fin_symm hΦ, h2, sub_eq_zero]
      by_cases e : a = b
      · subst e; simp only [Matrix.one_apply_eq, map_one]
      · simp only [Matrix.one_apply_ne e, map_zero]
  rw [map_sub, sub_eq_zero] at h1
  refine h1.trans ?_
  by_cases e : a = b
  · subst e; simp only [Matrix.one_apply_eq, map_one]
  · simp only [Matrix.one_apply_ne e, map_zero]

end Block

end GlobalTheory.BlockForms.CuspGrowth

namespace GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.CuspRep (Ad Cinf sInf infEq continuous_infEq infGL toL pFin_infGL)
open GlobalTheory.BlockForms.LeviLoc (gl_entry fin_symm compFin_eq_zero compFin_sigR map_formula)

section Emb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {Xf Yf : Matrix (Fin n) (Fin r) E} {l d : ℕ}
  {h : l + d ≤ r} {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J}

theorem htFin_blockEmb_infGL (hι : IsBlockEmb σ J Xf Yf h ι) (v : HeightOneSpectrum (𝓞 F))
    (y : GL (Fin d) (Cinf E)) : htFin F v (bc (compFin F E v) (matHom (AF F) σ J (ι (infGL E d y)))) = 1 := by
  obtain ⟨Φ, j, -, -, -, hΦ, hM⟩ := hι
  have hM' := hM (infGL E d y)
  rw [← map_inv] at hM'
  have hQ : (((infGL E d y⁻¹).1.map Φ.symm).map ((compFin F E v).comp (sigR (AF F) σ))) = 1 := by
    have e : (compFin F E v).comp (sigR (AF F) σ) = (sigR _ σ).comp (compFin F E v) :=
      RingHom.ext (compFin_sigR σ v)
    rw [e, RingHom.coe_comp, ← Matrix.map_map, map_compFin_infGL hΦ, Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : bc (compFin F E v) (matHom (AF F) σ J (ι (infGL E d y))) = 1 := by
    refine Units.ext ?_
    change (matHom (AF F) σ J (ι (infGL E d y))).1.map (compFin F E v) = 1
    rw [hM', map_formula _ _ _ _ _ _ _ _ hQ, map_compFin_infGL hΦ]
    simp
  rw [e1]
  exact htOf_eq_one.2 ⟨normFin_one_le F v, by rw [inv_one]; exact normFin_one_le F v⟩

end Emb

end GlobalTheory.BlockForms.CuspGrowth

namespace GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.CuspRep (Ad Cinf sInf infEq continuous_infEq infGL toL pFin_infGL)

section Inf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {Xf Yf : Matrix (Fin n) (Fin r) E} {l d : ℕ}
  {h : l + d ≤ r} {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J}

theorem exists_opNorm_blockEmb_infGL_le (hι : IsBlockEmb σ J Xf Yf h ι) (w : InfinitePlace F) (τ : EmbOver E w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : GL (Fin d) (Cinf E),
      (opNorm ((matHom (AF F) σ J (ι (infGL E d y))).1.map ((infEmb τ).comp (compInf F E w))) : ℝ) ≤
        K * GlobalTheory.CuspRep.height y := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨Φ, j, -, hΦc, -, -, hM⟩ := hι
  set θ := (infEmb τ).comp (compInf F E w) with hθ
  have hθc : Continuous θ := GlobalTheory.Grow.continuous_infEmb_compInf F w τ
  obtain ⟨c1, hc1, hb1⟩ := exists_entry_bound (θ.comp Φ.symm.toRingHom) (hθc.comp hΦc) d
  obtain ⟨c2, hc2, hb2⟩ := exists_entry_bound (θ.comp ((sigR (AF F) σ).comp Φ.symm.toRingHom))
    (hθc.comp ((GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ).comp hΦc)) d
  set A := (adMat F (blkCols h Xf)).map θ
  set B := (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)).map θ
  set C := (adMat F (blkCols h Yf)).map θ
  set D := (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J)).map θ
  set a1 : ℝ := d * (d * c1) + d * (d * 1)
  set a2 : ℝ := d * (d * c2) + d * (d * 1)
  have ha1 : 0 ≤ a1 := add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
    (by positivity)
  have ha2 : 0 ≤ a2 := add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
    (by positivity)
  refine ⟨n * (n * 1) + esum A * a1 * esum B + esum C * a2 * esum D,
    add_nonneg (add_nonneg (by positivity) (mul_nonneg (mul_nonneg (esum_nonneg A) ha1) (esum_nonneg B)))
      (mul_nonneg (mul_nonneg (esum_nonneg C) ha2) (esum_nonneg D)), fun y => ?_⟩
  set hh := GlobalTheory.CuspRep.height y
  have h1 : 1 ≤ hh := GlobalTheory.CuspRep.one_le_height y
  set P' := ((infGL E d y).1.map Φ.symm).map θ
  set Q' := (cT (sigR (AF F) σ) (((infGL E d y)⁻¹).1.map Φ.symm)).map θ
  have eM : (matHom (AF F) σ J (ι (infGL E d y))).1.map θ = 1 + A * (P' - 1) * B + C * (Q' - 1) * D := by
    rw [hM, map_one_add_two_rank_perturbation]
  have hP : ∀ a b, ‖P' a b‖ ≤ c1 * hh := fun a b => hb1 y a b
  have hQ : ∀ a b, ‖Q' a b‖ ≤ c2 * hh := fun a b => by
    have := hb2 y⁻¹ b a
    rw [map_inv, height_inv'] at this
    exact this
  have e1d : esum (1 : Matrix (Fin d) (Fin d) ℂ) ≤ d * (d * 1) := by simpa using esum_one_le (m := Fin d)
  have e1n : esum (1 : Matrix (Fin n) (Fin n) ℂ) ≤ n * (n * 1) := by simpa using esum_one_le (m := Fin n)
  have eP : esum P' ≤ d * (d * (c1 * hh)) := by simpa using esum_le_of_entry P' hP
  have eQ : esum Q' ≤ d * (d * (c2 * hh)) := by simpa using esum_le_of_entry Q' hQ
  have hd1 : (d : ℝ) * (d * 1) ≤ d * (d * 1) * hh := le_mul_of_one_le_right (by positivity) h1
  have k1 : esum P' + esum (1 : Matrix (Fin d) (Fin d) ℂ) ≤ a1 * hh :=
    calc esum P' + esum (1 : Matrix (Fin d) (Fin d) ℂ) ≤ d * (d * (c1 * hh)) + d * (d * 1) * hh :=
          add_le_add eP (e1d.trans hd1)
      _ = a1 * hh := by ring
  have k2 : esum Q' + esum (1 : Matrix (Fin d) (Fin d) ℂ) ≤ a2 * hh :=
    calc esum Q' + esum (1 : Matrix (Fin d) (Fin d) ℂ) ≤ d * (d * (c2 * hh)) + d * (d * 1) * hh :=
          add_le_add eQ (e1d.trans hd1)
      _ = a2 * hh := by ring
  have t1 : esum (A * (P' - 1) * B) ≤ esum A * (a1 * hh) * esum B :=
    (esum_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((esum_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ((esum_sub_le _ _).trans k1) (esum_nonneg A))) (esum_nonneg B))
  have t2 : esum (C * (Q' - 1) * D) ≤ esum C * (a2 * hh) * esum D :=
    (esum_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((esum_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ((esum_sub_le _ _).trans k2) (esum_nonneg C))) (esum_nonneg D))
  have t0 : esum (1 : Matrix (Fin n) (Fin n) ℂ) ≤ n * (n * 1) * hh :=
    e1n.trans (le_mul_of_one_le_right (by positivity) h1)
  have s1 := esum_add_le (1 : Matrix (Fin n) (Fin n) ℂ) (A * (P' - 1) * B)
  have s2 := esum_add_le (1 + A * (P' - 1) * B) (C * (Q' - 1) * D)
  calc (opNorm ((matHom (AF F) σ J (ι (infGL E d y))).1.map θ) : ℝ)
      ≤ esum ((matHom (AF F) σ J (ι (infGL E d y))).1.map θ) := opNorm_le_esum _
    _ = esum (1 + A * (P' - 1) * B + C * (Q' - 1) * D) := by rw [eM]
    _ ≤ n * (n * 1) * hh + esum A * (a1 * hh) * esum B + esum C * (a2 * hh) * esum D := by linarith
    _ = (n * (n * 1) + esum A * a1 * esum B + esum C * a2 * esum D) * hh := by ring

end Inf

end GlobalTheory.BlockForms.CuspGrowth

namespace GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.CuspRep (Ad Cinf sInf infEq continuous_infEq infGL toL pFin_infGL)

section Ht

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {Xf Yf : Matrix (Fin n) (Fin r) E} {l d : ℕ}
  {h : l + d ≤ r} {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J}

theorem exists_htInf_blockEmb_infGL_le (hι : IsBlockEmb σ J Xf Yf h ι) (w : InfinitePlace F) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ y : GL (Fin d) (Cinf E),
      (htInf F w (bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y)))) : ℝ) ≤ c * GlobalTheory.CuspRep.height y := by
  choose K hK0 hK using exists_opNorm_blockEmb_infGL_le hι w
  have hS : 0 ≤ ∑ τ, K τ := Finset.sum_nonneg fun τ _ => hK0 τ
  refine ⟨1 + ∑ τ, K τ, by linarith, fun y => ?_⟩
  have hh1 := GlobalTheory.CuspRep.one_le_height y
  have hpos : 0 ≤ (1 + ∑ τ, K τ) * GlobalTheory.CuspRep.height y := by nlinarith
  have hs : ∀ τ, K τ ≤ 1 + ∑ τ, K τ := fun τ =>
    (Finset.single_le_sum (f := K) (fun τ _ => hK0 τ) (Finset.mem_univ τ)).trans (by linarith)
  have key : ∀ y' : GL (Fin d) (Cinf E), GlobalTheory.CuspRep.height y' = GlobalTheory.CuspRep.height y →
      normInf F w ((bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y')))).1) ≤
        Real.toNNReal ((1 + ∑ τ, K τ) * GlobalTheory.CuspRep.height y) := by
    intro y' hy'
    refine (normInf_le_iff F w).2 fun τ => ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hpos]
    change (opNorm (((matHom (AF F) σ J (ι (infGL E d y'))).1.map (compInf F E w)).map (infEmb τ)) : ℝ) ≤ _
    rw [Matrix.map_map]
    refine (hK τ y').trans ?_
    rw [hy']
    exact mul_le_mul_of_nonneg_right (hs τ) (by linarith)
  have e : (bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y))))⁻¹ =
      bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y⁻¹))) := by simp only [map_inv]
  have h1 : (1 : ℝ≥0) ≤ Real.toNNReal ((1 + ∑ τ, K τ) * GlobalTheory.CuspRep.height y) := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hpos, NNReal.coe_one]; nlinarith
  have hle : htInf F w (bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y)))) ≤
      Real.toNNReal ((1 + ∑ τ, K τ) * GlobalTheory.CuspRep.height y) := by
    refine max_le h1 (max_le (key y rfl) ?_)
    rw [e]
    exact key y⁻¹ (height_inv' y)
  exact (NNReal.coe_le_coe.2 hle).trans (le_of_eq (Real.coe_toNNReal _ hpos))

theorem exists_height_blockEmb_infGL_le (hι : IsBlockEmb σ J Xf Yf h ι) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : GL (Fin d) (Cinf E),
      (height σ J (ι (infGL E d y)) : ℝ) ≤ K * GlobalTheory.CuspRep.height y ^ Fintype.card (InfinitePlace F) := by
  choose c hc1 hc using exists_htInf_blockEmb_infGL_le hι
  refine ⟨∏ w, c w, Finset.prod_nonneg fun w _ => by linarith [hc1 w], fun y => ?_⟩
  have e : height σ J (ι (infGL E d y)) =
      ∏ w, htInf F w (bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y)))) := by
    unfold GlobalTheory.AdelicU.height heightGL
    simp only [htFin_blockEmb_infGL hι, finprod_one, mul_one]
  rw [e, NNReal.coe_prod]
  calc ∏ w, (htInf F w (bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y)))) : ℝ)
      ≤ ∏ w, (c w * GlobalTheory.CuspRep.height y) :=
        Finset.prod_le_prod (fun w _ => NNReal.coe_nonneg _) fun w _ => hc w y
    _ = (∏ w, c w) * GlobalTheory.CuspRep.height y ^ Fintype.card (InfinitePlace F) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end Ht

end GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.BlockForms.CuspGrowth in

theorem GlobalTheory.BlockForms.growth_comp_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        ∀ g : GlobalTheory.CuspRep.GA E d, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι hι _ _ _ _ ψ hψ g₀ _ g
  obtain ⟨N, hN⟩ := hψ.1.growth
  obtain ⟨C0, hC0⟩ := hN [] (by simp)
  obtain ⟨K', hK'0, hK'⟩ := exists_height_blockEmb_infGL_le hι
  set a : ℝ := (height σ J (ι g) : ℝ)
  set b : ℝ := (height σ J g₀ : ℝ)
  have ha : 0 ≤ a := NNReal.coe_nonneg _
  have hb : 0 ≤ b := NNReal.coe_nonneg _
  refine ⟨max C0 0 * (a * K' * b) ^ N, Fintype.card (InfinitePlace F) * N, fun y => ?_⟩
  set c := Fintype.card (InfinitePlace F)
  have hx : ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀ = ι g * ι (GlobalTheory.CuspRep.infGL E d y) * g₀ := by rw [map_mul]
  have hH : (height σ J (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀) : ℝ) ≤
      a * (K' * GlobalTheory.CuspRep.height y ^ c) * b := by
    rw [hx]
    have e1 : (height σ J (ι g * ι (GlobalTheory.CuspRep.infGL E d y) * g₀) : ℝ) ≤
        height σ J (ι g * ι (GlobalTheory.CuspRep.infGL E d y)) * b := by
      exact_mod_cast height_mul_le σ J (ι g * ι (GlobalTheory.CuspRep.infGL E d y)) g₀
    have e2 : (height σ J (ι g * ι (GlobalTheory.CuspRep.infGL E d y)) : ℝ) ≤
        a * height σ J (ι (GlobalTheory.CuspRep.infGL E d y)) := by
      exact_mod_cast height_mul_le σ J (ι g) (ι (GlobalTheory.CuspRep.infGL E d y))
    exact e1.trans (mul_le_mul_of_nonneg_right (e2.trans (mul_le_mul_of_nonneg_left (hK' y) ha)) hb)
  have h0 := hC0 (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀)
  simp only [List.foldr_nil] at h0
  have hHn : 0 ≤ (height σ J (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀) : ℝ) := NNReal.coe_nonneg _
  calc ‖ψ (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀)‖
      ≤ C0 * (height σ J (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀) : ℝ) ^ N := h0
    _ ≤ max C0 0 * (height σ J (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀) : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hHn _)
    _ ≤ max C0 0 * (a * (K' * GlobalTheory.CuspRep.height y ^ c) * b) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHn hH _) (le_max_right _ _)
    _ = max C0 0 * (a * K' * b) ^ N * GlobalTheory.CuspRep.height y ^ (c * N) := by ring
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ContDiff

noncomputable section

namespace GlobalTheory.BlockRealLine

open Matrix
open scoped TensorProduct
open Formalism.UG (cT bc)
open GlobalTheory.CuspRep (Cinf infEq sInf infGL expGLi)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev infComp (w : InfinitePlace F) : Ainf F ⊗[F] E →+* w.Completion ⊗[F] E :=
  (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom

omit [NumberField E] in

theorem exists_place_of_prim {R : Type} [CommRing R] (j : Ainf F ⊗[F] E ≃+* R) (e : R) (he : e * e = e)
    (hp : ∀ f : R, f * f = f → f * e = f → f = 0 ∨ f = e) (y : Ainf F ⊗[F] E) (hy : j y = e) :
    ∃ w : InfinitePlace F, ∀ w', w' ≠ w → infComp w' y = 0 := by
  classical
  have hyy : y * y = y := j.injective (by rw [map_mul, hy, he])
  by_contra hne
  push_neg at hne
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨w1, -, h1⟩ := hne w0
  obtain ⟨w2, h12, h2⟩ := hne w1
  let δ : Ainf F ⊗[F] E := (GlobalTheory.AutFunCompare.sgW w1 (1 : w1.Completion)) ⊗ₜ[F] (1 : E)
  have hδ1 : infComp w1 δ = 1 := by
    change (GlobalTheory.AutFunCompare.evW w1 (GlobalTheory.AutFunCompare.sgW w1 (1 : w1.Completion))) ⊗ₜ[F] (1 : E) = 1
    rw [show GlobalTheory.AutFunCompare.evW w1 (GlobalTheory.AutFunCompare.sgW w1 (1 : w1.Completion)) = 1 from Pi.single_eq_same w1 _]
    rfl
  have hδ2 : infComp w2 δ = 0 := by
    change (GlobalTheory.AutFunCompare.evW w2 (GlobalTheory.AutFunCompare.sgW w1 (1 : w1.Completion))) ⊗ₜ[F] (1 : E) = 0
    rw [show GlobalTheory.AutFunCompare.evW w2 (GlobalTheory.AutFunCompare.sgW w1 (1 : w1.Completion)) = 0 from Pi.single_eq_of_ne h12 _]
    exact TensorProduct.zero_tmul _ _
  have hδδ : δ * δ = δ := by
    change _ ⊗ₜ[F] _ * _ ⊗ₜ[F] _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← GlobalTheory.AutFunCompare.sgW_mul, mul_one]
  rcases hp (j (y * δ)) (by
      rw [← map_mul]; congr 1
      calc y * δ * (y * δ) = (y * y) * (δ * δ) := by ring
        _ = y * δ := by rw [hyy, hδδ]) (by
      rw [← hy, ← map_mul]; congr 1
      calc y * δ * y = (y * y) * δ := by ring
        _ = y * δ := by rw [hyy]) with h | h
  · apply h1
    have e0 : y * δ = 0 := j.injective (h.trans (map_zero j).symm)
    have := congrArg (infComp w1) e0
    rwa [map_mul, hδ1, mul_one, map_zero] at this
  · apply h2
    have e0 : y * δ = y := j.injective (h.trans hy.symm)
    have := congrArg (infComp w2) e0
    rwa [map_mul, hδ2, mul_zero, eq_comm] at this

omit [NumberField E] in

theorem single_prim [DecidableEq (InfinitePlace E)] (v : InfinitePlace E) (f : Cinf E) (h1 : f * f = f)
    (h2 : f * Pi.single v 1 = f) : f = 0 ∨ f = Pi.single v 1 := by
  have hne : ∀ u, u ≠ v → f u = 0 := fun u hu => by
    have := congrFun h2 u
    rw [Pi.mul_apply, Pi.single_eq_of_ne hu, mul_zero] at this
    exact this.symm
  by_cases hv : f v = 0
  · left
    funext u
    by_cases hu : u = v
    · subst hu; exact hv
    · exact hne u hu
  · right
    funext u
    by_cases hu : u = v
    · subst hu
      rw [Pi.single_eq_same]
      have h := congrFun h1 u
      rw [Pi.mul_apply] at h
      exact mul_left_cancel₀ hv (h.trans (mul_one _).symm)
    · rw [Pi.single_eq_of_ne hu]; exact hne u hu

end GlobalTheory.BlockRealLine

namespace GlobalTheory.BlockRealLine

open Matrix
open scoped TensorProduct
open Formalism.UG (cT bc)
open GlobalTheory.CuspRep (Cinf infEq infGL expGLi)

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem compInf_eq_infComp (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w z = infComp w (GlobalTheory.LFun.infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

omit [NumberField E] in

theorem compInf_sigR (σ : E →ₐ[F] E) (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w (sigR _ σ z) = sigR _ σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

omit [NumberField F] [Algebra F E] in

theorem evalMat_exp {d : ℕ} (u : InfinitePlace E) (X : Matrix (Fin d) (Fin d) (Cinf E)) :
    (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix (NormedSpace.exp X) =
      NormedSpace.exp ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix X) := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) (Cinf E)) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) ℂ) := FiniteDimensional.complete ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hc : Continuous ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix :
      Matrix (Fin d) (Fin d) (Cinf E) → Matrix (Fin d) (Fin d) ℂ) :=
    LinearMap.continuous_of_finiteDimensional ((LinearMap.proj u : Cinf E →ₗ[ℝ] ℂ).mapMatrix)
  exact NormedSpace.map_exp (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix hc X

variable [IsTotallyComplex E]

theorem map_compInf_infGL {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
    (hΦ : ∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z)))
    [DecidableEq (InfinitePlace E)] {v : InfinitePlace E} {w' : InfinitePlace F}
    (hw : infComp w' (j.symm (infEq E (Pi.single v 1))) = 0) {d : ℕ} (y : GL (Fin d) (Cinf E))
    (hy : ∀ u, u ≠ v → ∀ a b, y.1 a b u = (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b u) :
    ((infGL E d y).1.map Φ.symm).map (compInf F E w') = 1 := by
  have key : ∀ x, GlobalTheory.LFun.infTens F E (Φ.symm x) = j.symm x.1 := fun x => by
    have e := congrArg Prod.fst (hΦ (Φ.symm x))
    rw [RingEquiv.apply_symm_apply] at e
    rw [e, RingEquiv.symm_apply_apply]
  ext a b
  have hcv : y.1 a b - (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b =
      (y.1 a b - (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b) * Pi.single v 1 := by
    funext u
    by_cases hu : u = v
    · subst hu; simp
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hu, mul_zero, Pi.sub_apply, hy u hu, sub_self]
  have hx : (infGL E d y).1 a b = (1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b +
      GlobalTheory.CuspRep.sInf E (y.1 a b - (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b) := by
    change (1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b -
      GlobalTheory.CuspRep.sInf E ((1 : Matrix (Fin d) (Fin d) (Cinf E)) a b) + GlobalTheory.CuspRep.sInf E (y.1 a b) = _
    rw [map_sub]; abel
  have h0 : compInf F E w' (Φ.symm (GlobalTheory.CuspRep.sInf E (y.1 a b - (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b))) = 0 := by
    rw [compInf_eq_infComp, key]
    change infComp w' (j.symm (infEq E (y.1 a b - (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b))) = 0
    rw [hcv, map_mul, map_mul, map_mul, hw, mul_zero]
  simp only [Matrix.map_apply, hx, map_add, h0, add_zero]
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.one_apply_ne hab]

end SlopeTestRemainingChoices

end GlobalTheory.BlockRealLine

namespace GlobalTheory.BlockRealLine

open Matrix
open scoped TensorProduct
open Formalism.UG (cT bc)
open GlobalTheory.CuspRep (Cinf infEq infGL expGLi)

theorem isRealLine_blockEmb_exp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
    ∀ (v : InfinitePlace E) (X : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i j, ∀ u, u ≠ v → X i j u = 0) →
      IsRealLine σ J fun t : ℝ => ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • X))) := by
  intro F E _ _ _ _ _ _ σ hcm n J _ r Xf Yf _ l d h ι hι v X hX
  classical
  obtain ⟨Φ, j, -, -, -, hΦ, hM⟩ := id hι
  obtain ⟨w, hw⟩ := exists_place_of_prim (j.trans (infEq E).symm) (Pi.single v (1 : ℂ))
    (by rw [← Pi.single_mul, one_mul]) (single_prim v) (j.symm (infEq E (Pi.single v 1))) (by simp)

  have hexp : ∀ t : ℝ, ∀ u, u ≠ v → ∀ a b,
      (expGLi d (t • X)).1 a b u = (1 : Matrix (Fin d) (Fin d) (Cinf E)) a b u := by
    intro t u hu a b
    have hz : (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix (t • X) = 0 := by
      ext a' b'
      change t • X a' b' u = 0
      rw [hX a' b' u hu, smul_zero]
    have H : (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix (NormedSpace.exp (t • X)) =
        (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) u).mapMatrix 1 := by
      rw [evalMat_exp, hz, NormedSpace.exp_zero, map_one]
    exact congrFun₂ H a b
  have hinv : ∀ t : ℝ, (expGLi d (t • X))⁻¹ = expGLi d ((-t) • X) := fun t => by
    have e := GlobalTheory.CuspRep.expGLi_add_smul d X (-t) t
    rw [neg_add_cancel, zero_smul, GlobalTheory.CuspRep.expGLi_zero] at e
    exact (eq_inv_of_mul_eq_one_left e.symm).symm

  have hcexp : Continuous fun t : ℝ => ((expGLi d (t • X) : GL (Fin d) (Cinf E)) : Matrix (Fin d) (Fin d) (Cinf E)) := by
    letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
    haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
    exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).continuousAt
  have hcGL : Continuous fun t : ℝ => expGLi d (t • X) := by
    refine Units.continuous_iff.2 ⟨hcexp, ?_⟩
    have e : (fun t : ℝ => (((expGLi d (t • X))⁻¹ : GL (Fin d) (Cinf E)) : Matrix (Fin d) (Fin d) (Cinf E))) =
        fun t => ((expGLi d ((-t) • X) : GL (Fin d) (Cinf E)) : Matrix (Fin d) (Fin d) (Cinf E)) :=
      funext fun t => by rw [hinv]
    rw [e]
    exact hcexp.comp continuous_neg
  have hcinf : Continuous (infGL E d) := by
    refine Continuous.units_map _ ?_
    have hs : Continuous (GlobalTheory.CuspRep.sInf E : Cinf E → GlobalTheory.CuspRep.Ad E) :=
      (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
    exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)
  let δ : ℝ → GAd σ J := fun t => ι (infGL E d (expGLi d (t • X)))
  have hc : Continuous δ := (GlobalTheory.BlockLevel.continuous_of_isBlockEmb hι).comp (hcinf.comp hcGL)
  have h0 : δ 0 = 1 := by simp only [δ, zero_smul, GlobalTheory.CuspRep.expGLi_zero, map_one]
  have hm : ∀ s t, δ (s + t) = δ s * δ t := fun s t => by
    simp only [δ, GlobalTheory.CuspRep.expGLi_add_smul, map_mul]

  have hinf : ∀ w', w' ≠ w → ∀ t, projArch σ J w' (δ t) = 1 := by
    intro w' hw' t
    have hM' := hM (infGL E d (expGLi d (t • X)))
    rw [← map_inv, hinv] at hM'
    have hQ : ((infGL E d (expGLi d ((-t) • X))).1.map Φ.symm).map ((compInf F E w').comp (sigR (AF F) σ)) = 1 := by
      have e : (compInf F E w').comp (sigR (AF F) σ) = (sigR _ σ).comp (compInf F E w') :=
        RingHom.ext (compInf_sigR σ w')
      rw [e, RingHom.coe_comp, ← Matrix.map_map, map_compInf_infGL hΦ (hw w' hw') _ (hexp (-t)),
        Matrix.map_one _ (map_zero _) (map_one _)]
    apply matHom_injective (w'.Completion) σ J
    rw [matHom_projArch, map_one]
    refine Units.ext ?_
    change (matHom (AF F) σ J (ι (infGL E d (expGLi d (t • X))))).1.map (compInf F E w') = 1
    rw [hM', GlobalTheory.BlockForms.LeviLoc.map_formula _ _ _ _ _ _ _ _ hQ, map_compInf_infGL hΦ (hw w' hw') _ (hexp t)]
    simp
  have hfin : ∀ v' t, proj σ J v' (δ t) = 1 := by
    intro v' t
    have hM' := hM (infGL E d (expGLi d (t • X)))
    rw [← map_inv] at hM'
    have hQ : ((infGL E d (expGLi d (t • X))⁻¹).1.map Φ.symm).map ((compFin F E v').comp (sigR (AF F) σ)) = 1 := by
      have e : (compFin F E v').comp (sigR (AF F) σ) = (sigR _ σ).comp (compFin F E v') :=
        RingHom.ext (GlobalTheory.BlockForms.LeviLoc.compFin_sigR σ v')
      rw [e, RingHom.coe_comp, ← Matrix.map_map, GlobalTheory.BlockForms.CuspGrowth.map_compFin_infGL hΦ,
        Matrix.map_one _ (map_zero _) (map_one _)]
    apply matHom_injective _ σ J
    rw [matHom_proj, map_one]
    refine Units.ext ?_
    change (matHom (AF F) σ J (ι (infGL E d (expGLi d (t • X))))).1.map (compFin F E v') = 1
    rw [hM', GlobalTheory.BlockForms.LeviLoc.map_formula _ _ _ _ _ _ _ _ hQ, GlobalTheory.BlockForms.CuspGrowth.map_compFin_infGL hΦ]
    simp
  have hδ : δ = fun t => embArch σ J w (projArch σ J w (δ t)) := by
    funext t
    refine GAd_ext σ J (fun w'' => ?_) fun v' => ?_
    · by_cases e : w'' = w
      · subst e; rw [projArch_embArch_self]
      · rw [projArch_embArch_ne σ J e, hinf w'' e t]
    · rw [proj_embArch, hfin v' t]
  have hline := GlobalTheory.LineDerSum.isRealLine_component hcm J δ hc h0 hm w
  rw [← hδ] at hline
  exact hline

end GlobalTheory.BlockRealLine
end
end
