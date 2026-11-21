import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitarySelfDualLatticeGridDoubling
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipVacuumEqMultipleOfTranslateMean

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.StdLoc

open GlobalTheory.StdPairCone GlobalTheory.LFun GlobalTheory.FunObj.Comparison₂
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

variable {D : D7}

theorem cpt_locIdele (w Q : Pl D.host.E) (y : (Kw w)ˣ) :
    cpt (D := D) Q (toEAf D (locIdele D.host.F w y : AE D)) = (Neutral.B1.finiteSingle D.host.E w (y : Kw w)) Q := by
  rw [GlobalTheory.DepthFix.cpt_eq_finAd]
  exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (finTens_locIdele (F := D.host.F) w y)

def prodId (S : Finset (Pl D.host.E)) (y : ∀ w : S, (Kw w.1)ˣ) : (AE D)ˣ := ∏ w : S, locIdele D.host.F w.1 (y w)

theorem infPart_prodId (S : Finset (Pl D.host.E)) (y : ∀ w : S, (Kw w.1)ˣ) : infPart D (prodId S y : AE D) = 1 := by
  rw [prodId, Units.coe_prod, map_prod]
  exact Finset.prod_eq_one fun w _ => infTens_locIdele (F := D.host.F) w.1 _

theorem cpt_prodId_mem (S : Finset (Pl D.host.E)) (y : ∀ w : S, (Kw w.1)ˣ) (Q : S) :
    cpt (D := D) Q.1 (toEAf D (prodId S y : AE D)) = y Q := by
  classical
  rw [prodId, Units.coe_prod, map_prod, map_prod, Finset.prod_eq_single Q]
  · rw [cpt_locIdele, finSingle_self]
  · intro b _ hb
    rw [cpt_locIdele]
    exact finSingle_ne (fun h => hb (Subtype.ext h.symm)) _
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem cpt_prodId_notMem (S : Finset (Pl D.host.E)) (y : ∀ w : S, (Kw w.1)ˣ) {Q : Pl D.host.E} (hQ : Q ∉ S) :
    cpt (D := D) Q (toEAf D (prodId S y : AE D)) = 1 := by
  rw [prodId, Units.coe_prod, map_prod, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [cpt_locIdele]
  exact finSingle_ne (fun h => hQ (by rw [h]; exact w.2)) _

theorem prodId_inv (S : Finset (Pl D.host.E)) (y : ∀ w : S, (Kw w.1)ˣ) : (prodId S y)⁻¹ = prodId S fun w => (y w)⁻¹ := by
  simp only [prodId, map_inv, Finset.prod_inv_distrib]

theorem int_iff (w : Pl D.host.E) (y : Kw w) :
    y ∈ w.adicCompletionIntegers D.host.E ↔ ValuativeRel.valuation (Kw w) y ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans (vEq w).le_one_iff_le_one.symm

theorem cpt_twist_mem {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (z : EAf D) {w : Pl D.host.E} (hw : w ∈ S) :
    cpt (D := D) w (1 - toEAf D e + toEAf D e * z) = cpt (D := D) w z := by
  rw [RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, (cpt_idemSum he).2.1 w hw, sub_self, zero_add, one_mul]

theorem cpt_twist_notMem {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (z : EAf D) {w : Pl D.host.E} (hw : w ∉ S) :
    cpt (D := D) w (1 - toEAf D e + toEAf D e * z) = 1 := by
  rw [RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, (cpt_idemSum he).2.2 w hw, sub_zero, zero_mul, add_zero]

theorem cpt_mul_inv (w : Pl D.host.E) (x : (AE D)ˣ) :
    cpt (D := D) w (toEAf D (x : AE D)) * cpt (D := D) w (toEAf D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
  have h : toEAf D (x : AE D) * toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  rw [← RingHom.map_mul, h, RingHom.map_one]

theorem unit_of_isUnitDet {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {N : Matrix (Fin k) (Fin k) (EAf D)} {x : (AE D)ˣ} (hx : IsUnitDet e N x) {w : Pl D.host.E} (hw : w ∈ S)
    (hN : ValuativeRel.valuation (Kw w) (cpt (D := D) w N.det) ≤ 1) :
    cpt (D := D) w N.det ≠ 0 ∧ ValuativeRel.valuation (Kw w) (cpt (D := D) w N.det) = 1 := by
  obtain ⟨-, h2, h3⟩ := hx
  have h4 := (int_iff w _).1 ((mem_OA_iff _).1 h3 w)
  have h5 := cpt_mul_inv w x
  rw [h2, cpt_twist_mem he _ hw] at h5
  refine ⟨left_ne_zero_of_mul_eq_one h5, le_antisymm hN ?_⟩
  have h6 := congrArg (ValuativeRel.valuation (Kw w)) h5
  rw [map_mul, map_one] at h6
  exact h6.ge.trans (mul_le_of_le_one_right' h4)

theorem unitChar_eq_prod (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    (N : Matrix (Fin k) (Fin k) (EAf D)) (hN : ∀ w ∈ S, ValuativeRel.valuation (Kw w) (cpt (D := D) w N.det) ≤ 1) :
    unitChar ν e N = ∏ w ∈ S, unitInd (locChar ν w) (cpt (D := D) w N.det) := by
  classical
  by_cases h : ∀ w ∈ S, cpt (D := D) w N.det ≠ 0 ∧ ValuativeRel.valuation (Kw w) (cpt (D := D) w N.det) = 1
  · let y : ∀ w : S, (Kw w.1)ˣ := fun w => Units.mk0 _ (h w.1 w.2).1
    have k1 : ∀ Q, cpt (D := D) Q (toEAf D (prodId S y : AE D)) = cpt (D := D) Q (1 - toEAf D e + toEAf D e * N.det) :=
      fun Q => by
        by_cases hQ : Q ∈ S
        · exact (cpt_prodId_mem S y ⟨Q, hQ⟩).trans (cpt_twist_mem he _ hQ).symm
        · exact (cpt_prodId_notMem S y hQ).trans (cpt_twist_notMem he _ hQ).symm
    have hx : ∃ x, IsUnitDet e N x := by
      refine ⟨prodId S y, infPart_prodId S y, cpt_ext k1, (mem_OA_iff _).2 fun Q => ?_⟩
      rw [prodId_inv]
      by_cases hQ : Q ∈ S
      · rw [cpt_prodId_mem S _ ⟨Q, hQ⟩, int_iff, Units.val_inv_eq_inv_val, map_inv₀]
        exact le_of_eq (inv_eq_one.2 (h Q hQ).2)
      · rw [cpt_prodId_notMem S _ hQ]
        exact one_mem _
    have hc : hx.choose = prodId S y := Units.ext (GlobalTheory.FunObj.ae_ext (hx.choose_spec.1.trans (infPart_prodId S y).symm)
      fun Q => by rw [hx.choose_spec.2.1, k1])
    rw [unitChar, dif_pos hx, hc, ← Finset.prod_coe_sort, prodId, map_prod, ← Finset.prod_inv_distrib]
    refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun w _ => ?_)
    rw [unitInd, dif_pos (h w.1 w.2)]
    rfl
  · rw [unitChar, dif_neg fun ⟨x, hx⟩ => h fun w hw => unit_of_isUnitDet he hx hw (hN w hw)]
    push Not at h
    obtain ⟨w, hw, h⟩ := h
    exact (Finset.prod_eq_zero hw (by rw [unitInd, dif_neg fun h' => h h'.1 h'.2])).symm

theorem mem_cball_iff (w : Pl D.host.E) (c : ℕ) (y : Kw w) :
    y ∈ cball (unifAt w ^ c) ↔ Valued.v y ≤ WithZero.exp (-(c : ℤ)) := by
  have h : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  refine (vEq w _ _).trans ?_
  rw [Units.val_pow_eq_pow_val, map_pow, h, ← WithZero.exp_nsmul]
  simp

theorem inId_iff (S : Finset (Pl D.host.E)) (c : Pl D.host.E → ℕ) {z : EAf D} (hz : z ∈ OA D) :
    InId (∏ w ∈ S, w.asIdeal ^ c w) z ↔ ∀ w ∈ S, cpt (D := D) w z ∈ cball (unifAt w ^ c w) := by
  have h : ∏ w ∈ S, w.asIdeal ^ c w = S.inf fun w => w.asIdeal ^ c w :=
    (HeightOneSpectrum.inf_pow_eq_prod S c (fun w => w) fun _ _ _ _ hne => hne).symm
  have h0 : ∏ w ∈ S, w.asIdeal ^ c w ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  simp only [mem_cball_iff]
  constructor
  · rintro ⟨h1, h2⟩ w hw
    exact v_le_of_mem_idS (s := ⟨z, h1⟩) (h.le.trans (Finset.inf_le hw)) h2
  · intro H
    exact ⟨hz, mem_idS_of_v_le (w := fun w => w) h0 h (s := ⟨z, hz⟩) H⟩

open Classical in

theorem stdA_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1) (c : ℕ) {a b a₁ a₂ : ℕ} (ha : a = a₁) (hb : b = a₁ + a₂)
    (N : Matrix (Fin b) (Fin a) k) (M : Matrix (Fin a₁) (Fin (a₁ + a₂)) k)
    (hM : ∀ r s, M r s = N (Fin.cast hb.symm s) (Fin.cast ha.symm r)) :
    stdA ν ϖ c a₁ a₂ M =
      if (∀ i j, ValuativeRel.valuation k (N i j) ≤ 1) ∧ ∀ i j, a ≤ i.1 → N i j ∈ cball (ϖ ^ c) then
        unitInd ν (topL a N).det else 0 := by
  subst ha hb
  have hM' : ∀ r s, M r s = N s r := hM
  have e1 : blk₁ M = (topL a N)ᵀ := by
    ext r s
    rw [blk₁, of_apply, hM', transpose_apply, topL, dif_pos ⟨by omega, r.2⟩]
    rfl
  have e2 : (blk₁ M).det = (topL a N).det := by rw [e1, det_transpose]
  have e3 : (∀ i j, blk₂ M i j ∈ cball (ϖ ^ c)) ↔ ∀ i j, a ≤ i.1 → N i j ∈ cball (ϖ ^ c) := by
    refine ⟨fun H i j hi => ?_, fun H i j => ?_⟩
    · have := H j ⟨i.1 - a, by omega⟩
      rw [blk₂, of_apply, hM'] at this
      convert this using 2
      ext
      simp only [Fin.natAdd_mk]
      omega
    · rw [blk₂, of_apply, hM']
      exact H _ _ (by simp)
  have e4 : ∀ y ∈ cball (ϖ ^ c), ValuativeRel.valuation k y ≤ 1 := fun y hy => by
    refine le_trans (show ValuativeRel.valuation k y ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k) from hy) ?_
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one' hϖ c
  unfold stdA
  split_ifs with h1 h2 h2
  · rw [unitInd, dif_pos ⟨e2 ▸ h1.1, e2 ▸ h1.2.1.2⟩]
    simp only [e2]
  · refine absurd ⟨fun i j => ?_, e3.1 h1.2.2⟩ h2
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [← hM']
      exact h1.2.1.1 j i
    · exact e4 _ (e3.1 h1.2.2 _ _ (by simp))
  · rw [unitInd, dif_neg]
    intro h3
    refine h1 ⟨e2 ▸ h3.1, ⟨fun i j => ?_, e2 ▸ h3.2⟩, e3.2 h2.2⟩
    rw [blk₁, of_apply, hM']
    exact h2.1 _ _
  · rfl

theorem valuation_det_le {k : Type} [Field k] [ValuativeRel k] {n : ℕ} {M : Matrix (Fin n) (Fin n) k}
    (h : ∀ i j, ValuativeRel.valuation k (M i j) ≤ 1) : ValuativeRel.valuation k M.det ≤ 1 := by
  let A : Matrix (Fin n) (Fin n) (ValuativeRel.valuation k).integer := fun i j => ⟨M i j, h i j⟩
  have e : M.det = ((A.det : (ValuativeRel.valuation k).integer) : k) :=
    (RingHom.map_det (ValuativeRel.valuation k).integer.subtype A).symm
  rw [e]
  exact A.det.2

theorem topL_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {b a : ℕ} (n : ℕ) (N : Matrix (Fin b) (Fin a) R) :
    f (topL n N).det = (topL n (N.map f)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, map_apply, topL]
  split_ifs
  · rfl
  · exact map_zero f

theorem valuation_unifAt_le (w : Pl D.host.E) : ValuativeRel.valuation (Kw w) (unifAt w : Kw w) ≤ 1 := by
  have h : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  rw [(vEq w).le_one_iff_le_one, h, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

open Classical in

theorem std_eq_prod (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (c : Pl D.host.E → ℕ)
    {a b : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) (h0 : ∀ w ∉ S, ∀ i j, cpt (D := D) w (N i j) = 0) :
    (if IsIntM N ∧ ∀ i j, a ≤ i.1 → InId (∏ w ∈ S, w.asIdeal ^ c w) (N i j) then unitChar ν e (topL a N) else 0) =
      ∏ w ∈ S, if (∀ i j, ValuativeRel.valuation (Kw w) (N.map (cpt (D := D) w) i j) ≤ 1) ∧
          ∀ i j, a ≤ i.1 → N.map (cpt (D := D) w) i j ∈ cball (unifAt w ^ c w) then
        unitInd (locChar ν w) (topL a (N.map (cpt (D := D) w))).det else 0 := by
  have e1 : IsIntM N ↔ ∀ w ∈ S, ∀ i j, ValuativeRel.valuation (Kw w) (cpt (D := D) w (N i j)) ≤ 1 := by
    refine ⟨fun H w _ i j => (int_iff w _).1 ((mem_OA_iff _).1 (H i j) w), fun H i j => (mem_OA_iff _).2 fun w => ?_⟩
    by_cases hw : w ∈ S
    · exact (int_iff w _).2 (H w hw i j)
    · rw [h0 w hw]
      exact zero_mem _
  rw [Finset.prod_ite_zero]
  split_ifs with h1 h2 h2
  · rw [unitChar_eq_prod ν he _ fun w hw => ?_]
    · exact Finset.prod_congr rfl fun w _ => by rw [topL_map]
    · rw [topL_map]
      refine valuation_det_le fun i j => ?_
      unfold topL
      split_ifs
      · exact (h2 w hw).1 _ _
      · rw [map_zero]
        exact zero_le_one
  · exact absurd (fun w hw => ⟨e1.1 h1.1 w hw, fun i j hi => (inId_iff S c (h1.1 i j)).1 (h1.2 i j hi) w hw⟩) h2
  · have h3 := e1.2 fun w hw => (h2 w hw).1
    exact absurd ⟨h3, fun i j hi => (inId_iff S c (h3 i j)).2 fun w hw => (h2 w hw).2 i j hi⟩ h1
  · rfl

theorem cpt_frMapO_eq_zero {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (A WW : HSp D)
    (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) {x : WO A WW} (hx : IsHalf e x) {w : Pl D.host.E} (hw : w ∉ S)
    (i : Fin WW.rank) (j : Fin A.rank) : cpt (D := D) w (frMapO A WW βA βW x i j) = 0 := by
  have h : ((x : Matrix (Fin WW.rank) (Fin A.rank) (AE D)).map (toEAf D)).map (cpt (D := D) w) = 0 := by
    refine Matrix.ext fun r s => ?_
    change cpt (D := D) w (toEAf D (x r s)) = 0
    rw [← hx r s, RingHom.map_mul, RingHom.map_mul, (cpt_idemSum he).2.2 w hw, zero_mul]
  change (frMapO A WW βA βW x).map (cpt (D := D) w) i j = 0
  rw [frMapO, Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]

theorem change_eq {k : Type} [Field k] {a d a' d' : Type} [Fintype a] [DecidableEq a] [Fintype d] [DecidableEq d]
    [Fintype a'] [DecidableEq a'] [Fintype d'] [DecidableEq d'] (ea : a ≃ a') (ed : d ≃ d') (β β' : GL a k) (γ γ' : GL d k)
    (x : Matrix d a k) :
    (GlobalTheory.StepData.reGL ea (invT (β⁻¹ * β'))).val * reindex ea ed ((γ'⁻¹).val * x * β'.val)ᵀ *
      (invT (GlobalTheory.StepData.reGL ed (γ'⁻¹ * γ))).val = reindex ea ed ((γ⁻¹).val * x * β.val)ᵀ := by
  have h1 : (invT (GlobalTheory.StepData.reGL ed (γ'⁻¹ * γ))).val = (((γ⁻¹ * γ').val)ᵀ).submatrix ed.symm ed.symm := by
    change ((GlobalTheory.StepData.reGL ed (γ'⁻¹ * γ))⁻¹).valᵀ = _
    rw [← map_inv, GlobalTheory.StepData.reGL_val, _root_.mul_inv_rev, inv_inv, transpose_submatrix]
  have h2 : (invT (β⁻¹ * β')).val = ((β'⁻¹ * β).val)ᵀ := by
    change ((β⁻¹ * β')⁻¹).valᵀ = _
    rw [_root_.mul_inv_rev, inv_inv]
  rw [h1, GlobalTheory.StepData.reGL_val, h2, reindex_apply, reindex_apply, submatrix_mul_equiv, submatrix_mul_equiv, ← transpose_mul,
    ← transpose_mul]
  congr 2
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc β'.val, ← Matrix.mul_assoc γ'.val, Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.one_mul]

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

theorem locChar_nu {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) :
    locChar (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) w = (locGrid G t w).nu i j := by
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) :=
    mul_div_mul_right_eq_div _ _ _
  rw [e1, locChar_eq_of_chrEq (SqNum.chrEq_nu G t i j hL)]
  have hj : (j : ℕ) < D.R.m := j.2
  ext x
  simp only [SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Formalism.L2.Host.HChar.loc_mul,
    Formalism.L2.Host.HChar.loc_inv, div_eq_mul_inv]
  rfl

theorem ordX_colX_val (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) (s : Fin (spX G i j).rank) :
    (ordX G t i j w (colX G t i j w s)).val = s.val := by
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective s
  simp only [ordX, colX, SplitFlip.stdSplit, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply]
  rcases s with s | s
  · rfl
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right, finCongr_symm, finCongr_apply, Fin.val_cast,
      Fin.val_natAdd]
    congr 1
    exact rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩

end GlobalTheory.TopFlip.StdLoc

namespace GlobalTheory.TopFlip

open GlobalTheory.TopFlip.StdLoc

theorem stdFst_eq_prodA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j) (ε : AE D), IsIdemSum ε (locPl G t) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ε (X.ideal (locPl G) t)
        (spW G i j) (spX G i j) X.rA.β X.rW.β = prodA B t i j ε (locFst B t X) := by
  intro D T L sc G μ₀ hL B t i j X ε he
  classical
  funext x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst prodA
  by_cases hx : IsHalf ε x
  · simp only [hx, true_and, if_true]
    refine (std_eq_prod _ he (X.c t) _ fun w hw => cpt_frMapO_eq_zero he _ _ _ _ hx hw).trans
      (Finset.prod_congr rfl fun w _ => ?_)
    have hb : (spX G i j).rank = (locGrid G t w).rank (i + 1, j + 1) + (locGrid G t w).rank (i, j) := by
      simpa using Fintype.card_congr ((colX G t i j w).trans (ordX G t i j w))
    rw [locChar_nu hL]
    refine (stdA_eq _ _ (valuation_unifAt_le w) _ (rankW G t i j w) hb _ _ fun r s => ?_).symm
    have h1 := change_eq (finCongr (rankW G t i j w)) (colX G t i j w) (loc w X.rA.β) (loc w (B.β (i + 1) (j + 1)))
      (loc w X.rW.β) (loc w (frX B i j))
      (((x : Matrix (Fin (spX G i j).rank) (Fin (spW G i j).rank) (AE D)).map (toEAf D)).map (cpt (D := D) w))
    have h2 : ∀ (β : GL (Fin (spW G i j).rank) (EAf D)) (γ : GL (Fin (spX G i j).rank) (EAf D)),
        (frMapO (spW G i j) (spX G i j) β γ x).map (cpt (D := D) w) = ((loc w γ)⁻¹).val *
          ((x : Matrix (Fin (spX G i j).rank) (Fin (spW G i j).rank) (AE D)).map (toEAf D)).map (cpt (D := D) w) *
            (loc w β).val := fun β γ => by
      rw [frMapO, Matrix.map_mul, Matrix.map_mul, ← map_inv]
      rfl
    rw [← h2, ← h2] at h1
    have h3 : (chA B t X w).val * linA B t i j w x * (invT (chX B t X w)).val = _ := h1
    rw [h3]
    have h4 : (colX G t i j w).symm ((ordX G t i j w).symm s) = Fin.cast hb.symm s := by
      refine Fin.ext ((ordX_colX_val t i j w _).symm.trans ?_)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl
    simp only [reindex_apply, submatrix_apply, transpose_apply, h4]
    rfl
  · rw [if_neg hx, if_neg fun h => hx h.1]

end GlobalTheory.TopFlip

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairFirstMember_eq_prod_local_gridBases : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j) (ε : AE D), IsIdemSum ε (locPl G t) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ε (X.ideal (locPl G) t)
        (spW G i j) (spX G i j) X.rA.β X.rW.β = prodA B t i j ε (locFst B t X) := by
  atlas_forward_decl GlobalTheory.TopFlip.stdFst_eq_prodA
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.StdSnd

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (unitChar IsUnitDet InId rightBlock dualCoord stdSnd)
open GlobalTheory.StdPairCone (stdB blk₁ blk₂ IsGLO)
open GlobalTheory.LFun (locChar locIdele)
open GlobalTheory.FunObj.Comparison₂ (vEq)

theorem hom_sum {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : ι → R) (s : Finset ι) :
    f (∑ i ∈ s, p i) = ∑ i ∈ s, f (p i) := map_sum f p s

theorem hom_prod {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : ι → R) (s : Finset ι) :
    f (∏ i ∈ s, p i) = ∏ i ∈ s, f (p i) := map_prod f p s

variable {D : D7}

theorem cpt_idemSum {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (Q : Pl D.host.E) :
    (Q ∈ S → cpt (D := D) Q (toEAf D e) = 1) ∧ (Q ∉ S → cpt (D := D) Q (toEAf D e) = 0) := by
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  rw [hsum, hom_sum (toEAf D), hom_sum (cpt (D := D) Q)]
  refine ⟨fun hQ => ?_, fun hQ => ?_⟩
  · rw [Finset.sum_eq_single Q (fun P hP hPQ => (cpt_of_isIdemAt (hes P hP)).2 Q (Ne.symm hPQ)) (fun h => absurd hQ h)]
    exact (cpt_of_isIdemAt (hes Q hQ)).1
  · exact Finset.sum_eq_zero fun P hP => (cpt_of_isIdemAt (hes P hP)).2 Q (fun h => hQ (h ▸ hP))

theorem cpt_prod_locIdele (S : Finset (Pl D.host.E)) (u : ∀ w : S, (Kw (D := D) w.1)ˣ) (Q : Pl D.host.E) :
    (∀ hQ : Q ∈ S, cpt (D := D) Q (toEAf D ((∏ w : S, locIdele D.host.F w.1 (u w) : (AE D)ˣ) : AE D)) = u ⟨Q, hQ⟩) ∧
    (Q ∉ S → cpt (D := D) Q (toEAf D ((∏ w : S, locIdele D.host.F w.1 (u w) : (AE D)ˣ) : AE D)) = 1) := by
  have hloc : ∀ (w : Pl D.host.E) (y : (Kw (D := D) w)ˣ), cpt (D := D) Q (toEAf D (locIdele D.host.F w y : AE D)) =
        (Neutral.B1.finiteSingle D.host.E w (y : Kw (D := D) w)) Q := by
    intro w y
    rw [GlobalTheory.DepthFix.cpt_eq_finAd]
    exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y)
  rw [Units.coe_prod, hom_prod (toEAf D), hom_prod (cpt (D := D) Q)]
  simp only [hloc]
  refine ⟨fun hQ => ?_, fun hQ => ?_⟩
  · rw [Finset.prod_eq_single ⟨Q, hQ⟩]
    · rw [GlobalTheory.LFun.finSingle_self]
    · intro b _ hb
      exact GlobalTheory.LFun.finSingle_ne (fun h => hb (Subtype.ext h.symm)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · exact Finset.prod_eq_one fun w _ => GlobalTheory.LFun.finSingle_ne (fun h => hQ (by rw [h]; exact w.2)) _

theorem infPart_prod_locIdele (S : Finset (Pl D.host.E)) (u : ∀ w : S, (Kw (D := D) w.1)ˣ) :
    infPart D ((∏ w : S, locIdele D.host.F w.1 (u w) : (AE D)ˣ) : AE D) = 1 := by
  rw [Units.coe_prod, hom_prod]
  exact Finset.prod_eq_one fun w _ => GlobalTheory.LFun.infTens_locIdele (F := D.host.F) w.1 _

theorem prod_map_inv {ι M : Type} [Fintype ι] [CommGroup M] {K : ι → Type} [∀ i, Group (K i)] (f : ∀ i, K i →* M)
    (u : ∀ i, K i) : (∏ i, f i (u i))⁻¹ = ∏ i, f i (u i)⁻¹ := by
  simp only [map_inv, Finset.prod_inv_distrib]

theorem char_prod_inv {ι M : Type} [Fintype ι] [CommMonoid M] (ν : M →* Circle) (x : ι → M) :
    (((ν (∏ i, x i))⁻¹ : Circle) : ℂ) = ∏ i, (((Circle.toUnits (ν (x i)))⁻¹ : ℂˣ) : ℂ) := by
  rw [map_prod, ← Finset.prod_inv_distrib]
  refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun w _ => ?_)
  rw [Units.val_inv_eq_inv_val]
  exact Circle.coe_inv _

theorem isUnitDet_prod {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    (N : Matrix (Fin k) (Fin k) (EAf D)) (u : ∀ w : S, (Kw (D := D) w.1)ˣ)
    (hu : ∀ w : S, (u w : Kw (D := D) w.1) = cpt (D := D) w.1 N.det)
    (hv : ∀ w : S, Valued.v (u w : Kw (D := D) w.1) = 1) : IsUnitDet e N (∏ w : S, locIdele D.host.F w.1 (u w)) := by
  refine ⟨infPart_prod_locIdele S u, cpt_ext fun Q => ?_, ?_⟩
  · rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
    by_cases hQ : Q ∈ S
    · rw [(cpt_prod_locIdele S u Q).1 hQ, (cpt_idemSum he Q).1 hQ, hu, sub_self, zero_add, one_mul]
    · rw [(cpt_prod_locIdele S u Q).2 hQ, (cpt_idemSum he Q).2 hQ, sub_zero, zero_mul, add_zero]
  · have e1 : (∏ w : S, locIdele D.host.F w.1 (u w) : (AE D)ˣ)⁻¹ = ∏ w : S, locIdele D.host.F w.1 (u w)⁻¹ :=
      prod_map_inv (fun w : S => locIdele D.host.F w.1) u
    rw [e1]
    refine (mem_OA_iff _).2 fun Q => ?_
    by_cases hQ : Q ∈ S
    · rw [(cpt_prod_locIdele S (fun w => (u w)⁻¹) Q).1 hQ, HeightOneSpectrum.mem_adicCompletionIntegers,
        Units.val_inv_eq_inv_val, map_inv₀, hv ⟨Q, hQ⟩, inv_one]
    · rw [(cpt_prod_locIdele S (fun w => (u w)⁻¹) Q).2 hQ]
      exact one_mem _

theorem isUnitDet_unique {e : AE D} {k : ℕ} {N : Matrix (Fin k) (Fin k) (EAf D)} {x x' : (AE D)ˣ} (h : IsUnitDet e N x)
    (h' : IsUnitDet e N x') : x = x' :=
  Units.ext (ae_ext (h.1.trans h'.1.symm) fun Q => congrArg (cpt (D := D) Q) (h.2.1.trans h'.2.1.symm))

theorem unitChar_eq_prod (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    (N : Matrix (Fin k) (Fin k) (EAf D)) (u : ∀ w : S, (Kw (D := D) w.1)ˣ)
    (hu : ∀ w : S, (u w : Kw (D := D) w.1) = cpt (D := D) w.1 N.det)
    (hv : ∀ w : S, Valued.v (u w : Kw (D := D) w.1) = 1) :
    unitChar ν e N = ∏ w : S, (((locChar ν w.1 (u w))⁻¹ : ℂˣ) : ℂ) := by
  have hx := isUnitDet_prod he N u hu hv
  have hex : ∃ x, IsUnitDet e N x := ⟨_, hx⟩
  unfold unitChar
  rw [dif_pos hex, isUnitDet_unique hex.choose_spec hx]
  exact char_prod_inv ν _

theorem v_det_of_isUnitDet {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {N : Matrix (Fin k) (Fin k) (EAf D)} {x : (AE D)ˣ} (hx : IsUnitDet e N x) {w : Pl D.host.E} (hw : w ∈ S)
    (hN : Valued.v (cpt (D := D) w N.det) ≤ 1) : Valued.v (cpt (D := D) w N.det) = 1 := by
  have h1 : cpt (D := D) w (toEAf D (x : AE D)) = cpt (D := D) w N.det := by
    rw [hx.2.1, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (cpt_idemSum he w).1 hw, sub_self,
      zero_add, one_mul]
  have h2 : Valued.v (cpt (D := D) w (toEAf D ((x⁻¹ : (AE D)ˣ) : AE D))) ≤ 1 := (mem_OA_iff _).1 hx.2.2 w
  have h3 : Valued.v (cpt (D := D) w N.det) * Valued.v (cpt (D := D) w (toEAf D ((x⁻¹ : (AE D)ˣ) : AE D))) = 1 := by
    rw [← h1, ← Valuation.map_mul, ← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one,
      Valuation.map_one]
  refine le_antisymm hN ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
    _ ≤ Valued.v (cpt (D := D) w N.det) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

theorem mem_cball_pow (w : Pl D.host.E) (c : ℕ) (z : Kw (D := D) w) :
    z ∈ cball (unifAt (D := D) w ^ c) ↔ Valued.v z ≤ WithZero.exp (-(c : ℤ)) := by
  have h : Valued.v (unifAt (D := D) w : Kw (D := D) w) = WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  refine (vEq w _ _).trans ?_
  rw [Units.val_pow_eq_pow_val, map_pow, h, ← WithZero.exp_nsmul]
  simp

theorem mem_integer_iff (w : Pl D.host.E) (z : Kw (D := D) w) : z ∈ (ValuativeRel.valuation (Kw (D := D) w)).integer ↔ Valued.v z ≤ 1 := by
  rw [Valuation.mem_integer_iff, (vEq w).le_one_iff_le_one]

theorem inId_prod_iff (S : Finset (Pl D.host.E)) (c : Pl D.host.E → ℕ) {z : EAf D}
    (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    InId (∏ w ∈ S, w.asIdeal ^ c w) z ↔ ∀ w ∈ S, Valued.v (cpt (D := D) w z) ≤ WithZero.exp (-(c w : ℤ)) := by
  have h : (∏ w ∈ S, w.asIdeal ^ c w) = S.inf fun v => v.asIdeal ^ c v :=
    (HeightOneSpectrum.inf_pow_eq_prod S c id fun v _ v' _ hne => hne).symm
  have h0 : (∏ w ∈ S, w.asIdeal ^ c w) ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  generalize (∏ w ∈ S, w.asIdeal ^ c w) = I at h h0
  constructor
  · rintro ⟨h1, h2⟩ w hw
    exact GlobalTheory.FunObj.Comparison₂.v_le_of_mem_idS (s := ⟨z, h1⟩) (h.le.trans (Finset.inf_le hw)) h2
  · intro H
    exact ⟨hz, GlobalTheory.FunObj.Comparison₂.mem_idS_of_v_le (w := fun v => v) (e := c) (S := S) (s := ⟨z, hz⟩) h0 h H⟩

open Classical in

theorem std_eq_prod (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    (c : Pl D.host.E → ℕ) {a a' : ℕ} (Y : Matrix (Fin a') (Fin (a + a')) (EAf D)) (hY : ∀ i j, toEAf D e * Y i j = Y i j) :
    (if IsIntM Y ∧ ∀ i j, j.1 < a → InId (∏ w ∈ S, w.asIdeal ^ c w) (Y i j) then unitChar ν e (rightBlock a Y) else 0) =
      ∏ w ∈ S, stdB (locChar ν w) (unifAt (D := D) w) (c w) a a' (Y.map (cpt (D := D) w)) := by
  have hb : ∀ i j, rightBlock a Y i j = Y i (Fin.natAdd a j) := fun i j => dif_pos (Fin.natAdd a j).2
  have hdet : ∀ w, (blk₂ (Y.map (cpt (D := D) w))).det = cpt (D := D) w (rightBlock a Y).det := fun w => by
    rw [RingHom.map_det]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hb]
    rfl
  by_cases H : ∀ w ∈ S, (blk₂ (Y.map (cpt (D := D) w))).det ≠ 0 ∧ IsGLO (blk₂ (Y.map (cpt (D := D) w))) ∧
      ∀ i j, blk₁ (Y.map (cpt (D := D) w)) i j ∈ cball (unifAt (D := D) w ^ c w)
  · have hint : IsIntM Y := fun i j => (mem_OA_iff _).2 fun Q => by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      by_cases hQ : Q ∈ S
      · refine Fin.addCases (motive := fun j => Valued.v (cpt (D := D) Q (Y i j)) ≤ 1) (fun j => ?_) (fun j => ?_) j
        · refine ((mem_cball_pow Q _ _).1 ((H Q hQ).2.2 i j)).trans ?_
          rw [← WithZero.exp_zero, WithZero.exp_le_exp]
          omega
        · exact (mem_integer_iff Q _).1 ((H Q hQ).2.1.1 i j)
      · rw [← hY, RingHom.map_mul, (cpt_idemSum he Q).2 hQ, zero_mul, Valuation.map_zero]
        exact zero_le_one
    rw [if_pos ⟨hint, fun i j hj => (inId_prod_iff S c (hint i j)).2 fun w hw =>
      (mem_cball_pow w _ _).1 ((H w hw).2.2 i ⟨j.1, hj⟩)⟩,
      unitChar_eq_prod ν he _ (fun w => Units.mk0 _ (H w.1 w.2).1) (fun w => hdet w.1)
        (fun w => (vEq w.1).eq_one_iff_eq_one.1 (H w.1 w.2).2.1.2), ← Finset.prod_coe_sort S]
    refine Finset.prod_congr rfl fun w _ => ?_
    unfold stdB
    rw [dif_pos (H w.1 w.2)]
  · obtain ⟨w, hw⟩ := not_forall.1 H
    obtain ⟨hw, hn⟩ := Classical.not_imp.1 hw
    rw [Finset.prod_eq_zero (f := fun w => stdB (locChar ν w) (unifAt (D := D) w) (c w) a a' (Y.map (cpt (D := D) w))) hw
      (by unfold stdB; exact dif_neg hn)]
    split_ifs with hc
    · unfold unitChar
      refine dif_neg fun ⟨x, hx⟩ => hn ?_
      have hi : ∀ i j, blk₂ (Y.map (cpt (D := D) w)) i j ∈ (ValuativeRel.valuation (Kw (D := D) w)).integer := fun i j =>
        (mem_integer_iff w _).2 ((mem_OA_iff _).1 (hc.1 i _) w)
      have hd : (blk₂ (Y.map (cpt (D := D) w))).det ∈ (ValuativeRel.valuation (Kw (D := D) w)).integer := by
        rw [Matrix.det_apply']
        exact Subring.sum_mem _ fun σ _ => mul_mem (intCast_mem _ _) (Subring.prod_mem _ fun i _ => hi _ _)
      have h1 : Valued.v (blk₂ (Y.map (cpt (D := D) w))).det = 1 := by
        rw [mem_integer_iff, hdet] at hd
        rw [hdet]
        exact v_det_of_isUnitDet he hx hw hd
      refine ⟨fun h0 => ?_, ⟨hi, (vEq w).eq_one_iff_eq_one.2 h1⟩, fun i j => (mem_cball_pow w _ _).2 ?_⟩
      · rw [h0, Valuation.map_zero] at h1
        exact zero_ne_one h1
      · exact (inId_prod_iff S c (hc.1 i _)).1 (hc.2 i (Fin.castAdd a' j) j.2) w hw
    · rfl

open Classical in

theorem std_eq_prod' (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    (c : Pl D.host.E → ℕ) {a a' d : ℕ} (hd : d = a + a') (b b' : Pl D.host.E → ℕ) (hb : ∀ w, a = b w) (hb' : ∀ w, a' = b' w)
    (Y : Matrix (Fin a') (Fin d) (EAf D)) (hY : ∀ i j, toEAf D e * Y i j = Y i j)
    (Z : ∀ w, Matrix (Fin (b' w)) (Fin (b w + b' w)) (Kw (D := D) w))
    (hZ : ∀ w r s, ∃ r' s', r'.1 = r.1 ∧ s'.1 = s.1 ∧ Z w r s = cpt (D := D) w (Y r' s')) :
    (if IsIntM Y ∧ ∀ i j, j.1 < a → InId (∏ w ∈ S, w.asIdeal ^ c w) (Y i j) then unitChar ν e (rightBlock a Y) else 0) =
      ∏ w ∈ S, stdB (locChar ν w) (unifAt (D := D) w) (c w) (b w) (b' w) (Z w) := by
  obtain rfl : b = fun _ => a := funext fun w => (hb w).symm
  obtain rfl : b' = fun _ => a' := funext fun w => (hb' w).symm
  subst hd
  have : ∀ w, Z w = Y.map (cpt (D := D) w) := fun w => Matrix.ext fun r s => by
    obtain ⟨r', s', h1, h2, h3⟩ := hZ w r s
    rw [h3, Fin.ext h1, Fin.ext h2]
    rfl
  simp only [this]
  exact std_eq_prod ν he c Y hY

theorem change_frames {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n d : ℕ} (β β' : GL (Fin n) R) (γ γ' : GL (Fin d) R)
    (M : Matrix (Fin n) (Fin d) R) (ξ : R) (x : K) (hx : f ξ = x) (hξ : x ≠ 0) :
    (Units.map (Matrix.scalar (Fin n)).toMonoidHom (Units.mk0 x hξ) *
        ((GeneralLinearGroup.map f β')⁻¹ * GeneralLinearGroup.map f β)).val *
        ((β⁻¹).val * M * γ.val).map f * ((GeneralLinearGroup.map f γ)⁻¹ * GeneralLinearGroup.map f γ').val =
      (ξ • ((β'⁻¹).val * M * γ'.val)).map f := by
  have hl : ∀ {k : ℕ} (g : GL (Fin k) R), g.val.map f = (GeneralLinearGroup.map f g).val := fun g => rfl
  have hs : (ξ • ((β'⁻¹).val * M * γ'.val)).map f = x • ((β'⁻¹).val * M * γ'.val).map f := Matrix.ext fun r s => by
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, hx]
    rfl
  have hu : (Units.map (Matrix.scalar (Fin n)).toMonoidHom (Units.mk0 x hξ)).val = x • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.smul_one_eq_diagonal]
    rfl
  rw [hs, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hl, hl, hl, hl, map_inv, map_inv]
  generalize GeneralLinearGroup.map f β = b
  generalize GeneralLinearGroup.map f β' = b'
  generalize GeneralLinearGroup.map f γ = g
  generalize GeneralLinearGroup.map f γ' = g'
  generalize M.map f = N
  have h1 : b.val * (b⁻¹).val = 1 := b.mul_inv
  have h2 : g.val * (g⁻¹).val = 1 := g.mul_inv
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hu, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul]
  congr 1
  calc (b'⁻¹).val * b.val * ((b⁻¹).val * N * g.val) * ((g⁻¹).val * g'.val)
      = (b'⁻¹).val * (b.val * (b⁻¹).val) * N * (g.val * (g⁻¹).val) * g'.val := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

theorem locChar_nu {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) :
    locChar (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) w = (locGrid G t w).nu i j := by
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) :=
    mul_div_mul_right_eq_div _ _ _
  rw [e1, GlobalTheory.LFun.locChar_eq_of_chrEq (SqNum.chrEq_nu G t i j hL)]
  have hj : (j : ℕ) < D.R.m := j.2
  ext x
  simp only [SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Formalism.L2.Host.HChar.loc_mul,
    Formalism.L2.Host.HChar.loc_inv, div_eq_mul_inv]
  rfl

theorem val_colX_ordX (t : T) (i j : Fin D.R.m) (w : Pl D.host.E)
    (s : Fin ((locGrid G t w).rank (i + 1, j + 1) + (locGrid G t w).rank (i, j))) :
    ((colX G t i j w).symm ((ordX G t i j w).symm s)).1 = s.1 := by
  have h : ∀ z : (locGrid G t w).Cols i j, ((colX G t i j w).symm z).1 = (finSumFinEquiv z).1 := by
    rintro (z | z)
    · rfl
    · change _ + z.1 = _ + z.1
      rw [rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩]
  rw [h]
  simp [ordX, SplitFlip.stdSplit]

theorem stdSnd_eq_prodB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j) (ε : AE D), IsIdemSum ε (locPl G t) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ε (X.ideal (locPl G) t)
        (spW G i j).rank (spW₁ G i j) (spX G i j) X.rA'.β X.rW.β = prodB B t i j ε (locSnd B t X) := by
  intro D T L sc G μ₀ hL B t i j X ε hε
  classical
  funext y
  unfold stdSnd prodB
  by_cases hy : IsHalf (cA D ε) y
  · rw [if_pos hy]
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    have w₀ : Pl D.host.E := ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩
    have hd : (spX G i j).rank = (spW G i j).rank + (spW₁ G i j).rank := by
      have := Fintype.card_congr ((colX G t i j w₀).trans (ordX G t i j w₀))
      rw [Fintype.card_fin, Fintype.card_fin] at this
      rw [this, rankW G t i j w₀, rankW₁ G t i j w₀]
    have key := std_eq_prod' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) hε (X.c t) hd _ _
      (rankW G t i j) (rankW₁ G t i j) (dualCoord (spW₁ G i j) (spX G i j) X.rA'.β X.rW.β y)
      (fun r s => by
        unfold dualCoord
        rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, GlobalTheory.AdjVecLocal.frMapAdj_half _ _ _ _ hy])
      (fun w => reindex (Equiv.refl _) (ordX G t i j w) ((chB B t X w).val * linB B t i j w y * (chX B t X w).val))
      (fun w r s => ⟨(finCongr (rankW₁ G t i j w)).symm r, _, rfl, val_colX_ordX t i j w s, by
        unfold chB chX linB frMapAdj dualCoord frMapAdj
        rw [GlobalTheory.StepData.reGL_val, GlobalTheory.StepData.reGL_val, Matrix.reindex_apply, Matrix.reindex_apply,
          Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
        exact congrFun (congrFun (change_frames (cpt (D := D) w) (B.β i j) X.rA'.β (frX B i j) X.rW.β _
          (eToEAf D D.host.xi0) (xiAt (D := D) w) (GlobalTheory.FunObj.Comparison₂.cpt_tmul w _) _) _) _⟩)
    refine Eq.trans ?_ (key.trans (Finset.prod_congr rfl fun w _ => ?_))
    · exact @if_congr _ _ _ (_) (_) _ _ _ _ (and_iff_right hy) rfl rfl
    · rw [locChar_nu hL]
      rfl
  · rw [if_neg hy, if_neg fun h => hy h.1]

end GlobalTheory.TopFlip.StdSnd

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairSecondMember_eq_prod_local_gridBases : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j) (ε : AE D), IsIdemSum ε (locPl G t) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ε (X.ideal (locPl G) t)
        (spW G i j).rank (spW₁ G i j) (spX G i j) X.rA'.β X.rW.β = prodB B t i j ε (locSnd B t X) := by
  atlas_forward_decl GlobalTheory.TopFlip.StdSnd.stdSnd_eq_prodB
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.VacRouteBig

open GlobalTheory.RouteSeesaw (box2 topR botR)

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
open GlobalTheory.VacUnique GlobalTheory.FockCompare in

theorem eq_smul_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f f' : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) (hth : IsThetaFunO ψ S T f')
    (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f')
    (hlat' : IsLatVac (heisO ψ S T)
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f') :
    ∃ a : ℂ, f' = a • f := by
  classical
  have hψ := hf.1
  have hθ : IsInfFam θ := hf.2.inf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT hΛS.1 hΛT.1
  have hlat := hf.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat
  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f' hth hfock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hth hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, det f f' a hf.2.theta hth hlat hlat' fun z => (congrFun ha z).symm⟩

theorem adjM_eq (S B : HSp D) (y : WO S B) : GlobalTheory.RouteSeesaw.adjM S B y = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B y := by
  unfold GlobalTheory.RouteSeesaw.adjM GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger
  rw [Matrix.mul_assoc]
  rfl

theorem heisO_adj (ψ : AddChar (AF D.host.F) ℂ) (S B : HSp D) (u : WO S B) (g : WO B S → ℂ) :
    heisO ψ (negSp S) B u (fun y => g (GlobalTheory.RouteSeesaw.adjM S B y)) =
      fun y => heisO ψ B S (GlobalTheory.RouteSeesaw.adjM S B u) g (GlobalTheory.RouteSeesaw.adjM S B y) := by
  funext y
  unfold heisO
  dsimp only
  rw [GlobalTheory.FockConj.symplOH_negSp, GlobalTheory.RouteSeesaw.adjM_add, adjM_eq, adjM_eq, GlobalTheory.AdjointPair.symplOH_dagger]

theorem heisenbergOperator_externalProduct_blocks (ψ : AddChar (AF D.host.F) ℂ) (S A B : HSp D) (φ : WO S A → ℂ) (φ' : WO S B → ℂ)
    (u : WO S (GlobalTheory.Doubling.hsum A B)) :
    heisO ψ S (GlobalTheory.Doubling.hsum A B) u (box2 φ φ') =
      box2 (heisO ψ S A (topR (A := A) (B := B) u) φ) (heisO ψ S B (botR (A := A) (B := B) u) φ') := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.MixModel.OrthDec.heisO_boxT, GlobalTheory.SeesawSumTarget.boxT_sumDec,
    GlobalTheory.MixModel.OrthDec.resT_apply]
  dsimp only
  rw [GlobalTheory.SeesawSumTarget.pA_sumDec, GlobalTheory.SeesawSumTarget.pB_sumDec]

theorem isHalf_adjM (S B : HSp D) {e : AE D} {y : WO S B} (hy : IsHalf e y) :
    IsHalf (cA D e) (GlobalTheory.RouteSeesaw.adjM S B y) := fun a b => by
  have h : ∀ k l, cA D e * cA D (y k l) = cA D (y k l) := fun k l => by rw [← map_mul, hy k l]
  simp only [GlobalTheory.RouteSeesaw.adjM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (incA D (S.gram⁻¹ a l) * incA D (B.gram k b)) * h k l

theorem isLatticeVacuum_externalProduct_adjoint (ψ : AddChar (AF D.host.F) ℂ) (S A B : HSp D) {ΛA : AddSubgroup (WO (negSp S) A)}
    {ΛB : AddSubgroup (WO B S)} {Λ : AddSubgroup (WO (negSp S) (GlobalTheory.Doubling.hsum A B))}
    (hΛ : ∀ u ∈ Λ, topR (A := A) (B := B) u ∈ ΛA ∧ GlobalTheory.RouteSeesaw.adjM S B (botR (A := A) (B := B) u) ∈ ΛB)
    {φ : WO (negSp S) A → ℂ} {g : WO B S → ℂ} (hφ : IsLatVac (heisO ψ (negSp S) A) ΛA φ)
    (hg : IsLatVac (heisO ψ B S) ΛB g) :
    IsLatVac (heisO ψ (negSp S) (GlobalTheory.Doubling.hsum A B)) Λ
      (box2 (S := negSp S) (A := A) (B := B) φ fun y => g (GlobalTheory.RouteSeesaw.adjM S B y)) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have e1 : topR (A := A) (B := B) (2 • u) = 2 • topR (A := A) (B := B) u := rfl
    have e2 : GlobalTheory.RouteSeesaw.adjM S B (botR (A := A) (B := B) (2 • u)) =
        2 • GlobalTheory.RouteSeesaw.adjM S B (botR (A := A) (B := B) u) := by
      rw [two_nsmul, two_nsmul, ← GlobalTheory.RouteSeesaw.adjM_add]
      rfl
    rw [heisenbergOperator_externalProduct_blocks, heisO_adj, e1, e2, hφ.1 _ (hΛ u hu).1, hg.1 _ (hΛ u hu).2]
  · have h1 : IsHalf e (topR (A := A) (B := B) u) := fun a b => hh _ _
    have h2 : IsHalf e (botR (A := A) (B := B) u) := fun a b => hh _ _
    rw [heisenbergOperator_externalProduct_blocks, heisO_adj, hφ.2 e he _ (hΛ u hu).1 h1,
      hg.2 _ (GlobalTheory.PlaceModelSum.isSplitIdem_cA he) _ (hΛ u hu).2 (isHalf_adjM S B h2)]

theorem externalProduct_adjoint_ne_zero (S A B : HSp D) {φ : WO (negSp S) A → ℂ} {g : WO B S → ℂ} {x : WO (negSp S) A} {z : WO B S}
    (hx : φ x ≠ 0) (hz : g z ≠ 0) :
    (box2 (S := negSp S) (A := A) (B := B) φ fun y => g (GlobalTheory.RouteSeesaw.adjM S B y)) ≠ 0 := fun h0 => by
  let d := GlobalTheory.BiTransfer.sumDec A B
  have h := congrFun h0 ((d.resT (negSp S)).symm (x, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger B S z))
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec] at h
  unfold GlobalTheory.MixModel.OrthDec.boxT at h
  rw [AddEquiv.apply_symm_apply] at h
  dsimp only at h
  rw [adjM_eq, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger] at h
  exact mul_ne_zero hx hz h

theorem vac_eq_smul_vacA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ (fun _ => True) : Set _) = orderingsOnSpW G i j →
      ∀ f, IsVacO W.ψ W.θ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (fun τ => -W.cart (.grid (i + 1) (j + 1)) τ) (frSum AV AV₁).cart
        (G.Λ (.grid (i + 1) (j + 1))) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacA ρ i j := by
  intro D T L sc G μ₀ hL W ρ i j AV AV₁ hV hV₁ Λ hΛ hlat f hf
  have hX : (Node.grid (i + 1) (j + 1)).InRange D.R.m := ⟨i.2, j.2⟩
  obtain ⟨A, hA⟩ := exists_isGridFr W hX
  have u₁ := ρ.vX_is i (j + 1) i.2 j.2
  have u₂ := ρ.vT_is μ₀ (i + 1) j i.2 j.2
  have v₁ := u₁.2
  have v₂ := u₂.2
  have cA : (GlobalTheory.SquareComm.frSgn true A).cart = fun τ => -W.cart (.grid (↑i + 1) (↑j + 1)) τ := funext fun τ =>
    (GlobalTheory.PairLift.cart_frSgn true A τ).trans (congrArg Neg.neg (hA τ).2)
  have cA' : A.cart = W.cart _ := funext fun τ => (hA τ).2
  have cV : AV.cart = W.cart _ := funext fun τ => (hV τ).2
  have cV₁ : AV₁.cart = W.cart _ := funext fun τ => (hV₁ τ).2
  have w₁ : IsVacF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV (ρ.vX i (j + 1)) := ⟨v₁.theta, fun τ => by
    rw [cA, cV]
    exact v₁.fock τ⟩
  have w₂ : IsVacF W.ψ W.θ AV₁ A (ρ.vT (i + 1) j) := ⟨v₂.theta, fun τ => by
    rw [cA', cV₁]
    exact v₂.fock τ⟩
  have w₃ := (GlobalTheory.SquareAlg.adj_ptF W.ψ_std W.θ_is A AV₁ w₂).1
  have hv := GlobalTheory.SquareAlg.isVacF_boxT (GlobalTheory.BiTransfer.sumDec _ _) (GlobalTheory.SquareComm.frSgn true A) (GlobalTheory.SquareComm.frSum AV AV₁) AV AV₁
    W.ψ_std W.θ_is (GlobalTheory.SquareAlg.qA_cart_frSum AV AV₁) (GlobalTheory.SquareAlg.qB_cart_frSum AV AV₁) w₁ w₃
  rw [GlobalTheory.SeesawSumTarget.boxT_sumDec] at hv
  have hfock := hv.2
  rw [cA] at hfock
  have hl : IsLatVac (heisO W.ψ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j))
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ fun _ => True) (vacA ρ i j) :=
    isLatticeVacuum_externalProduct_adjoint W.ψ (spW G i j) (spV G i j) (spV₁ G i j) (fun u hu => hlat.le hu) v₁.lat v₂.lat
  obtain ⟨a, ha⟩ := eq_smul_of_vac (S := GlobalTheory.Grid.neg (spW G i j)) (T := spX G i j) (f' := vacA ρ i j)
    (fun τ => isCartanInv_neg (W.cart_is _ hX τ)) (fun τ => GlobalTheory.CompactFockAction.cart_isCartanInv (frSum AV AV₁) τ)
    (isSelfDualC_neg (node_isV G hL hX).sd) hΛ hf hv.1 hfock hl
  obtain ⟨x, hx⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO u₁
  obtain ⟨z, hz⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO u₂
  have hne : vacA ρ i j ≠ 0 := externalProduct_adjoint_ne_zero (spW G i j) (spV G i j) (spV₁ G i j) hx hz
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (by rw [ha, zero_smul])
  exact ⟨a⁻¹, inv_ne_zero ha0, by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

end GlobalTheory.TopFlip.VacRouteBig

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitVacuum_eq_smul_arrowVacua_product : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ (fun _ => True) : Set _) = orderingsOnSpW G i j →
      ∀ f, IsVacO W.ψ W.θ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (fun τ => -W.cart (.grid (i + 1) (j + 1)) τ) (frSum AV AV₁).cart
        (G.Λ (.grid (i + 1) (j + 1))) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacA ρ i j := by
  atlas_forward_decl GlobalTheory.TopFlip.VacRouteBig.vac_eq_smul_vacA
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlipVacB

open GlobalTheory.RouteSeesaw GlobalTheory.SquareDict.AlgSmall GlobalTheory.PairLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heis_rd (hψ : IsStdChar D ψ (-1)) (S V : HSp D) (w : WO S V) (g : WO (negSp V) S → ℂ) :
    heisO ψ S V w (rd S V g) = rd S V (heisO ψ (negSp V) S (adjO (negSp V) S w) g) := by
  rw [rd_eq, GlobalTheory.CjNeg.heis_negT' hψ, GlobalTheory.AdjLawPf.adj_heis ψ hψ.1.2.1, ← rd_eq]

theorem heisenbergOperator_externalProductOnHermitianSum (S A B : HSp D) (u : WO S (GlobalTheory.Doubling.hsum A B)) (f : WO S A → ℂ) (g : WO S B → ℂ) :
    heisO ψ S (GlobalTheory.Doubling.hsum A B) u (box2 f g) =
      box2 (heisO ψ S A (topR (A := A) (B := B) u) f) (heisO ψ S B (botR (A := A) (B := B) u) g) := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.MixModel.OrthDec.heisO_boxT, GlobalTheory.SeesawSumTarget.boxT_sumDec,
    GlobalTheory.MixModel.OrthDec.resT_apply, GlobalTheory.SeesawSumTarget.pA_sumDec, GlobalTheory.SeesawSumTarget.pB_sumDec]

theorem externalProduct_latticeVacua_adjoint_isLatticeVacuum (hψ : IsStdChar D ψ (-1)) {S A B : HSp D} {Λ : AddSubgroup (WO S (GlobalTheory.Doubling.hsum A B))}
    {ΛA : AddSubgroup (WO S A)} {ΛB : AddSubgroup (WO (negSp B) S)}
    (h : ∀ u ∈ Λ, topR (A := A) (B := B) u ∈ ΛA ∧ adjO (negSp B) S (botR (A := A) (B := B) u) ∈ ΛB)
    {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : IsLatVac (heisO ψ S A) ΛA f)
    (hg : IsLatVac (heisO ψ (negSp B) S) ΛB g) :
    IsLatVac (heisO ψ S (GlobalTheory.Doubling.hsum A B)) Λ (box2 f (rd S B g)) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have e1 : topR (A := A) (B := B) (2 • u) = 2 • topR (A := A) (B := B) u := rfl
    have e2 : adjO (negSp B) S (botR (A := A) (B := B) (2 • u)) = 2 • adjO (negSp B) S (botR (A := A) (B := B) u) := by
      have e3 : botR (A := A) (B := B) (2 • u) = botR (A := A) (B := B) u + botR (A := A) (B := B) u := by
        rw [two_nsmul]; rfl
      rw [e3, two_nsmul]
      exact GlobalTheory.AdjLawPf.adj_add (negSp B) S _ _
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, e1, e2, hf.1 _ (h u hu).1, hg.1 _ (h u hu).2]
  · have h1 : IsHalf e (topR (A := A) (B := B) u) := fun a b => hh _ _
    have h2 : IsHalf e (botR (A := A) (B := B) u) := fun a b => hh _ _
    have he' : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, hf.2 e he _ (h u hu).1 h1,
      hg.2 _ he' _ (h u hu).2 (GlobalTheory.AdjLawPf.adj_half (negSp B) S e _ h2)]

theorem vac_ne_zero {θ : InfFam D} {S T : HSp D} {sS sT LS LT} {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) :
    f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 (0 : WO S T → ℂ) = 1 := hn p hp
  simp [nrm2] at n1

theorem externalProduct_readThroughAdjoint_ne_zero {S A B : HSp D} {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : f ≠ 0) (hg : g ≠ 0) :
    box2 f (rd S B g) ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hf
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
  intro h0
  have := congrFun h0 (((GlobalTheory.BiTransfer.sumDec A B).resT S).symm (x, adjO S (negSp B) y))
  simp only [GlobalTheory.MixModel.OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.zero_apply, rd] at this
  erw [GlobalTheory.AdjLawPf.adj_invol] at this
  exact mul_ne_zero hx hy this

theorem vac_eq_smul_vacB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j →
      ∀ f, IsVacO W.ψ W.θ (spW₁ G i j) (spX G i j) (W.cart (.grid i j)) (frSum AV AV₁).cart
        (G.Λ (.grid i j)) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacB ρ i j := by
  intro D T L sc G μ₀ hL W ρ i j AV AV₁ hV hV₁ Λ hΛ hlat f hf
  obtain ⟨A₁, h₁⟩ := exists_isGridFr W (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩
  have v1 := ρ.vT_is μ₀ i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have c₁ : A₁.cart = W.cart _ := funext fun s => (h₁ s).2
  have cV : AV.cart = W.cart _ := funext fun s => (hV s).2
  have cV₁ : (negFr AV₁).cart = fun s => -W.cart (.grid (i + 1) j) s := funext fun s => by rw [negFr_cart, (hV₁ s).2]
  have w1 : IsVacF W.ψ W.θ A₁ AV (ρ.vT i j) := ⟨v1.2.theta, fun s => by rw [c₁, cV]; exact v1.2.fock s⟩
  have w2 : IsVacF W.ψ W.θ (negFr AV₁) A₁ (ρ.vX i j) := ⟨v2.2.theta, fun s => by rw [c₁, cV₁]; exact v2.2.fock s⟩
  have key := fockVacuum_externalProductOnHermitianSum AV AV₁ W.ψ_std W.θ_is A₁ w1 (rd_vac W.ψ_std W.θ_is A₁ AV₁ w2)
  have e : vacB ρ i j = box2 (ρ.vT i j) (rd (spW₁ G i j) (spV₁ G i j) (ρ.vX i j)) := rfl
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have hl : IsLatVac (heisO W.ψ (spW₁ G i j) (spX G i j))
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ fun _ => True) (vacB ρ i j) := by
    rw [e]
    refine externalProduct_latticeVacua_adjoint_isLatticeVacuum W.ψ_std (fun u hu => ?_) v1.2.lat v2.2.lat
    have hu' : u ∈ orderingsOnSpWOne G i j := by rw [← hlat]; exact hu
    exact hu'
  obtain ⟨a, ha⟩ := GlobalTheory.LevelSeries.eq_smul_vacuum W.ψ_std W.θ_is (W.cart_is (.grid i j) ⟨i.2.le, j.2.le⟩)
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv (frSum AV AV₁)) s0 hΛ hf (f' := vacB ρ i j) key.1 hl
    (fun s => by have := key.2 s; rw [c₁] at this; exact this)
  have hne : vacB ρ i j ≠ 0 := by rw [e]; exact externalProduct_readThroughAdjoint_ne_zero (vac_ne_zero v1) (vac_ne_zero v2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (by rw [ha, zero_smul])
  exact ⟨a⁻¹, inv_ne_zero ha0, by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

end GlobalTheory.TopFlipVacB

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitVacuum_eq_smul_product_arrow_vacua : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j →
      ∀ f, IsVacO W.ψ W.θ (spW₁ G i j) (spX G i j) (W.cart (.grid i j)) (frSum AV AV₁).cart
        (G.Λ (.grid i j)) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacB ρ i j := by
  atlas_forward_decl GlobalTheory.TopFlipVacB.vac_eq_smul_vacB
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7}

theorem om_fockF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {ε : Bool} {M X : HSp D} (A : Fr M) (B : Fr X)
    {χ χ' : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep M X} (hω : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω) {h : GA D X} (hh : h ∈ GfC X)
    {f : WO M X → ℂ} (hf : IsFinF ψ θ ε A B f) (c : ℂ) (P) :
    fockF ψ θ ε A B (c • ω (1, h) f) P = c • ω (1, h) (fockF ψ θ ε A B f P) := by
  have e : ω.toSgn ε (1, h) = ω (1, h) := by simp [GlobalTheory.Grid.WRep.toSgn]
  have h1 := GlobalTheory.FiniteFock.compAt_mt_of_finite θ (S := GlobalTheory.Grid.sgn ε M) (hk := one_mem _)
  have h2 := GlobalTheory.FiniteFock.compAt_mt_of_finite θ (hk := hh)
  have := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ _ X χ χ' _ hω hθ (frSgn ε A).cart _ A.onb _ B.cart _ B.onb _ 1 h
    (fun τ => by rw [h1, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h1, Matrix.one_mul]) (fun τ => by rw [h2, Matrix.one_mul]) f hf.1 P).2
  rw [e] at this
  exact (GlobalTheory.FiniteFock.pureTensorO_smul _ _ _ _ _ _ _ _ _ _ _).trans (congrArg (c • ·) this.symm)

theorem om_compare {ψ : AddChar (AF D.host.F) ℂ} {S X : HSp D} {χ χ' χ₁ χ₁' : (AE D)ˣ →* Circle} {ω ω₁}
    (hω : IsWeilDatumO ψ S X χ χ' ω) (hω₁ : IsWeilDatumO ψ S X χ₁ χ₁' ω₁) {h : GA D X} {y : (AE D)ˣ} (hy : IsDetRoot X h y)
    {f} (hf : IsThetaFunO ψ S X f) : ω₁ (1, h) f = ((χ₁ y : ℂ) * (χ y : ℂ)⁻¹) • ω (1, h) f := by
  rw [GlobalTheory.WeilChange.weilData_differ_by_splitFac D ψ S X χ χ' χ₁ χ₁' ω ω₁ hω hω₁ 1 h 1 y (by simp [IsDetRoot]) hy f hf]
  simp [splitFacO]

theorem thetaAt_move {ψ : AddChar (AF D.host.F) ℂ} {S X : HSp D} {χ χ' : (AE D)ˣ →* Circle} {ω}
    (hω : IsWeilDatumO ψ S X χ χ' ω) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)} (hS : Submodule.IsLattice D.host.E ΛS) (hX : Submodule.IsLattice D.host.E ΛX)
    {a : AE D} (ha : a * a = a) (hc : a * cA D a = 0) (hinf : infPart D a = 0) {b b' Φ f : WO S X → ℂ} (hb : IsThetaFunO ψ S X b)
    {h : GA D X} (hfx : ∀ x : WO S X, IsHalf a x ∨ IsHalf (cA D a) x → actO S X 1 h x = x) {c : ℂ} (hc0 : c ≠ 0)
    (e : ω (1, h) b = c • b')
    (hf : IsThetaAt ψ (symplO S X) (heisO ψ S X) a (latO S X ΛS ΛX fun _ => True) 1 b Φ f) :
    IsThetaAt ψ (symplO S X) (heisO ψ S X) a (latO S X ΛS ΛX fun _ => True) 1 b' Φ (c⁻¹ • ω (1, h) f) := by
  have := GlobalTheory.ThetaBaseMove.isThetaAt_move hω
    (fun f₀ h₀ Tm hTm Ψ hΨ => GlobalTheory.DiagLiftFix.isTheta_placeModel hω.std hS hX ha hc hinf h₀ Tm hTm Ψ hΨ) hb 1 h
    (inv_ne_zero hc0) hfx hf
  rwa [e, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

set_option maxHeartbeats 1000000 in

theorem exists_move (hL : L.Is μ₀) (hst : ∀ t, SquareStanding G t) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) {i j : Fin D.R.m}
    {X : TriG G i j} (hX : TopGrid W i j X) {νH}
    (hI : X.Is W.ψ W.θ (fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) νH (locPl G))
    {AV : Fr (spV G i j)} {AV₁ : Fr (spV₁ G i j)} (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁) :
    ∃ h ∈ GfC (spX G i j), ∃ (cA cB : ℂ) (y : (AE D)ˣ), cA ≠ 0 ∧ cB ≠ 0 ∧ ∀ t,
      IsLinA B t i j ρ (X.e t) (locFst B t X) (cA⁻¹ • X.ω t (1, h) (X.f t)) ∧
      IsLinB B t i j ρ (X.e t) (locSnd B t X) ((cB * (L.xi t y : ℂ))⁻¹ • X.ω' t (1, h) (X.f' t)) := by
  obtain ⟨h, hh, Λ, hΛ, hfx, hmv, tA, tB⟩ := GlobalTheory.T.exists_finiteUnitary_selfDual_lattice_grid_doubling (G := G) hL i j
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hX
  have x7 := x6 AV AV₁ hV hV₁
  have sW := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  have sW₁ := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  have sX : IsSelfDualC (spX G i j) (latX G i j) := by have := hI.rigW.1; rwa [x3] at this
  have vA := hI.isVac
  have vB := hI.isVac'
  rw [x1, x3, x4, x7] at vA
  rw [x2, x3, x5, x7] at vB
  have eA : ∀ t, (X.ω t).toSgn true (1, h) = X.ω t (1, h) := fun t => by simp [GlobalTheory.Grid.WRep.toSgn]
  have h2 := GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ (hk := hh)
  have mA := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (hI.weil μ₀) W.θ_is _ _ _ _ _ _ _ _ 1 h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul]) (hmv _ _ (isSelfDualC_neg sW)) _ vA
  have mB := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (hI.weil' μ₀) W.θ_is _ _ _ _ _ _ _ _ 1 h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul]) (hmv _ _ sW₁) _ vB
  obtain ⟨cA', hcA, kA⟩ := GlobalTheory.T.unitVacuum_eq_smul_arrowVacua_product hL W ρ i j AV AV₁ hV hV₁ Λ hΛ tA _ mA
  obtain ⟨cB, hcB, kB⟩ := GlobalTheory.T.unitVacuum_eq_smul_product_arrow_vacua hL W ρ i j AV AV₁ hV hV₁ Λ hΛ tB _ mB
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ h
  refine ⟨h, hh, cA', cB * (L.xi μ₀ y : ℂ)⁻¹, y, hcA, mul_ne_zero hcB (inv_ne_zero (Circle.coe_ne_zero _)), fun t => ⟨?_, ?_⟩⟩
  · have he := hI.idem t
    have f1 := hI.fst t
    rw [x1, x3, GlobalTheory.T.standardPairFirstMember_eq_prod_local_gridBases hL B t i j X _ he] at f1
    have k : (X.ω t).toSgn true (1, h) X.vac = cA' • vacA ρ i j := by
      rw [om_compare (hI.weil μ₀) (hI.weil t) hy vA.2.theta, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_smul, kA]
    have := thetaAt_move (hI.weil t) sW.1 sX.1 (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2 (GlobalTheory.PlaceVec.idemSum_infPart he)
      vA.2.theta (hfx t (hst t) _ he _) hcA k f1
    rwa [eA] at this
  · have he := hI.idem t
    have f1 := hI.snd t
    rw [x2, x3, GlobalTheory.T.standardPairSecondMember_eq_prod_local_gridBases hL B t i j X _ he] at f1
    have k : X.ω' t (1, h) X.vac' = (cB * (L.xi μ₀ y : ℂ)⁻¹ * (L.xi t y : ℂ)) • vacB ρ i j := by
      refine (om_compare (hI.weil' μ₀) (hI.weil' t) hy vB.2.theta).trans ?_
      rw [kB, smul_smul]
      congr 1
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha, LevCh.mu, Lift.tup, MonoidHom.mul_apply, Circle.coe_mul]
      field_simp
    exact thetaAt_move (S := spW₁ G i j) (hI.weil' t) sW₁.1 sX.1 (by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he])
      (by rw [← map_mul, he.2, map_zero]) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he))
      vB.2.theta (fun x hx => hfx t (hst t) _ he _ x (by rwa [GlobalTheory.LatVac.cA_cA, or_comm] at hx))
      (mul_ne_zero (mul_ne_zero hcB (inv_ne_zero (Circle.coe_ne_zero _))) (Circle.coe_ne_zero _)) k f1

end GlobalTheory.TopFlip

end
end
