import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySecond
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInertLocalDatumAtInertPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDoubleCosetOperatorEqInertHeckeOperator
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalMemUnitaryGroupAntidiagonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalStdLatticeStabilizerMemMaxCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertDatumLocalEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalInjectiveOnTrivOutside
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalMemUnitaryGroupAntidiagonalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalStdLatticeStabilizerMemMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertDatumLocalEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalInjectiveOnTrivOutsideStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeEqZpowStdInertCompletion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertEigSat

theorem exists_den {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [Fintype ι] (v : Valuation K Γ)
    (x : ι → K) : ∃ N : K, N ≠ 0 ∧ ∀ i, v (N * x i) ≤ 1 := by
  classical
  have h : ∀ i, ∃ N : K, N ≠ 0 ∧ v N ≤ 1 ∧ v (N * x i) ≤ 1 := fun i => by
    by_cases hx : v (x i) ≤ 1
    · exact ⟨1, one_ne_zero, by simp, by simpa using hx⟩
    · have h0 : x i ≠ 0 := fun e => hx (by simp [e])
      refine ⟨(x i)⁻¹, inv_ne_zero h0, ?_, by simp [h0]⟩
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (not_le.1 hx).le
  choose N h0 h1 h2 using h
  refine ⟨∏ i, N i, Finset.prod_ne_zero_iff.2 fun i _ => h0 i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc, map_mul, map_prod]
  exact mul_le_one' (Finset.prod_le_one' fun j _ => h1 j) (h2 i)

theorem val_mulVec_le {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] {n : ℕ} (v : Valuation K Γ)
    {A : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, v (A i j) ≤ 1) {y : Fin n → K} (hy : ∀ i, v (y i) ≤ 1) (i : Fin n) :
    v ((A *ᵥ y) i) ≤ 1 := by
  show v (∑ j, A i j * y j) ≤ 1
  refine v.map_sum_le fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (hA i j) (hy j)

theorem exists_scalar {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    {σ : w.adicCompletion E →+* w.adicCompletion E} {ϖ : w.adicCompletion E} {q n : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q)
    (g : GL (Fin n) (w.adicCompletion E))
    (hg : ∀ U : GL (Fin n) (w.adicCompletion E), U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) →
      (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ i j, Valued.v ((g * U * g⁻¹).1 i j) ≤ 1) :
    ∃ c : w.adicCompletion E, c ≠ 0 ∧ ∀ z : Fin n → w.adicCompletion E,
      (∀ i, Valued.v (z i) ≤ 1) ↔ ∀ i, Valued.v ((g.1 *ᵥ (c • z)) i) ≤ 1 := by
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := fun e => by rw [e, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  let L : AddSubgroup (Fin n → w.adicCompletion E) :=
    { carrier := {y | ∀ i, Valued.v ((g.1 *ᵥ y) i) ≤ 1}
      add_mem' := fun {a b} ha hb i => by
        rw [Matrix.mulVec_add]
        exact (Valued.v.map_add _ _).trans (max_le (ha i) (hb i))
      zero_mem' := fun i => by simp
      neg_mem' := fun {a} ha i => by
        rw [Matrix.mulVec_neg, Pi.neg_apply, Valuation.map_neg]
        exact ha i }
  have hL : ∀ y, y ∈ L ↔ ∀ i, Valued.v ((g.1 *ᵥ y) i) ≤ 1 := fun _ => Iff.rfl
  obtain ⟨N, hN0, hN⟩ := exists_den (Valued.v : Valuation (w.adicCompletion E) _)
    (fun p : (Fin n × Fin n) ⊕ (Fin n × Fin n) => Sum.elim (fun a => g.1 a.1 a.2) (fun a => (g⁻¹).1 a.1 a.2) p)
  obtain ⟨x, hx1, hx2⟩ := hU.2.2.2.2.1
  obtain ⟨k, hk⟩ := GlobalTheory.T.stable_lattice_eq_zpow_std_inert_completion E w σ hU.1 hU.2.1 ⟨x, hx1, hx2⟩ ϖ hϖ n L N hN0
    (fun a ha y hy => (hL _).2 fun i => by
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_one' ha (hy i))
    (fun y hy => (hL _).2 fun i => by
      rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec]
      exact val_mulVec_le _ (fun a b => hN (Sum.inl (a, b))) hy i)
    (fun y hy i => by
      have e : N * y i = ((N • (g⁻¹).1) *ᵥ (g.1 *ᵥ y)) i := by
        rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        rfl
      rw [e]
      exact val_mulVec_le _ (fun a b => hN (Sum.inr (a, b))) hy i)
    (fun U hU1 i1 i2 y hy => (hL _).2 fun i => by
      have e : g.1 *ᵥ (U.1 *ᵥ y) = (g * U * g⁻¹).1 *ᵥ (g.1 *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
      rw [e]
      exact val_mulVec_le _ (hg U hU1 i1 i2) hy i)
  refine ⟨ϖ ^ (-k), zpow_ne_zero _ h0, fun z => ?_⟩
  rw [← hL, hk]
  refine forall_congr' fun i => ?_
  rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, one_mul]

theorem exists_datum {E : Type} [Field E] [NumberField E] [IsCMField E] (F : Subfield E)
    (hF : F = maximalRealSubfield E) (σ : E →ₐ[F] E) (hσ : ∀ x, σ x = IsCMField.complexConj E x) (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E (w.under (𝓞 F)) w)
    (τ : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E)
    (hU : Formalism.UG.IsUnramInv ϖ τ (Formalism.UG.qV F (w.under (𝓞 F))))
    (hc : GlobalTheory.LFun.IsConjAt σ (rfl : w.under (𝓞 F) = _) τ) :
    ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (Dv : InertDatum E n v w), NG.OverPl w v ∧
      Dv.σw = τ ∧ Dv.ϖ = ϖ ∧ Formalism.UG.qV (maximalRealSubfield E) v = Formalism.UG.qV F (w.under (𝓞 F)) ∧
      (∀ z, Dv.e (ReciprocityTheory.Aut.compAt E v (Formalism.IndefR.principalLevelFrame.tensCastR hF z)) = GlobalTheory.LFun.compAt F w z) ∧
      ∀ M : Matrix (Fin n) (Fin n) (AL E), (∀ u, u ∉ ({v} : Set _) → M.map (ReciprocityTheory.Aut.compAt E u) = 1) ↔
        ∀ u, u ≠ w.under (𝓞 F) → (M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm).map
          (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E)).toRingHom = 1 := by
  subst hF
  obtain rfl : σ = (IsCMField.complexConj E).toAlgHom := AlgHom.ext hσ
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have hunder : w.under (𝓞 (maximalRealSubfield E)) = v := rfl
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov E w = Formalism.UG.intL (w.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield E) E
    (v.adicCompletion (maximalRealSubfield E))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  have hcomp : ∀ u z, (Algebra.TensorProduct.comm (maximalRealSubfield E) E (u.adicCompletion (maximalRealSubfield E)))
      (ReciprocityTheory.Aut.compAt E u (Formalism.IndefR.principalLevelFrame.tensCastR (rfl : maximalRealSubfield E = _) z)) =
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV (maximalRealSubfield E) u) (AlgHom.id _ E)) z := by
    intro u z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨v, ⟨e, τ, ϖ, k, ?_, hU, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, fun z => ?_, fun M => ?_⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj E).toAlgHom _ x)) =
      τ (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke
  · show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ _) = _
    rw [hcomp]
    exact (GlobalTheory.LFun.finAdEquiv_apply hunder z).symm
  · refine forall_congr' fun u => imp_congr Iff.rfl ?_
    let c := (Algebra.TensorProduct.comm (maximalRealSubfield E) E (u.adicCompletion (maximalRealSubfield E))).toRingEquiv
    have e1 : (M.map (Formalism.IndefR.principalLevelFrame.tensCastR (rfl : maximalRealSubfield E = _)).symm).map
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV (maximalRealSubfield E) u) (AlgHom.id _ E)).toRingHom =
        c.mapMatrix (M.map (ReciprocityTheory.Aut.compAt E u)) := by
      ext i j
      have := hcomp u ((Formalism.IndefR.principalLevelFrame.tensCastR (rfl : maximalRealSubfield E = _)).symm (M i j))
      rw [RingEquiv.apply_symm_apply] at this
      exact this.symm
    rw [e1]
    exact (map_eq_one_iff c.mapMatrix c.mapMatrix.injective).symm

theorem sum_reps_eq {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    {a : GAf L n} (ha : TrivOutside {v} a) {R : Finset (GAf L n)}
    (hR : GlobalTheory.SphLabelOps.Reps (GlobalTheory.InertSph.Kv L n v) a R) (W : Type) [AddCommGroup W] [Module ℂ W]
    (φ : GAf L n → W) (hφ : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) :
    ∑ γ ∈ R, NG.rt L n γ φ = heckeFunI L n (Umax L n) Dv
      (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv a⟩) φ := by
  classical
  have h1 := GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv
  have h2 := GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv
  have h3 := GlobalTheory.T.exists_trivOutside_inertDatum_local_eq L n v w Dv
  have h4 := GlobalTheory.T.inertDatum_local_injective_on_trivOutside L n v w Dv
  set K := InertSph.Kv L n v
  have tR : ∀ γ ∈ R, TrivOutside {v} γ := by
    intro γ hγ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR.1 γ hγ
    exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 ha) hk₂.2
  have hv1 : ∀ x : GAf L n, TrivOutside {v} x → (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂) →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc x) = 1 := by
    intro x hx hp
    unfold Formalism.AUTREP.InertDatum.hval
    rw [dif_pos (h1 x)]
    exact Formalism.UG.P.dosetInd_of_mem ℂ _ _ _ ((GlobalTheory.InertDCOp.mem_dc_iff Dv h1 h2 h3 h4 ha hx).2 hp)
  have hv0 : ∀ x : GAf L n, TrivOutside {v} x →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc x) ≠ 0 →
      ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂ := by
    intro x hx h0
    unfold Formalism.AUTREP.InertDatum.hval at h0
    rw [dif_pos (h1 x)] at h0
    refine (GlobalTheory.InertDCOp.mem_dc_iff Dv h1 h2 h3 h4 ha hx).1 ?_
    by_contra hn
    exact h0 (Formalism.UG.P.dosetInd_of_not_mem ℂ _ _ _ hn)
  funext g
  rw [Finset.sum_apply]
  unfold heckeFunI
  rw [finsum_eq_sum_of_support_subset (s := R.image (QuotientGroup.mk : GAf L n → GAf L n ⧸ Umax L n))]
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun γ hγ => ?_
      have hc : ∃ x : GAf L n, (x : GAf L n ⧸ Umax L n) = (γ : GAf L n ⧸ Umax L n) ∧ TrivOutside {v} x :=
        ⟨γ, rfl, tR γ hγ⟩
      rw [dif_pos hc]
      obtain ⟨e, hxt⟩ := hc.choose_spec
      have hU : γ⁻¹ * hc.choose ∈ Umax L n := QuotientGroup.eq.1 e.symm
      have hT : TrivOutside {v} (γ⁻¹ * hc.choose) :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tR γ hγ)) hxt
      have hp : ∃ k₁ ∈ K, ∃ k₂ ∈ K, hc.choose = k₁ * a * k₂ := by
        obtain ⟨k₁, hk₁, k₂, hk₂, e'⟩ := hR.1 γ hγ
        exact ⟨k₁, hk₁, k₂ * (γ⁻¹ * hc.choose), mul_mem hk₂ ⟨hU, hT⟩, by rw [← mul_assoc, ← e']; group⟩
      rw [hv1 _ hxt hp, one_smul]
      have := congrFun (hφ _ hU hT) (g * γ)
      show φ (g * γ) = φ (g * hc.choose)
      rw [← this]
      show φ (g * γ * (γ⁻¹ * hc.choose)) = φ (g * hc.choose)
      group
    · intro γ hγ γ' hγ' e
      have hU : γ⁻¹ * γ' ∈ Umax L n := QuotientGroup.eq.1 e
      have hT : TrivOutside {v} (γ⁻¹ * γ') :=
        GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv (tR γ hγ)) (tR γ' hγ')
      exact (hR.2 γ' (hR.1 γ' hγ')).unique ⟨hγ, hU, hT⟩ ⟨hγ', by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc0
    rw [Function.mem_support] at hc0
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ Umax L n) = c ∧ TrivOutside {v} x
    · rw [dif_pos hc] at hc0
      obtain ⟨e, hxt⟩ := hc.choose_spec
      have h0 : Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) ⟨Dv.loc a, h1 a⟩) (Dv.loc hc.choose) ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hc0; exact hc0 rfl
      obtain ⟨γ, ⟨hγ, hγx⟩, -⟩ := hR.2 _ (hv0 _ hxt h0)
      rw [Finset.coe_image]
      refine ⟨γ, hγ, ?_⟩
      show (γ : GAf L n ⧸ Umax L n) = c
      rw [← e]
      exact QuotientGroup.eq.2 hγx.1
    · exact absurd (dif_neg hc) hc0

section Frame

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

set_option maxHeartbeats 2000000 in

theorem triv_iff {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {PV : principalLevelFrame.RowPsi V n}
    (hs : GlobalTheory.NJoin.StdFrame hF PV) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    {v₀ : HeightOneSpectrum (𝓞 D.host.F)}
    (hsupp : ∀ M : Matrix (Fin n) (Fin n) (AL D.host.E),
      (∀ u, u ∉ ({v} : Set _) → M.map (ReciprocityTheory.Aut.compAt D.host.E u) = 1) ↔
        ∀ u, u ≠ v₀ → (M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm).map
          (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u) (AlgHom.id D.host.F D.host.E)).toRingHom = 1)
    (κ : GAf D.host.E n) : TrivOutside {v} κ ↔ PV.ψ κ ∈ (emb D.sp.cm.sig V.gram v₀).range := by
  obtain ⟨⟨β, β', hb1, hb2, hK⟩, -⟩ := hs
  rw [range_emb, mem_atPts]
  refine (hsupp κ.1.1).trans (Iff.trans ?_ (and_iff_right (PV.into κ)).symm)
  refine forall_congr' fun u => imp_congr (by simp) ?_
  set φ := (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e1 : (matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram u (PV.ψ κ))).1 =
      (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (PV.ψ κ)).map φ := by
    rw [← projFinLoc_projFin]
    rfl
  have e2 : proj D.sp.cm.sig V.gram u (PV.ψ κ) = 1 ↔
      (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (PV.ψ κ)).map φ = 1 := by
    rw [← e1]
    exact ⟨fun h => by rw [h, map_one, Units.val_one], fun h => matHom_injective _ _ _ (by
      rw [map_one]; exact Units.ext h)⟩
  have c1 : β.map φ * β'.map φ = 1 := by rw [← Matrix.map_mul, hb1, Matrix.map_one _ (map_zero _) (map_one _)]
  have c2 : β'.map φ * β.map φ = 1 := by rw [← Matrix.map_mul, hb2, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e2, hK, Matrix.map_mul, Matrix.map_mul]
  constructor
  · intro h
    rw [h, Matrix.mul_one, c1]
  · intro h
    have := congrArg (fun X => β'.map φ * X * β.map φ) h
    simpa only [← Matrix.mul_assoc, c2, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc _ (β'.map φ) (β.map φ)] using this

set_option maxHeartbeats 2000000 in

theorem exists_frame {hF : D.host.F = maximalRealSubfield D.host.E} {PV : principalLevelFrame.RowPsi V V.rank}
    (hs : GlobalTheory.NJoin.StdFrame hF PV) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (Dv : InertDatum D.host.E V.rank v w)
    (hc : IsConjAt D.sp.cm.sig (rfl : w.under (𝓞 D.host.F) = _) Dv.σw)
    (he : ∀ z, Dv.e (ReciprocityTheory.Aut.compAt D.host.E v (Formalism.IndefR.principalLevelFrame.tensCastR hF z)) = GlobalTheory.LFun.compAt D.host.F w z)
    (ht : ∀ κ : GAf D.host.E V.rank,
      TrivOutside {v} κ ↔ PV.ψ κ ∈ (emb D.sp.cm.sig V.gram (w.under (𝓞 D.host.F))).range) :
    ∃ a, IsFrameAt w (frameLat V) a ∧ ∀ κ, a⁻¹ * locMat D.sp.cm.sig V.gram (rfl : w.under (𝓞 D.host.F) = _)
      (proj D.sp.cm.sig V.gram _ (PV.ψ κ)) * a = Dv.loc κ := by
  obtain ⟨⟨β, β', hb1, hb2, hK⟩, hUm⟩ := hs
  set φ := GlobalTheory.LFun.compAt D.host.F w
  let b : GL (Fin V.rank) (w.adicCompletion D.host.E) := ⟨β.map φ, β'.map φ,
    by rw [← Matrix.map_mul, hb1, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, hb2, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have key : ∀ κ, locMat D.sp.cm.sig V.gram (rfl : w.under (𝓞 D.host.F) = _) (proj D.sp.cm.sig V.gram _ (PV.ψ κ)) =
      b * (Dv.P * Dv.loc κ * Dv.P⁻¹) * b⁻¹ := by
    intro κ
    rw [InertDatum.loc, mul_assoc Dv.P, mul_inv_cancel_right, mul_inv_cancel_left]
    refine Units.ext ?_
    rw [← finMat_map_compAt, hK, Matrix.map_mul, Matrix.map_mul, Units.val_mul, Units.val_mul]
    congr 2
    refine Matrix.ext fun i j => ?_
    have := he ((Formalism.IndefR.principalLevelFrame.tensCastR hF).symm (κ.1.1 i j))
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V (w.under (𝓞 D.host.F))
  obtain ⟨e₀, ⟨-, ⟨a₀, ha₀, -, e1⟩, e2⟩, -⟩ := (((exists_isInertChart _ (isCMExt_host D) _).2 w rfl hw).2.2.2.2 _ hc).2
    _ _ _ hH hL.fg hL.span_eq_top hd
  have hP := (GlobalTheory.InertDoubleCoset.mem_range_iff _ _).1 Dv.Pint
  obtain ⟨c, hc0, hcz⟩ := exists_scalar Dv.unram (a₀⁻¹ * b) fun U hU i1 i2 => by
    have hy : Dv.P⁻¹ * U * Dv.P ∈ Formalism.UG.GU Dv.σw V.rank := by
      have h1 : Formalism.UG.cT Dv.σw U.1 * U.1 = 1 := by
        have : Formalism.UG.cT Dv.σw U.1 * 1 * U.1 = 1 := hU
        rwa [Matrix.mul_one] at this
      show Formalism.UG.cT Dv.σw (Dv.P⁻¹ * U * Dv.P).1 * Formalism.UG.antiJ _ _ * (Dv.P⁻¹ * U * Dv.P).1 = Formalism.UG.antiJ _ _
      conv_lhs => rw [← Dv.Panti]
      rw [← Matrix.mul_assoc, ← Formalism.UG.cT_mul, Matrix.mul_assoc, ← Units.val_mul, mul_assoc Dv.P⁻¹,
        mul_inv_cancel_left, Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ U.1, h1,
        Matrix.one_mul, Dv.Panti]
    obtain ⟨κ, hκ, eκ⟩ := GlobalTheory.T.exists_trivOutside_inertDatum_local_eq _ _ v w Dv _ hy
    have hUi : U ∈ (Formalism.UG.bc (n := Fin V.rank) (Formalism.UG.intL (w.adicCompletion D.host.E)).subtype).range :=
      (GlobalTheory.InertDoubleCoset.mem_range_iff _ _).2 ⟨i1, i2⟩
    have hκU : κ ∈ Umax D.host.E V.rank := GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral _ _ v w Dv κ hκ
      (by rw [eκ]; exact ((GlobalTheory.InertDoubleCoset.mem_range_iff _ _).1
            (mul_mem (mul_mem (inv_mem Dv.Pint) hUi) Dv.Pint)).1)
    obtain ⟨x, hx⟩ := (ht κ).1 hκ
    have hxs := (Supp.emb_mem_KsphC V x).1 (by rw [hx]; exact (hUm κ).1 hκU)
    have h5 := GlobalTheory.SatInd.CosetFin.entries_int ((e2 x).1 hxs)
    have h6 : (e₀ x : GL (Fin V.rank) (w.adicCompletion D.host.E)) = a₀⁻¹ * b * U * (a₀⁻¹ * b)⁻¹ := by
      have h7 := key κ
      rw [← hx, proj_emb_self, eκ] at h7
      rw [e1, h7]
      group
    rw [← h6]
    exact h5
  let s : GL (Fin V.rank) (w.adicCompletion D.host.E) := ⟨c • 1, c⁻¹ • 1,
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul, Matrix.one_mul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, Matrix.one_mul]⟩
  have hsc : ∀ x, x * s = s * x := fun x => Units.ext (by
    show x.1 * (c • 1) = (c • 1) * x.1
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])
  have hf : IsFrameAt w (frameLat V) (b * s) := fun y => by
    have e : (b * s).1 *ᵥ y = a₀.1 *ᵥ ((a₀⁻¹ * b).1 *ᵥ (c • y)) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left, Units.val_mul, ← Matrix.mulVec_mulVec]
      congr 1
      show (c • (1 : Matrix _ _ _)) *ᵥ y = _
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [e, ← ha₀]
    exact hcz y
  refine ⟨b * s * Dv.P, (InertChart.isFrameAt_mul hf Dv.Pint).1, fun κ => ?_⟩
  rw [key]
  calc (b * s * Dv.P)⁻¹ * (b * (Dv.P * Dv.loc κ * Dv.P⁻¹) * b⁻¹) * (b * s * Dv.P)
      = Dv.P⁻¹ * s⁻¹ * ((Dv.P * Dv.loc κ * Dv.P⁻¹) * s) * Dv.P := by group
    _ = Dv.loc κ := by rw [hsc]; group

open Classical in

theorem exists_sphOp {n : ℕ} (hn : V.rank = n) {hF : D.host.F = maximalRealSubfield D.host.E} {PV : principalLevelFrame.RowPsi V n}
    (hs : GlobalTheory.NJoin.StdFrame hF PV) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (Dv : InertDatum D.host.E n v w)
    (hc : IsConjAt D.sp.cm.sig (rfl : w.under (𝓞 D.host.F) = _) Dv.σw)
    (he : ∀ z, Dv.e (ReciprocityTheory.Aut.compAt D.host.E v (Formalism.IndefR.principalLevelFrame.tensCastR hF z)) = GlobalTheory.LFun.compAt D.host.F w z)
    (ht : ∀ κ : GAf D.host.E n,
      TrivOutside {v} κ ↔ PV.ψ κ ∈ (emb D.sp.cm.sig V.gram (w.under (𝓞 D.host.F))).range)
    {d : Fin n → ℤ} (hd : Antitone d) (t : Formalism.UG.GU Dv.σw n) (htd : t.1.1 = Matrix.diagonal fun k => Dv.ϖ ^ d k) :
    ∃ R : Finset (GAf D.host.E n), GlobalTheory.Hk3.SphOp V w (List.ofFn d) (R.image PV.ψ) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf D.host.E n → W),
        (∀ κ ∈ Umax D.host.E n, TrivOutside {v} κ → NG.rt D.host.E n κ φ = φ) →
        ∑ γ ∈ R, NG.rt D.host.E n γ φ =
          heckeFunI D.host.E n (Umax D.host.E n) Dv (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) t) φ := by
  subst hn
  obtain ⟨a, ha, hloc⟩ := exists_frame hs hw Dv hc he ht
  obtain ⟨x, hx, ex⟩ := GlobalTheory.T.exists_trivOutside_inertDatum_local_eq _ _ v w Dv _ t.2
  obtain ⟨R, hR⟩ := GlobalTheory.InertDCOp.exists_reps Dv (GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal _ _ v w Dv) (GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact _ _ v w Dv) hx
  refine ⟨R, ?_, fun W _ _ φ hφ => ?_⟩
  · obtain ⟨e, f, hef⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (comp_finAdEquiv D) w
    obtain ⟨ϖ, p1, p2⟩ : ∃ ϖ ∈ w.asIdeal, ϖ ∉ w.asIdeal ^ 2 :=
      SetLike.exists_of_lt (Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl)
    have hsu : ∀ κ, SuppF V f (PV.ψ κ) ↔ TrivOutside {v} κ := fun κ =>
      (Supp.suppF_iff_of_isPrimeIdem V hef rfl _).trans (ht κ).symm
    have hK : ∀ g, g ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ ∃ k ∈ GlobalTheory.InertSph.Kv D.host.E V.rank v, PV.ψ k = g :=
      fun g => by
        constructor
        · rintro ⟨m1, m2⟩
          obtain ⟨k, rfl⟩ := PV.onto g m1.1
          exact ⟨k, ⟨(hs.2 k).2 m1, (hsu k).1 m2⟩, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨(hs.2 k).1 hk.1, (hsu k).2 hk.2⟩
    obtain ⟨s1, s2⟩ := rep_image PV.ψ PV.inj hK hR.1 hR.2
    have hu : ∀ i, Valued.v (Dv.ϖ ^ d i) = WithZero.exp (-d i) := fun i => by
      rw [map_zpow₀, show Valued.v Dv.ϖ = WithZero.exp (-1 : ℤ) from Dv.unram.2.2.2.1, ← WithZero.exp_zsmul]
      simp
    refine ⟨e, f, ϖ, PV.ψ x, offS_iff.2 (Finset.notMem_empty _), hef, p1, p2,
      List.pairwise_ofFn.2 fun i j hij => hd hij.le, fun _ _ => Iff.rfl, fun _ _ _ => rfl, (hsu x).2 hx,
      divAt_of_diagonal rfl hef p1 p2 ha hu (by rw [hloc, ex, htd]), fun γ hγ => ?_, fun γ hγ => ⟨?_, s1 γ hγ⟩, s2⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR.1 y hy
      exact (hsu _).2 (GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 hx) hk₂.2)
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hγ
      exact PV.into y
  · rw [sum_reps_eq Dv hx hR W φ hφ]
    congr 2
    exact Subtype.ext ex

end Frame

end GlobalTheory.InertEigSat

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertEigSat

set_option maxHeartbeats 4000000 in

theorem heckeFunI_eigC (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (h41 : Formalism.MainNotions.SumRepresentations.Conclusion41 D)
    (i : D.nd.Loc) (x : D.nd.X i) {w : HeightOneSpectrum (𝓞 D.host.E)} (hns : ¬ Formalism.BasicNotions.IsSplitPl D.host w)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hov : NG.OverPl w v)
    (Dv : InertDatum D.host.E D.R.nV v w)
    (hfix : ∀ g : D.what₂.Mt (D.nd.mu i) (D.nd.j i), ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ →
      NG.rt D.host.E D.R.nV κ ((P.M.loc i).real g) = (P.M.loc i).real g)
    (P₀ : D.naut.AV i) (hP₀ : D.naut.ptV i P₀ = some x) (α₀ : Fin (D.R.nV / 2) → ℂ)
    (hα₀ : D.naut.satV i P₀ w = Multiset.map α₀ Finset.univ.val)
    (h0 : Formalism.UG.GU Dv.σw D.R.nV → ℂ) (hh0 : h0 ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw D.R.nV)) :
    ∀ g ∈ eigC D.nd D.naut i x, heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0 ((P.M.loc i).real g) =
      Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield D.host.E) v) h0 α₀ • (P.M.loc i).real g := by
  classical
  obtain ⟨C, a, xs, hC⟩ := GlobalTheory.EigInert.heckeFunI_umax_sum Dv h0 hh0
  set c := Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield D.host.E) v) h0 α₀ with hc
  intro g hg
  unfold eigC at hg
  refine Submodule.iSup_induction _ (motive := fun g => heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0
    ((P.M.loc i).real g) = c • (P.M.loc i).real g) hg ?_ ?_ ?_
  · intro P' g' hg'
    by_cases hP' : D.naut.ptV i P' = some x
    · rw [iSup_pos (show P' ∈ {P | D.naut.ptV i P = some x} from hP')] at hg'
      obtain ⟨α', hα', hsv'⟩ := GlobalTheory.EigInert.satParam hL D P i P' v w hov hns Dv
      have hub : ubc D.R.nV (D.naut.satV i P' w) = ubc D.R.nV (D.naut.satV i P₀ w) := by
        have h41i := (show Formalism.MainNotions.SumRepresentations.At.Conclusion41 D.nd D.naut i from h41 i).2.1 P' P₀ (by rw [hP']; simp) (by rw [hP', hP₀])
        have hS : w ∉ D.nd.S i := fun hm => hns (D.nd.SQ_split i w (Or.inl hm))
        have hQ : w ∉ D.nd.Q i := fun hm => hns (D.nd.SQ_split i w (Or.inr hm))
        exact (h41i.2 w hS hQ).2 hns
      rw [hsv', hα₀] at hub
      have hW := GlobalTheory.T.satakeTransform_eq_of_unramifiedBaseChange_eq _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α' _ hub h0 hh0
      rw [hc, ← hW]
      have hmem : (P.M.loc i).real g' ∈ NG.isoTyp (P.H.av.rep i P').ρ (P.H.av.rep i P').S := by
        have h2 := hg'
        rw [P.H.av.typeV] at h2
        exact h2
      exact GlobalTheory.T.isotypicFixedVector_isSatakeEigen_inertPlace _ _ (P.H.av.rep i P') v w hov Dv α' hα' _ hmem (hfix g') h0 hh0
    · rw [iSup_neg (show P' ∉ {P | D.naut.ptV i P = some x} from hP')] at hg'
      rw [(Submodule.mem_bot ℂ).1 hg']
      simp [hC]
  · simp [hC]
  · intro g1 g2 h1 h2
    rw [hC] at h1 h2 ⊢
    simp only [map_add, smul_add, Finset.sum_add_distrib, h1, h2]

open Formalism.IndefR Formalism.IndefR.Links in

theorem real_cast {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    {X : GlobalTheory.NJoin.RealAt D cf nch tp} {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (A : GlobalTheory.NJoin.Agree X M rep) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (k : ℕ)
    (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) :
    ∃ e : (X.R.cV j).W ≃ₗ[ℂ] (M μ k p1 p2).wt.W, ∀ (x : D.what₂.Mt μ (j.1 + 1)) h,
      (M μ k p1 p2).real (hk ▸ x) h = e (X.fn hμ j x ((A.PV j).ψ ((A.a j)⁻¹ * h))) := by
  subst hk
  exact ⟨A.eW μ hμ j, A.real μ hμ j⟩

theorem cast_eq_zero {D : D7} {μ : D.what₂.Tup} {a k : ℕ} (hk : a = k) (x : D.what₂.Mt μ a)
    (h : (hk ▸ x : D.what₂.Mt μ k) = 0) : x = 0 := by
  subst hk
  exact h

open Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Mult Formalism.L2.Theta Formalism.L2.DIV GlobalTheory.Hk3 in
set_option maxHeartbeats 1000000 in

theorem sum_ext {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ w ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP w) {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    {d : List ℤ} {R : Finset (GA D V)} (hR : SphOp V w d R) (z : ℂ)
    (he : hkF V w (Finsupp.single d 1) f = z • f) (g : GA D V) :
    ∑ γ ∈ R, c.ext f (g * γ) = z • c.ext f g := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := GlobalTheory.DefLiftHecke.one_pow_notMem w 0
  obtain ⟨hk, -⟩ := GlobalTheory.LevOp.level_operators V β Λ 1 (flag1L L) hB w h1 hw
  have h2 := ((GlobalTheory.SphLabelOps.label_operators V w).1 d R hR).2 _
    (GlobalTheory.PRep.rightReg ℂ (GA D V) c.W) (c.ext f) fun k hkk => funext fun g =>
      GlobalTheory.DefLiftHecke.ext_level c hc hf (hk k hkk).1 (hk k hkk).2 g
  have h3 := congrFun h2 g
  have h4 := GlobalTheory.DefLiftHecke.ext_hkF c hc w (Finsupp.single d 1) f g
  rw [he, map_smul, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, one_smul] at h4
  rw [opOf, Finsupp.sum_single_index (by exact zero_smul _ _), one_smul, Finset.sum_apply, LinearMap.sum_apply,
    Finset.sum_apply] at h3
  exact h3.trans h4.symm

open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.Theta GlobalTheory.Hk3 in
set_option maxHeartbeats 1000000 in

theorem sum_extV {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) (j : Fin D.R.m) (t : X.T) (h) (hh : IsOpsV X.R j t h)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hG : Good X.R t w) {d : List ℤ} {R : Finset (GA D (Vc D j))}
    (hR : SphOp (Vc D j) w d R) (y : (X.R.HV j t).H) (c : ℂ) (hy : h w (Finsupp.single d 1) y = c • y) (g) :
    ∑ γ ∈ R, X.R.extV j t y (g * γ) = c • X.R.extV j t y g :=
  have hC := X.given.core
  sum_ext (X.R.cV j) (hC.models.cV j) (hC.lev.βV j) (L := X.R.datVt j t) hG
    ((hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)) hR c
    ((hh w hG _ y).symm.trans ((congrArg (X.R.HV j t).e hy).trans (map_smul _ _ _))) g

set_option maxHeartbeats 4000000 in

theorem eig_eq_satU : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ P₀, D.naut.ptV i P₀ = some x ∧ ∃ α₀ : Fin ((Formalism.IndefR.Links.Vc D j).rank / 2) → ℂ, D.naut.satV i P₀ w = Finset.univ.val.map α₀ ∧ ∀ (τ : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E), Formalism.UG.IsUnramInv ϖ τ (Formalism.UG.qV D.host.F (w.under (𝓞 D.host.F))) → GlobalTheory.LFun.IsConjAt D.sp.cm.sig (rfl : w.under (𝓞 D.host.F) = _) τ → ∀ (d : Fin (Formalism.IndefR.Links.Vc D j).rank → ℤ) (t' : Formalism.UG.GU τ (Formalism.IndefR.Links.Vc D j).rank), Antitone d → t'.1.1 = Matrix.diagonal (fun k => ϖ ^ d k) → s w (List.ofFn d) = Formalism.UG.SatU ϖ (Formalism.UG.qV D.host.F (w.under (𝓞 D.host.F))) (Formalism.UG.dosetInd ℂ (Formalism.UG.KU τ (Formalism.IndefR.Links.Vc D j).rank) t') α₀ := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 h hops s hs w hG hin
  classical
  have hn : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hns : ¬ Formalism.BasicNotions.IsSplitPl D.host w := GlobalTheory.T.not_isSplitPlace_of_inert_over_realSubfield D w hin
  have hf0 : (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ≠ 0 := fun e => hy0 (X.hinj _ _ (by
    rw [hy, cast_eq_zero hj f e, map_zero]
    exact congrArg Subtype.val (map_zero (X.IL.jMt _ hμ j))))
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, D.naut.ptV i P₀ = some x := by
    by_contra hne
    apply hf0
    unfold eigC at hf
    have : (⨆ P ∈ {P | D.naut.ptV i P = some x}, D.naut.typeV i P) = ⊥ :=
      iSup_eq_bot.2 fun P' => iSup_eq_bot.2 fun hP' => absurd ⟨P', hP'⟩ hne
    rw [this] at hf
    exact (Submodule.mem_bot ℂ).1 hf
  obtain ⟨v₀, Dv₀, hov₀⟩ := GlobalTheory.T.exists_inertLocalDatum_at_inertPlace D hA.hF w hin
  obtain ⟨α₀, -, hα₀⟩ := GlobalTheory.EigInert.satParam hL D P i P₀ v₀ w hov₀ hns Dv₀
  refine ⟨P₀, hP₀, ?_⟩
  rw [hn]
  refine ⟨α₀, hα₀, fun τ ϖ hU hc d t hd ht => ?_⟩
  obtain ⟨v, Dv, hov, rfl, rfl, hq, he, hsupp⟩ :=
    exists_datum D.host.F hA.hF D.sp.cm.sig (fun _ => rfl) D.R.nV w hin τ ϖ hU hc
  obtain ⟨R, hR, hop⟩ := exists_sphOp hn (hA.stdV j) hin Dv hc he (triv_iff (hA.stdV j) hsupp) hd t ht
  have hfix := GlobalTheory.T.operator_eigen_good_place_first hAF hL D P X hA h41 h7 htl i hμ j hj h hops w hG hin v hov
  have k1 := heckeFunI_eigC hL D P h41 i x hns hov Dv hfix P₀ hP₀ α₀ hα₀ _
    (Formalism.UG.Final.DosetIndMem _ (Formalism.UG.KU Dv.σw D.R.nV) ℂ t) _ hf
  rw [← hop _ _ (hfix _), hq] at k1
  have k2 := sum_extV X j _ h hops hG hR y _ (hs w _ hG ⟨_, hR⟩)
  obtain ⟨e, hreal⟩ := real_cast hA hμ j _ hj (D.nd.j_range i).1 (D.nd.j_range i).2
  have k3 : ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ ((P.M.loc i).real (hj ▸ f)) =
      s w (List.ofFn d) • (P.M.loc i).real (hj ▸ f) := by
    funext g
    have k4 := congrArg e (k2 ((hA.PV j).ψ ((hA.a j)⁻¹ * g)))
    rw [Finset.sum_image (hA.PV j).inj.injOn, map_sum, map_smul, hy] at k4
    rw [Finset.sum_apply, Pi.smul_apply]
    refine (Finset.sum_congr rfl fun γ _ => ?_).trans (k4.trans (congrArg _ (hreal f g).symm))
    refine (hreal f (g * γ)).trans ?_
    rw [← mul_assoc, map_mul]
  have hne : (P.M.loc i).real (hj ▸ f) ≠ 0 := fun e0 => hf0 ((P.M.loc i).real_inj (e0.trans (map_zero _).symm))
  exact smul_left_injective ℂ hne (k3.symm.trans k1)

end GlobalTheory.InertEigSat

end
end
