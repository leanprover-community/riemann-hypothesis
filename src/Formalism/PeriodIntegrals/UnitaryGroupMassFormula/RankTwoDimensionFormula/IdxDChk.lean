import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDSI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAJacE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKLevi

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

theorem hrow_dot (x y : Fin n → A) : hrow σ J x ⬝ᵥ y = Formalism.UG.hform σ J x y := by
  simp only [hrow, Formalism.UG.hform, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

theorem sMat_mulVec (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) (y : Fin n → A) :
    sMat σ J b bs C D *ᵥ y = y + ∑ i, ∑ j, (((C - 1) i j * Formalism.UG.hform σ J (bs j) y) • b i +
      ((D - 1) i j * Formalism.UG.hform σ J (b j) y) • bs i) := by
  have key : ∀ (a c : Fin n → A) (t : A), (t • Matrix.vecMulVec a c) *ᵥ y = (t * (c ⬝ᵥ y)) • a := by
    intro a c t
    funext q
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hsum : ∀ (s : Finset (Fin k)) (f : Fin k → Matrix (Fin n) (Fin n) A),
      (∑ i ∈ s, f i) *ᵥ y = ∑ i ∈ s, f i *ᵥ y := by
    intro s f
    classical
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]
  unfold sMat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, hsum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_mulVec, key, key, hrow_dot, hrow_dot]

end Alg

variable {D : D7} {X : HidaSetting D}

theorem sMat_Lf (hI : IdxDInt) (b bs : Fin D.R.k → VA X.B.I) (hb : ∀ i, b i ∈ X.B.I.Lf ∧ bs i ∈ X.B.I.Lf)
    (C D' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hC : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ (D' - 1) i j ∈ IntAf X.B.I.F X.B.I.E)
    (y : VA X.B.I) (hy : y ∈ X.B.I.Lf) :
    sMat (sigA X.B.I) (JA X.B.I) b bs C D' *ᵥ y ∈ X.B.I.Lf := by
  rw [sMat_mulVec]
  refine X.B.I.Lf.add_mem hy (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_)
  have h1 : Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (bs j) y ∈ IntAf X.B.I.F X.B.I.E :=
    (hI X.B.I).1 _ (hb j).2 _ hy
  have h2 : Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (b j) y ∈ IntAf X.B.I.F X.B.I.E :=
    (hI X.B.I).1 _ (hb j).1 _ hy
  refine X.B.I.Lf.add_mem ?_ ?_
  · exact X.B.I.Lf.smul_mem ⟨_, (IntAf X.B.I.F X.B.I.E).mul_mem (hC i j).1 h1⟩ (hb i).1
  · exact X.B.I.Lf.smul_mem ⟨_, (IntAf X.B.I.F X.B.I.E).mul_mem (hC i j).2 h2⟩ (hb i).2

theorem one_sub_int (i j : Fin D.R.k) (C : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hC : C i j ∈ IntAf X.B.I.F X.B.I.E) : (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  split_ifs
  · exact sub_mem hC (one_mem _)
  · simpa using hC

theorem fmat_inv_fix (x : X.B.I.Gf) (w : VA X.B.I) (h : X.B.I.fmat x *ᵥ w = w) : X.B.I.fmat x⁻¹ *ᵥ w = w := by
  have h1 : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
    first
    | simp [Formalism.MainNotions.S.AutInst.fmat]
    | (simp only [Formalism.MainNotions.S.AutInst.fmat]
       rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one])
  calc X.B.I.fmat x⁻¹ *ᵥ w = X.B.I.fmat x⁻¹ *ᵥ (X.B.I.fmat x *ᵥ w) := by rw [h]
    _ = (X.B.I.fmat x⁻¹ * X.B.I.fmat x) *ᵥ w := by rw [Matrix.mulVec_mulVec]
    _ = w := by rw [h1, Matrix.one_mulVec]

theorem fixV_of (u : D.what₂.Word) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I y ∈ fixV X u := by
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
  · rw [show X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) from
      fmat_inv_fix _ _ (X.xu_fix u a).1]
    exact Or.inl (Or.inl ⟨a, rfl⟩)
  · rw [show X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) from
      fmat_inv_fix _ _ (X.xu_fix u a).2]
    exact Or.inl (Or.inr ⟨a, rfl⟩)
  · rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inr rfl

theorem idxSurj_of (hAlg : IdxDAlg) (hAd : IdxDAd) (hI : IdxDInt) (hSig : IdxDSig) (hFr : IdxDFrame)
    (hMat : IdxDMat) (hLev : IdxDLevi) : IdxSurj := by
  intro D X Y u _ A
  obtain ⟨e, he⟩ := hAd X.B.I.F X.B.g
  obtain ⟨b, bs, hfr, hL, hperp, hcong⟩ := hFr D X u e he
  obtain ⟨C, C', hCC, hint, hres⟩ := hMat D X Y.TR e he A
  obtain ⟨hinv, hherm⟩ := hSig X.B.I
  obtain ⟨hfix, hcomp, hone, hunit⟩ :=
    hAlg _ (sigA X.B.I) X.B.I.n D.R.k (JA X.B.I) (epsX X e) b bs hinv hherm hfr
  have hCC' : C * C' = 1 := mul_eq_one_comm.mp hCC
  set σ := sigA X.B.I with hσ
  set s := sMat σ (JA X.B.I) b bs C (C'.map σ)ᵀ with hs
  set sI := sMat σ (JA X.B.I) b bs C' (C.map σ)ᵀ with hsI
  have hmapT : ∀ M N : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), M * N = 1 →
      (N.map σ)ᵀ * (M.map σ)ᵀ = 1 := by
    intro M N hMN
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one]
  have h1 : s * sI = 1 := by
    rw [hs, hsI, hcomp, hCC', hmapT C C' hCC']
    exact hone 1 1 (by simp) (by simp)
  have h2 : sI * s = 1 := by
    rw [hs, hsI, hcomp, hCC, hmapT C' C hCC]
    exact hone 1 1 (by simp) (by simp)
  let u0 : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := ⟨s, sI, h1, h2⟩
  have hmem : u0 ∈ Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F) := hunit C C' hCC
  let s' : X.B.I.Gf := ⟨u0, hmem⟩
  have hfs : X.B.I.fmat s' = s := rfl
  have hintS : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ ((C'.map σ)ᵀ - 1) i j ∈ IntAf X.B.I.F X.B.I.E :=
    fun i j => ⟨one_sub_int i j C (hint i j).1, one_sub_int i j _ ((hI X.B.I).2 _ (hint j i).2)⟩
  have hintI : ∀ i j, (C' - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ ((C.map σ)ᵀ - 1) i j ∈ IntAf X.B.I.F X.B.I.E :=
    fun i j => ⟨one_sub_int i j C' (hint i j).2, one_sub_int i j _ ((hI X.B.I).2 _ (hint j i).1)⟩
  have hK : s' ∈ X.B.I.Kset := by
    show ∀ x, x ∈ X.B.I.Lf ↔ s *ᵥ x ∈ X.B.I.Lf
    intro x
    constructor
    · exact sMat_Lf hI b bs hL C _ hintS x
    · intro hx
      have := sMat_Lf hI b bs hL C' _ hintI _ hx
      rwa [← hsI, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at this
  have hfixs : ∀ w ∈ fixV X u, s *ᵥ w = w := by
    intro w hw
    exact hfix C _ w fun j => hperp j w hw
  let sF : Hfin X u := ⟨X.xu u * s' * (X.xu u)⁻¹, by
    intro y hy
    have e1 : X.B.I.fmat (X.xu u * s' * (X.xu u)⁻¹) =
        X.B.I.fmat (X.xu u) * X.B.I.fmat s' * X.B.I.fmat (X.xu u)⁻¹ := rfl
    have e2 : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = 1 := by
      have : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = X.B.I.fmat (X.xu u * (X.xu u)⁻¹) := rfl
      rw [this, mul_inv_cancel]; rfl
    rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfs, hfixs _ (fixV_of u y hy),
      Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]⟩
  have hcj : cj X u sF = s' := by
    show (X.xu u)⁻¹ * (X.xu u * s' * (X.xu u)⁻¹) * X.xu u = s'
    group
  refine ⟨sF, ?_, ?_⟩
  · rw [hcj]; exact hK
  · rw [hcj]
    funext v
    have hM : leviM Y.TR s' v = ((A v : GL (Fin D.R.k) (Y.TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (Y.TR.Fq v)) := by
      ext i j
      rw [← hres v i j]
      exact hLev D X Y.TR e he b bs hfr hL hcong C C' hCC hint v i j
    unfold levi
    split_ifs with hdet
    · ext i j
      show leviM Y.TR s' v i j = _
      rw [hM]
    · exact absurd (by rw [hM]; exact (A v).isUnit.map Matrix.detMonoidHom) hdet

end PI.UnitaryDimensionFormula
end
end

section
noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain

namespace PI.UnitaryDimensionFormula

section
variable {F : Type} [Field F] [NumberField F]

theorem adAd_natCast_apply (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (g : FiniteAdeleRing (𝓞 F) F) v = (g : v.adicCompletion F) :=
  map_natCast (Formalism.UG.evalV F v) g

theorem adAd_val_g (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (g : v.adicCompletion F) = v.intValuation (g : 𝓞 F) := by
  have e1 : (g : v.adicCompletion F) = ((g : F) : v.adicCompletion F) := by
    exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have e2 : (g : F) = algebraMap (𝓞 F) F (g : 𝓞 F) := (map_natCast _ g).symm
  rw [e2, HeightOneSpectrum.valuation_of_algebraMap]

theorem adAd_val_lt (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : (g : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) < 1 := by
  rw [adAd_val_g]; exact (v.intValuation_lt_one_iff_mem _).2 h

theorem adAd_val_one (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : (g : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) = 1 := by
  rw [adAd_val_g]
  exact (v.intValuation_eq_one_iff_mem_primeCompl _).2 h

def adOfInt (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨f, Filter.Eventually.of_forall hf⟩

theorem adOfInt_int (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : adOfInt f hf ∈ Formalism.UG.intAd F := hf

end

theorem idxDAd : IdxDAd := by
  intro F _ _ g
  let P : HeightOneSpectrum (𝓞 F) → Prop := fun v => (g : 𝓞 F) ∈ v.asIdeal
  have h01 : ∀ v : HeightOneSpectrum (𝓞 F),
      (if P v then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F := by
    intro v; split_ifs
    · exact one_mem _
    · exact zero_mem _
  let e := adOfInt (fun v => if P v then (1 : v.adicCompletion F) else 0) h01
  refine ⟨e, adOfInt_int _ _, ?_, ?_, ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show (if P v then (1 : v.adicCompletion F) else 0) * (if P v then 1 else 0) = if P v then 1 else 0
    split_ifs <;> simp
  · have ht : ∀ v : HeightOneSpectrum (𝓞 F),
        (if P v then (0 : v.adicCompletion F) else (g : v.adicCompletion F)⁻¹) ∈ v.adicCompletionIntegers F := by
      intro v
      split_ifs with hv
      · exact zero_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, adAd_val_one g v hv, inv_one]
    refine ⟨adOfInt _ ht, adOfInt_int _ _, ?_⟩
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (1 : v.adicCompletion F) - (if P v then 1 else 0) =
      (g : FiniteAdeleRing (𝓞 F) F) v * (if P v then 0 else (g : v.adicCompletion F)⁻¹)
    rw [adAd_natCast_apply]
    split_ifs with hv
    · simp
    · have hne : (g : v.adicCompletion F) ≠ 0 := by
        intro h0
        have := adAd_val_one g v hv
        rw [h0, map_zero] at this
        exact zero_ne_one this
      rw [sub_zero, mul_inv_cancel₀ hne]
  · intro c hc
    have hu : ∀ v : HeightOneSpectrum (𝓞 F), P v →
        Valued.v (1 + (g : v.adicCompletion F) * c v) = 1 := by
      intro v hv
      have hlt : Valued.v ((g : v.adicCompletion F) * c v) < 1 := by
        rw [map_mul]
        have hcv : Valued.v (c v) ≤ 1 := hc v
        calc Valued.v (g : v.adicCompletion F) * Valued.v (c v) ≤ Valued.v (g : v.adicCompletion F) * 1 :=
              mul_le_mul' le_rfl hcv
          _ < 1 := by rw [mul_one]; exact adAd_val_lt g v hv
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hlt), map_one]
    have hy : ∀ v : HeightOneSpectrum (𝓞 F),
        (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) ∈ v.adicCompletionIntegers F := by
      intro v
      split_ifs with hv
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu v hv, inv_one]
      · exact zero_mem _
    refine ⟨adOfInt _ hy, adOfInt_int _ _, ?_⟩
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (if P v then (1 : v.adicCompletion F) else 0) * (1 + (g : FiniteAdeleRing (𝓞 F) F) v * c v) *
      (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) = if P v then 1 else 0
    rw [adAd_natCast_apply]
    split_ifs with hv
    · have hne : (1 + (g : v.adicCompletion F) * c v) ≠ 0 := by
        intro h0
        have := hu v hv
        rw [h0, map_zero] at this
        exact zero_ne_one this
      rw [one_mul, mul_inv_cancel₀ hne]
    · simp

end PI.UnitaryDimensionFormula
end
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mat_idem_mul {Rg : Type} [Ring Rg] (E a b : Rg) (hE : E * E = E) (hc : ∀ x : Rg, E * x = x * E) :
    (E * a + (1 - E)) * (E * b + (1 - E)) = E * (a * b) + (1 - E) := by
  have h1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h3 : (1 - E) * (1 - E) = 1 - E := by rw [sub_mul, one_mul, h1, sub_zero]
  have e1 : E * a * (E * b) = E * (a * b) := by
    rw [mul_assoc, ← mul_assoc a E b, ← hc a, ← mul_assoc, ← mul_assoc, hE, mul_assoc]
  have e2 : E * a * (1 - E) = 0 := by
    have : a * (1 - E) = (1 - E) * a := by rw [mul_sub, sub_mul, mul_one, one_mul, hc a]
    rw [mul_assoc, this, ← mul_assoc, h1, zero_mul]
  have e3 : (1 - E) * (E * b) = 0 := by rw [← mul_assoc, h2, zero_mul]
  rw [add_mul, mul_add, mul_add, e1, e2, e3, h3, add_zero, zero_add]

theorem mat_lift_core {O : Type} [CommRing O] {k : ℕ} (gO eO wO : O) (he2 : eO * eO = eO) (hw2 : wO * wO = wO)
    (Mo No tt : Matrix (Fin k) (Fin k) O) (htt : ∀ i j, wO * (No * Mo - 1) i j = gO * tt i j)
    (hJ : ∀ m : O, ∃ y : O, eO * (1 + gO * m) * y = eO) :
    ∃ C C' : Matrix (Fin k) (Fin k) O, C' * C = 1 ∧ ∀ i j, (eO * wO) * C i j = (eO * wO) * Mo i j := by
  set Q : Matrix (Fin k) (Fin k) O := 1 + gO • tt with hQdef
  obtain ⟨m, hm⟩ : ∃ m : O, Q.det = 1 + gO * m := by
    have hQ : (Ideal.Quotient.mk (Ideal.span {gO})).mapMatrix Q = 1 := by
      have hπg : Ideal.Quotient.mk (Ideal.span {gO}) gO = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [hQdef, map_add, map_one]
      ext i j
      simp [hπg]
    have h1 : Ideal.Quotient.mk (Ideal.span {gO}) (Q.det - 1) = 0 := by
      rw [map_sub, RingHom.map_det, hQ, det_one, map_one, sub_self]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    refine ⟨a, ?_⟩
    rw [mul_comm, ha]; ring
  obtain ⟨yO, hey0⟩ := hJ m
  have hey : eO * Q.det * yO = eO := by rw [hm]; exact hey0
  set εO := eO * wO with hεdef
  set E : Matrix (Fin k) (Fin k) O := εO • 1 with hEdef
  have hEc : ∀ x : Matrix (Fin k) (Fin k) O, E * x = x * E := by
    intro x; simp [hEdef]
  have hε2 : εO * εO = εO := by
    calc εO * εO = (eO * eO) * (wO * wO) := by rw [hεdef]; ring
      _ = εO := by rw [he2, hw2]
  have hE2 : E * E = E := by simp [hEdef, smul_smul, hε2]
  have hEQ : E * (No * Mo) = E * Q := by
    ext i j
    simp only [hEdef, Matrix.smul_mul, one_mul, Matrix.smul_apply, smul_eq_mul, hQdef, Matrix.add_apply]
    have h1 : (No * Mo) i j = (No * Mo - 1) i j + (1 : Matrix (Fin k) (Fin k) O) i j := by
      rw [Matrix.sub_apply]; ring
    have h2 : wO * (gO * tt i j) = gO * tt i j := by
      rw [← htt i j, ← mul_assoc, hw2]
    have key : εO * (No * Mo - 1) i j = εO * (gO • tt) i j := by
     calc εO * (No * Mo - 1) i j = eO * (wO * (No * Mo - 1) i j) := by rw [hεdef]; ring
      _ = eO * (wO * (gO * tt i j)) := by rw [htt i j, h2]
      _ = εO * (gO * tt i j) := by rw [hεdef]; ring
      _ = εO * (gO • tt) i j := by rw [Matrix.smul_apply, smul_eq_mul]
    rw [h1, mul_add, mul_add, key, Matrix.smul_apply, smul_eq_mul]; ring
  set P : Matrix (Fin k) (Fin k) O := yO • Q.adjugate with hPdef
  have hEPQ : E * (P * Q) = E := by
    have : P * Q = (yO * Q.det) • (1 : Matrix (Fin k) (Fin k) O) := by
      rw [hPdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    rw [this, hEdef, smul_mul_smul, one_mul]
    congr 1
    calc εO * (yO * Q.det) = wO * (eO * Q.det * yO) := by rw [hεdef]; ring
      _ = εO := by rw [hey, hεdef, mul_comm]
  refine ⟨E * Mo + (1 - E), E * (P * No) + (1 - E), ?_, ?_⟩
  · rw [mat_idem_mul E _ _ hE2 hEc]
    have : E * (P * No * Mo) = E := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEc P, Matrix.mul_assoc, hEQ, ← Matrix.mul_assoc, ← hEc P,
        Matrix.mul_assoc, hEPQ]
    rw [this, add_sub_cancel]
  · intro i j
    have hEC : E * (E * Mo + (1 - E)) = E * Mo := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, hE2, Matrix.mul_sub, Matrix.mul_one, hE2, sub_self, add_zero]
    have := congrFun (congrFun hEC i) j
    simpa [hEdef, Matrix.smul_mul] using this

theorem idxDMat_of (hJ : IdxDJacE) : IdxDMat := by
  intro D X TR e he A
  have heO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Set.mem_union_right _ ⟨⟨e, he.1⟩, rfl⟩)
  obtain ⟨t, ht, het⟩ := he.2.2.1
  have htO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)
  let eO : IntAf X.B.I.F X.B.I.E := ⟨_, heO⟩
  let wO : IntAf X.B.I.F X.B.I.E := ⟨X.ew, X.ew_int⟩
  let tO : IntAf X.B.I.F X.B.I.E := ⟨_, htO⟩
  let gO : IntAf X.B.I.F X.B.I.E := X.B.g
  have hgO : ((gO : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    simp [gO]
  have kerZ : ∀ x : IntAf X.B.I.F X.B.I.E, (∀ v, TR.res v x = 0) →
      ∃ t : IntAf X.B.I.F X.B.I.E, wO * x = gO * t := by
    intro x hx
    obtain ⟨t, ht, he'⟩ := (TR.res_ker x).1 hx
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    change X.ew * (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t
    rw [hgO]; exact he'
  have resG : ∀ v, TR.res v gO = 0 := by
    refine (TR.res_ker gO).2 ⟨X.ew, X.ew_int, ?_⟩
    rw [hgO, mul_comm]
  have heq : eO = 1 - gO * tO := by
    apply Subtype.ext
    change (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e = 1 - (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t)
    rw [hgO]
    have h1 : e = 1 - (X.B.g : Af X.B.I.F) * t := by rw [← het]; ring
    rw [h1, TensorProduct.tmul_sub]
    congr 1
    rw [← map_natCast (Algebra.TensorProduct.includeRight (R := X.B.I.F) (A := X.B.I.E) (B := Af X.B.I.F)) X.B.g]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have resE : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * x) = TR.res v x := by
    intro v x
    rw [heq, sub_mul, one_mul, map_sub, mul_assoc, map_mul, resG, zero_mul, sub_zero]
  have resEps : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * wO * x) = TR.res v x := by
    intro v x
    rw [mul_assoc, resE]
    exact TR.res_ew v x
  choose a0 ha0 using fun i j => TR.res_joint (fun v => (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
  choose b0 hb0 using fun i j => TR.res_joint
    (fun v => ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) i j)
  let Mo : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E) := Matrix.of a0
  let No : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E) := Matrix.of b0
  have hNM : ∀ v i j, TR.res v ((No * Mo - 1) i j) = 0 := by
    intro v i j
    have hM : (TR.res v).mapMatrix Mo = (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := by
      ext i j; exact congrFun (ha0 i j) v
    have hN : (TR.res v).mapMatrix No = ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) := by
      ext i j; exact congrFun (hb0 i j) v
    have : (TR.res v).mapMatrix (No * Mo - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one, sub_self]
    exact congrFun (congrFun this i) j
  choose tt htt using fun i j => kerZ _ (fun v => hNM v i j)
  have hw2 : wO * wO = wO := Subtype.ext X.ew_idem
  have he2 : eO * eO = eO := Subtype.ext (by
    change ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, he.2.1])
  have hJO : ∀ m : IntAf X.B.I.F X.B.I.E, ∃ y : IntAf X.B.I.F X.B.I.E, eO * (1 + gO * m) * y = eO := by
    intro m
    obtain ⟨y, hy, hyeq⟩ := hJ X.B.I.F X.B.I.E X.B.g e he (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) m.2
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * (1 + (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m) * y =
      (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e
    rw [hgO]; exact hyeq
  obtain ⟨CO, C'O, hCC, hent⟩ := mat_lift_core gO eO wO he2 hw2 Mo No (Matrix.of tt) (fun i j => htt i j) hJO
  refine ⟨CO.map (IntAf X.B.I.F X.B.I.E).subtype, C'O.map (IntAf X.B.I.F X.B.I.E).subtype, ?_,
    fun i j => ⟨(CO i j).2, (C'O i j).2⟩, ?_⟩
  · rw [← Matrix.map_mul, hCC, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro v i j
    have hmem : epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j ∈ IntAf X.B.I.F X.B.I.E :=
      (eO * wO * CO i j).2
    unfold resT
    rw [dif_pos hmem]
    have : (⟨epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j, hmem⟩ : IntAf X.B.I.F X.B.I.E) =
        eO * wO * Mo i j := by
      rw [← hent i j]; rfl
    rw [this, resEps]
    exact congrFun (ha0 i j) v

end PI.UnitaryDimensionFormula
end
end

section
noncomputable section

open Matrix

namespace PI.UnitaryDimensionFormula

section DAlg

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

def daB (x : Fin k → Fin n → A) : Matrix (Fin n) (Fin k) A := Matrix.of fun p i => x i p

def daP (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) : Matrix (Fin n) (Fin n) A :=
  daB x * M * (Formalism.UG.cT σ (daB y) * J)

def daT (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) : Matrix (Fin n) (Fin n) A :=
  J * daB x * M * (Formalism.UG.cT σ (daB y) * J)

theorem da_gram (x y : Fin k → Fin n → A) (i j : Fin k) :
    (Formalism.UG.cT σ (daB x) * J * daB y) i j = Formalism.UG.hform σ J (x i) (y j) := by
  simp only [Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.hform, daB, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem da_mulVec (y : Fin k → Fin n → A) (v : Fin n → A) (i : Fin k) :
    ((Formalism.UG.cT σ (daB y) * J) *ᵥ v) i = Formalism.UG.hform σ J (y i) v := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.hform, daB, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem da_row (y : Fin k → Fin n → A) (j : Fin k) (q : Fin n) :
    (Formalism.UG.cT σ (daB y) * J) j q = hrow σ J (y j) q := by
  simp only [Matrix.mul_apply, Formalism.UG.cT, hrow, daB, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]

theorem da_sum (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) :
    ∑ i, ∑ j, M i j • Matrix.vecMulVec (x i) (hrow σ J (y j)) = daP σ J x y M := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, daP, Matrix.mul_apply,
    da_row, daB, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [hrow, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    ring

theorem da_sMat (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) :
    sMat σ J b bs C D = 1 + daP σ J b bs (C - 1) + daP σ J bs b (D - 1) := by
  unfold sMat
  simp only [Finset.sum_add_distrib, da_sum, add_assoc]

variable {σ}

theorem da_cT_cT (hσ : ∀ a, σ (σ a) = a) {m p : Type} (M : Matrix m p A) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j
  simp [Formalism.UG.cT, hσ]

theorem da_cT_add {m p : Type} (M N : Matrix m p A) :
    Formalism.UG.cT σ (M + N) = Formalism.UG.cT σ M + Formalism.UG.cT σ N := by
  ext i j
  simp [Formalism.UG.cT]

theorem da_cT_sub {m p : Type} (M N : Matrix m p A) :
    Formalism.UG.cT σ (M - N) = Formalism.UG.cT σ M - Formalism.UG.cT σ N := by
  ext i j
  simp [Formalism.UG.cT]

theorem da_herm (hσ : ∀ a, σ (σ a) = a) (hJ : Formalism.UG.IsHerm σ J) (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = σ (Formalism.UG.hform σ J y x) := by
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have h := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using h
  simp only [Formalism.UG.hform, map_sum, map_mul, hσ, hJ']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem da_smul_l (c : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (c • x) y = σ c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem da_smul_r (c : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x (c • y) = c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem da_smulB (c : A) (x : Fin k → Fin n → A) (hx : ∀ i, x i = c • x i) : c • daB x = daB x := by
  ext p i
  simp only [daB, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact (congrFun (hx i) p).symm

theorem da_PP (x y : Fin k → Fin n → A) (c : A) (hm : Formalism.UG.cT σ (daB y) * J * daB x = c • 1)
    (hx : c • daB x = daB x) (M N : Matrix (Fin k) (Fin k) A) :
    daP σ J x y M * daP σ J x y N = daP σ J x y (M * N) := by
  unfold daP
  calc daB x * M * (Formalism.UG.cT σ (daB y) * J) * (daB x * N * (Formalism.UG.cT σ (daB y) * J))
        = daB x * M * (Formalism.UG.cT σ (daB y) * J * daB x) * N * (Formalism.UG.cT σ (daB y) * J) := by
          simp only [Matrix.mul_assoc]
    _ = (c • daB x) * (M * N) * (Formalism.UG.cT σ (daB y) * J) := by
          rw [hm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = daB x * (M * N) * (Formalism.UG.cT σ (daB y) * J) := by rw [hx]

theorem parabolic_product_zero (x y x' y' : Fin k → Fin n → A) (hm : Formalism.UG.cT σ (daB y) * J * daB x' = 0)
    (M N : Matrix (Fin k) (Fin k) A) :
    daP σ J x y M * daP σ J x' y' N = 0 := by
  unfold daP
  calc daB x * M * (Formalism.UG.cT σ (daB y) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = daB x * M * (Formalism.UG.cT σ (daB y) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hm]; simp

theorem da_P_add (x y : Fin k → Fin n → A) (M N : Matrix (Fin k) (Fin k) A) :
    daP σ J x y (M + N) = daP σ J x y M + daP σ J x y N := by
  unfold daP
  simp only [Matrix.mul_add, Matrix.add_mul]

private theorem cT_mul_lemma {m p q : Type} [Fintype p] (X : Matrix m p A) (Y : Matrix p q A) :
    Formalism.UG.cT σ (X * Y) = Formalism.UG.cT σ Y * Formalism.UG.cT σ X := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem da_cTP (hσ : ∀ a, σ (σ a) = a) (hJ : Formalism.UG.IsHerm σ J) (x y : Fin k → Fin n → A)
    (M : Matrix (Fin k) (Fin k) A) :
    Formalism.UG.cT σ (daP σ J x y M) * J = daT σ J y x (Formalism.UG.cT σ M) := by
  unfold daP daT
  simp only [cT_mul_lemma]
  rw [da_cT_cT hσ, show Formalism.UG.cT σ J = J from hJ]
  simp only [Matrix.mul_assoc]

theorem da_JP (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) :
    J * daP σ J x y M = daT σ J x y M := by
  unfold daP daT
  simp only [Matrix.mul_assoc]



theorem da_TP (x y x' y' : Fin k → Fin n → A) (c : A)
    (hm : Formalism.UG.cT σ (daB x) * J * daB x' = c • 1) (hy : c • daB y = daB y) (M N : Matrix (Fin k) (Fin k) A) :
    daT σ J y x M * daP σ J x' y' N = daT σ J y y' (M * N) := by
  unfold daT daP
  calc J * daB y * M * (Formalism.UG.cT σ (daB x) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = J * daB y * M * (Formalism.UG.cT σ (daB x) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = J * (c • daB y) * (M * N) * (Formalism.UG.cT σ (daB y') * J) := by
          rw [hm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = J * daB y * (M * N) * (Formalism.UG.cT σ (daB y') * J) := by rw [hy]

theorem transfer_product_zero (x y x' y' : Fin k → Fin n → A)
    (hm : Formalism.UG.cT σ (daB x) * J * daB x' = 0) (M N : Matrix (Fin k) (Fin k) A) :
    daT σ J y x M * daP σ J x' y' N = 0 := by
  unfold daT daP
  calc J * daB y * M * (Formalism.UG.cT σ (daB x) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = J * daB y * M * (Formalism.UG.cT σ (daB x) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hm]; simp

end DAlg

theorem idxDAlg : IdxDAlg := by
  intro A _ σ n k J ε b bs hσ hJ hfr
  obtain ⟨hεε, hεσ, hb, hbs, hbb⟩ := hfr
  have hx1 : ε • daB b = daB b := da_smulB ε b hb
  have hx2 : σ ε • daB bs = daB bs := da_smulB (σ ε) bs hbs
  have hm1 : Formalism.UG.cT σ (daB bs) * J * daB b = ε • (1 : Matrix (Fin k) (Fin k) A) := by
    ext i j
    rw [da_gram, hbb i j, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hm2 : Formalism.UG.cT σ (daB b) * J * daB bs = σ ε • (1 : Matrix (Fin k) (Fin k) A) := by
    ext i j
    rw [da_gram, da_herm J hσ hJ, hbb j i, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hm3 : Formalism.UG.cT σ (daB bs) * J * daB bs = 0 := by
    ext i j
    rw [da_gram, Matrix.zero_apply, hbs i, hbs j, da_smul_l, da_smul_r, hσ, ← mul_assoc, hεσ, zero_mul]
  have hm4 : Formalism.UG.cT σ (daB b) * J * daB b = 0 := by
    ext i j
    rw [da_gram, Matrix.zero_apply, hb i, hb j, da_smul_l, da_smul_r, ← mul_assoc, mul_comm (σ ε) ε, hεσ,
      zero_mul]
  have hPP : ∀ M N, daP σ J b bs M * daP σ J b bs N = daP σ J b bs (M * N) :=
    fun M N => da_PP J b bs ε hm1 hx1 M N
  have hQQ : ∀ M N, daP σ J bs b M * daP σ J bs b N = daP σ J bs b (M * N) :=
    fun M N => da_PP J bs b (σ ε) hm2 hx2 M N
  have hPQ : ∀ M N, daP σ J b bs M * daP σ J bs b N = 0 := fun M N => parabolic_product_zero J b bs bs b hm3 M N
  have hQP : ∀ M N, daP σ J bs b M * daP σ J b bs N = 0 := fun M N => parabolic_product_zero J bs b b bs hm4 M N
  have hc1 : Formalism.UG.cT σ (1 : Matrix (Fin k) (Fin k) A) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hc1n : Formalism.UG.cT σ (1 : Matrix (Fin n) (Fin n) A) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hTadd : ∀ (x y : Fin k → Fin n → A) (M N : Matrix (Fin k) (Fin k) A),
      daT σ J x y (M + N) = daT σ J x y M + daT σ J x y N := by
    intro x y M N
    unfold daT
    simp only [Matrix.mul_add, Matrix.add_mul]
  have hT0 : ∀ x y : Fin k → Fin n → A, daT σ J x y 0 = 0 := by
    intro x y
    unfold daT
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C D y hy
    have h0 : ∀ (x y' : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A),
        (∀ j, Formalism.UG.hform σ J (y' j) y = 0) → daP σ J x y' M *ᵥ y = 0 := by
      intro x y' M hz
      unfold daP
      rw [← Matrix.mulVec_mulVec]
      have hz' : (Formalism.UG.cT σ (daB y') * J) *ᵥ y = 0 := by
        ext i
        rw [da_mulVec]
        exact hz i
      rw [hz', Matrix.mulVec_zero]
    rw [da_sMat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      h0 b bs _ (fun j => (hy j).2), h0 bs b _ (fun j => (hy j).1), add_zero, add_zero]
  · intro C₁ D₁ C₂ D₂
    rw [da_sMat, da_sMat, da_sMat]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hPP, hQQ, hPQ, hQP,
      add_zero]
    rw [show C₁ * C₂ - 1 = (C₁ - 1) + (C₂ - 1) + (C₁ - 1) * (C₂ - 1) by noncomm_ring,
      show D₁ * D₂ - 1 = (D₁ - 1) + (D₂ - 1) + (D₁ - 1) * (D₂ - 1) by noncomm_ring,
      da_P_add, da_P_add, da_P_add, da_P_add]
    abel
  · intro C D hC hD
    have hP : daP σ J b bs (C - 1) = 0 := by
      unfold daP
      rw [← hx1, Matrix.smul_mul, ← Matrix.mul_smul, hC]
      simp
    have hQ : daP σ J bs b (D - 1) = 0 := by
      unfold daP
      rw [← hx2, Matrix.smul_mul, ← Matrix.mul_smul, hD]
      simp
    rw [da_sMat, hP, hQ, add_zero, add_zero]
  · intro C C' hCC
    have hDt : (C'.map σ)ᵀ = Formalism.UG.cT σ C' := rfl
    rw [hDt, da_sMat]
    have hZ1 : (C - 1) + Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) + Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) * (C - 1) = 0 := by
      rw [da_cT_sub, da_cT_cT hσ, hc1,
        show C - 1 + (C' - 1) + (C' - 1) * (C - 1) = C' * C - 1 by noncomm_ring, hCC, sub_self]
    have hZ2 : (Formalism.UG.cT σ C' - 1) + Formalism.UG.cT σ (C - 1) + Formalism.UG.cT σ (C - 1) * (Formalism.UG.cT σ C' - 1) = 0 := by
      rw [da_cT_sub, hc1,
        show Formalism.UG.cT σ C' - 1 + (Formalism.UG.cT σ C - 1) + (Formalism.UG.cT σ C - 1) * (Formalism.UG.cT σ C' - 1) =
          Formalism.UG.cT σ C * Formalism.UG.cT σ C' - 1 by noncomm_ring,
        ← cT_mul_lemma, hCC, hc1, sub_self]
    calc Formalism.UG.cT σ (1 + daP σ J b bs (C - 1) + daP σ J bs b (Formalism.UG.cT σ C' - 1)) * J *
          (1 + daP σ J b bs (C - 1) + daP σ J bs b (Formalism.UG.cT σ C' - 1))
        = J + daT σ J b bs ((C - 1) + Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) +
              Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) * (C - 1)) +
            daT σ J bs b ((Formalism.UG.cT σ C' - 1) + Formalism.UG.cT σ (C - 1) +
              Formalism.UG.cT σ (C - 1) * (Formalism.UG.cT σ C' - 1)) := by
          rw [da_cT_add, da_cT_add, hc1n]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, da_cTP J hσ hJ, da_JP,
            da_TP J b bs bs b (σ ε) hm2 hx2, da_TP J bs b b bs ε hm1 hx1, transfer_product_zero J b bs b bs hm4,
            transfer_product_zero J bs b bs b hm3, add_zero, hTadd]
          abel
      _ = J := by rw [hZ1, hZ2, hT0, hT0, add_zero, add_zero]

end PI.UnitaryDimensionFormula
end
end

section
namespace PI.UnitaryDimensionFormula

theorem idxSurj_of_frame (hFr : IdxDFrame) : IdxSurj :=
  idxSurj_of idxDAlg idxDAd idxDInt idxDSig hFr (idxDMat_of idxDJacE) idxDLevi

end PI.UnitaryDimensionFormula
end
