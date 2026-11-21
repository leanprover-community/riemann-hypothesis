import Formalism.PeriodIntegrals.GTLower
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.NumMore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionXi
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.IoPolDiagHw
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliShift
import Lemmata.GeneralBFactRight.Imports
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionLift
import Formalism.PeriodIntegrals.HwIrred
import Formalism.PeriodIntegrals.SchurFock
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitPowerNormScale.NormUnitsZpowSq
import Formalism.GradedWeylDivisibility.FinalD

section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem ioIntegral_of (hZ : CapelliZ) (hL : LiftMod) (hV : ZScalarVanish) : IoIntegral := by
  intro n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨Z, hZi, hZa⟩ := hZ n N h lam sg hI
  obtain ⟨m, hm, hd⟩ := hL n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨f', hf', hZf⟩ := hZi m hm
  refine ⟨f', hf', ?_⟩
  have hsC : MvPolynomial.map (Int.castRingHom ℂ) s ∈ nablaSq ℂ n sg :=
    Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW s hs
  have hO : OtherPart h lam sg ≤ LinearMap.ker Z := by
    unfold OtherPart
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun hne => iSup_le fun hw =>
      iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [LinearMap.mem_ker, hZa mu hmu φ hφ t ht, hV n N h lam sg mu hI hmu hne hw, Int.cast_zero, zero_smul]
  have h0 := hO hd
  rw [LinearMap.mem_ker, map_sub, hZf, hZa sg hI io0 hE _ hsC] at h0
  have hz : zScalar h lam sg sg = cBr h lam sg := rfl
  rw [hz] at h0
  rw [map_smul]
  exact (sub_eq_zero.mp h0).symm

theorem sqAct_smul {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) (c : ℂ)
    (x : MvPolynomial (Fin k × Fin k) ℂ) : sqAct ℂ k mu g (c • x) = c • sqAct ℂ k mu g x := by
  rw [sqAct, sqAct, map_smul, smul_comm]

theorem gTLower_of_steps (hN : Numbers) (hX : XiFacts) (hE : IoExists) (hP4 : IoIntegral)
    (hA : AdjointBr) (hB : BrIntegral) : PI.GTLower := by
  intro n N h lam sg hI
  obtain ⟨hc0, hcB, hdeg⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, -⟩ := hX n N h lam sg hI
  obtain ⟨io0, ⟨hE1, hE2⟩, hx, hW⟩ := hE n N h lam sg hI
  let c : ℂ := ((cBr h lam sg : ℤ) : ℂ)
  let io := c • io0
  have hio : ∀ x, io x = c • io0 x := fun x => rfl
  have I2 : ∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam := fun s hs =>
    Submodule.smul_mem _ _ (hE1 s hs)
  have I3 : ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
      io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s) := by
    intro g s hs
    rw [hio, hio, hE2 g s hs, sqAct_smul]
  have I4 : io (extremal ℂ n sg) = c • xi ℂ h lam sg := by rw [hio, hx]
  have I5 : LastWeight lam sg io := by
    intro a s hs
    rw [hio, sqAct_smul, hW a s hs, smul_comm]
  have I1 : ∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
      io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f := by
    intro s hs
    obtain ⟨f, hf, hf'⟩ := hP4 n N h lam sg hI io0 ⟨hE1, hE2⟩ hx hW s hs
    exact ⟨f, hf, by rw [hio, ← map_smul]; exact hf'⟩
  obtain ⟨I6, br, hrest, hT⟩ := hA n N h lam sg hI io ⟨I2, I3⟩ I4 I5
  have B1 := hB n N h lam sg hI io br I1 I2 hrest.1 hT
  exact ⟨hc0, hcB, hxi0, hdeg, io, br, ⟨I1, I2, I3, I4, I5, I6⟩, ⟨B1, hrest⟩, hT⟩

end PI.WGL
end
end

section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem numbers_dominant_large : Numbers := by
  intro n N h lam sg hI
  exact ⟨PI.GTNum.cBr_ne_zero h lam sg hI, PI.GTNum.abs_cBr_le_cBd h lam sg hI,
    PI.GTNum.degZ_eq h lam sg⟩

theorem scalar_vanishing_criterion : ZScalarVanish := by
  intro n N h lam sg mu hsg hmu hne hw
  have hsum : (∑ i : Fin n, mu.w i) = ∑ i : Fin n, sg.w i := by
    unfold wsum at hw
    exact hw
  have hD : D0 h lam mu = D0 h lam sg := by
    unfold D0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ sg.w i := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  have hmem : mu.w i ∈ Rset h lam sg i := by
    have hm := PI.GTNum.sg_mem_R h lam mu hmu i
    unfold Rset at hm ⊢
    rw [hD] at hm
    exact hm
  unfold zScalar
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, hmem⟩)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  ring

end PI.WGL
end
end

section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem io_fixed_up {n : ℕ} (lam : DomWeight (n + 1)) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hU : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) f = f)
    (a b : Fin n) (hab : a < b) : pol ℂ a.castSucc b.castSucc f = 0 := by
  have hne : a ≠ b := ne_of_lt hab
  have key : ∀ m : ℕ, (rowGen ℂ a.castSucc b.castSucc f - Polynomial.C f).eval (C (m : ℂ)) ∈
      (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro m
    rw [Submodule.mem_bot, Polynomial.eval_sub, Polynomial.eval_C, PI.WHw.eval_rowGen, sub_eq_zero]
    have hdet : (1 + Matrix.single a b (m : ℂ)).det ≠ 0 := by
      rw [det_one_add_single, if_neg hne]; exact one_ne_zero
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
    have hgv : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b (m : ℂ) := rfl
    have hup : ∀ i j, j < i → g i j = 0 := by
      intro i j hji
      have hij : i ≠ j := ne_of_gt hji
      show (1 + Matrix.single a b (m : ℂ)) i j = 0
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_neg hij, zero_add]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact absurd (lt_trans hab hji) (lt_irrefl _)
    have hdiag : ∀ i, g i i = 1 := by
      intro i
      show (1 + Matrix.single a b (m : ℂ)) i i = 1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_true]
      rw [if_neg]; · simp
      rintro ⟨rfl, h⟩; exact hne h.symm
    have h1 := hU g hup hdiag
    have hT := embGL_transvec g a b (m : ℂ) hgv
    have hdet1 : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl g) lam.detShift = 1 := by
      unfold detPow
      have hd : Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hT, det_one_add_single,
          if_neg (fun h => hne (Fin.castSucc_injective _ h).symm)]
        rfl)
      rw [hd, one_zpow, Units.val_one]
    unfold sqAct at h1
    rw [hdet1, one_smul, hT] at h1
    exact h1
  have := PI.WHw.coeff_mem_of_eval ⊥ _ key 1
  rw [Submodule.mem_bot, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega), sub_zero] at this
  rw [pol_eq_rowDiv]
  exact this

theorem io_torus_diag {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n)
    (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hT : ∀ t : Fin n → ℂˣ, sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) f =
      ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) • f)
    (a : Fin n) (hd : lam.detShift ≤ sg.w a) :
    pol ℂ a.castSucc a.castSucc f = ((sg.w a - lam.detShift : ℤ) : ℂ) • f := by
  set d : ℕ := (sg.w a - lam.detShift).toNat with hd'
  have hdz : ((d : ℕ) : ℤ) = sg.w a - lam.detShift := Int.toNat_of_nonneg (by omega)
  have key : ∀ m : ℕ, (rowGen ℂ a.castSucc a.castSucc f - Polynomial.C f * (1 + Polynomial.X) ^ d).eval
      (C (m : ℂ)) ∈ (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro m
    have hm0 : (m : ℂ) + 1 ≠ 0 := by norm_cast
    let t : Fin n → ℂˣ := fun j => if j = a then Units.mk0 ((m : ℂ) + 1) hm0 else 1
    have h1 := hT t
    have hgv : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a a (m : ℂ) := by
      ext i j
      simp only [diagGL, Matrix.diagonal_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, t]
      by_cases hij : i = j <;> by_cases hia : i = a <;> simp_all [add_comm] <;> intro h <;> exact absurd h.symm hia
    have hTr := embGL_transvec (diagGL ℂ n t) a a (m : ℂ) hgv
    have hdet : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) lam.detShift =
        ((m : ℂ) + 1) ^ lam.detShift := by
      unfold detPow
      rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hTr,
        det_one_add_single, if_pos rfl]
    have hprod : ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) = ((m : ℂ) + 1) ^ sg.w a := by
      rw [Finset.prod_eq_single a (fun j _ hj => by simp [t, hj]) (by simp), Units.val_zpow_eq_zpow_val]
      simp [t]
    unfold sqAct at h1
    rw [hdet, hTr, hprod] at h1
    have hz : ((m : ℂ) + 1) ^ sg.w a = ((m : ℂ) + 1) ^ lam.detShift * ((m : ℂ) + 1) ^ d := by
      rw [← zpow_natCast, hdz, ← zpow_add₀ hm0]
      congr 1
      ring
    rw [hz, ← smul_smul] at h1
    have h2 := smul_right_injective _ (zpow_ne_zero _ hm0) h1
    rw [Submodule.mem_bot, Polynomial.eval_sub, PI.WHw.eval_rowGen, sub_eq_zero, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    rw [show (1 + C (m : ℂ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ^ d = C (((m : ℂ) + 1) ^ d) by
      rw [map_pow, map_add, map_one, add_comm (C (m : ℂ)) 1], mul_comm, ← smul_eq_C_mul]
    exact h2
  have := PI.WHw.coeff_mem_of_eval ⊥ _ key 1
  rw [Submodule.mem_bot, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, sub_eq_zero] at this
  rw [pol_eq_rowDiv]
  unfold rowDiv
  rw [this, ← hdz, Int.cast_natCast, smul_eq_C_mul, mul_comm, map_natCast]

theorem capXi (hx : XiFacts) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (hI : Interlace h lam sg) (u : ℂ) :
    Formalism.REAL.qdet (capE h lam) u (xi ℂ h lam sg) = capP sg u • xi ℂ h lam sg := by
  subst h
  obtain ⟨-, -, hU, hT, -, -⟩ := hx n (n + 1) rfl lam sg hI
  have hHW : Formalism.REAL.IsHW (capE rfl lam) (fun k => ((sg.w k : ℤ) : ℂ)) (xi ℂ rfl lam sg) := by
    refine ⟨fun a' => ?_, fun a' b' hab => ?_⟩
    · have hd : lam.detShift ≤ sg.w a' := by
        have ha := a'.isLt
        have h1 := (hI a').2
        have h2 : lam.w ⟨n, by omega⟩ ≤ lam.w ⟨a'.1 + 1, by omega⟩ := lam.anti (by
          rw [Fin.le_iff_val_le_val]
          show a'.1 + 1 ≤ n
          omega)
        have h3 : lam.detShift = lam.w ⟨n, by omega⟩ := by
          unfold DomWeight.detShift
          rw [dif_pos (by omega)] <;> congr 1
        linarith
      have e : pol ℂ (Fin.castLE (by omega : n ≤ n + 1) a') (Fin.castLE (by omega : n ≤ n + 1) a')
          (xi ℂ rfl lam sg) = ((sg.w a' - lam.detShift : ℤ) : ℂ) • xi ℂ rfl lam sg :=
        io_torus_diag lam sg (xi ℂ rfl lam sg) hT a' hd
      rw [capE_apply, if_pos rfl, e, ← add_smul]
      congr 1
      push_cast
      ring
    · have e : pol ℂ (Fin.castLE (by omega : n ≤ n + 1) a') (Fin.castLE (by omega : n ≤ n + 1) b')
          (xi ℂ rfl lam sg) = 0 :=
        io_fixed_up lam (xi ℂ rfl lam sg) hU a' b' hab
      rw [capE_apply, if_neg (ne_of_lt hab), e, add_zero]
  rw [Formalism.REAL.quantumDetHighestWeight_holds _ n (capE rfl lam) _ _ (capE_glRel rfl lam) hHW u]
  rfl

theorem capFacts_of (h3 : PI.HwIrred) (hx : XiFacts) : CapFacts := by
  intro n N h lam sg hI
  refine ⟨fun u => Formalism.REAL.qdet (capE h lam) u, ?_, ?_⟩
  · intro mu _ φ hφ s hs u
    exact capScalar h3 h lam mu φ hφ s hs u
  · intro u
    exact capXi hx h lam sg hI u

theorem ioExists_of' (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) : IoExists :=
  ioExists_of_cap h3 h4 hx (capFacts_of h3 hx)

end PI.WGL
end
end

section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem ioExists_of (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) : IoExists :=
  ioExists_of' h3 h4 hx

end PI.WGL
end
end

section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def CapScalar : Prop :=
  ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ s ∈ nablaSq ℂ n mu, ∀ u : ℂ,
      Formalism.REAL.qdet (capE h lam) u (φ s) = (∏ k : Fin n, (u - (k : ℂ) + (mu.w k : ℂ))) • φ s

def capF {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (i : Fin n) (v : ℤ) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ((-1 : ℂ) ^ n) • Formalism.REAL.qdet (capE h lam) (-((v : ℂ) - ((i.1 : ℤ) : ℂ)))

def capZ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ((List.finRange n).map fun i =>
    ((((Rset h lam sg i).erase (sg.w i)).toList.map fun v => capF h lam i v).prod)).prod

theorem list_scalar {V ι : Type*} [AddCommGroup V] [Module ℂ V] (L : List ι) (F : ι → Module.End ℂ V)
    (c : ι → ℂ) (x : V) (hL : ∀ j ∈ L, F j x = c j • x) : (L.map F).prod x = (L.map c).prod • x := by
  first | exact Bl.general_b_fact_right.goal1 .. | (apply Bl.general_b_fact_right.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right.goal1 <;> assumption) | (apply @Bl.general_b_fact_right.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right.goal1 <;> assumption) | (apply @Bl.general_b_fact_right.goal1 <;> first | assumption | infer_instance)

theorem capF_scalar (hC : CapScalar) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) (i : Fin n) (v : ℤ) :
    capF h lam i v (φ s) = (∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) • φ s := by
  rw [capF, LinearMap.smul_apply, hC h lam mu φ hφ s hs, smul_smul]
  congr 1
  have : ((-1 : ℂ) ^ n) = ∏ _j : Fin n, (-1 : ℂ) := by simp
  rw [this, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast; ring

theorem capZ_scalar (hC : CapScalar) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    capZ h lam sg (φ s) = ((zScalar h lam sg mu : ℤ) : ℂ) • φ s := by
  unfold capZ
  rw [list_scalar (List.finRange n) _
    (fun i => ∏ v ∈ (Rset h lam sg i).erase (sg.w i),
      ∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) (φ s)]
  · rw [← Fin.prod_univ_def]
    unfold zScalar
    push_cast
    rfl
  · intro i _
    rw [list_scalar _ _ (fun v => ∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) (φ s),
      Finset.prod_map_toList]
    intro v _
    exact capF_scalar hC h lam mu φ hφ s hs i v

def presRing {N : ℕ} (lam : DomWeight N) : Subring (Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) where
  carrier := {Q | ∀ f ∈ nablaSq ℤ N lam, ∃ f' ∈ nablaSq ℤ N lam,
    Q (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) f'}
  mul_mem' := by
    intro Q1 Q2 h1 h2 f hf
    obtain ⟨f2, hf2, e2⟩ := h2 f hf
    obtain ⟨f3, hf3, e3⟩ := h1 f2 hf2
    exact ⟨f3, hf3, by rw [Module.End.mul_apply, e2, e3]⟩
  one_mem' := fun f hf => ⟨f, hf, rfl⟩
  add_mem' := by
    intro Q1 Q2 h1 h2 f hf
    obtain ⟨f1, hf1, e1⟩ := h1 f hf
    obtain ⟨f2, hf2, e2⟩ := h2 f hf
    exact ⟨f1 + f2, add_mem hf1 hf2, by rw [LinearMap.add_apply, e1, e2, map_add]⟩
  zero_mem' := fun f hf => ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    intro Q h1 f hf
    obtain ⟨f1, hf1, e1⟩ := h1 f hf
    exact ⟨-f1, neg_mem hf1, by rw [LinearMap.neg_apply, e1, map_neg]⟩

theorem algebraMap_int_mem {N : ℕ} (lam : DomWeight N) (w : ℤ) :
    algebraMap ℂ (Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) (w : ℂ) ∈ presRing lam := by
  rw [map_intCast]; exact intCast_mem _ w

theorem pol_mem_presRing {N : ℕ} (lam : DomWeight N) (a b : Fin N) :
    (pol ℂ (m := N) a b : Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) ∈ presRing lam := by
  intro f hf
  exact ⟨pol ℤ a b f, pol_mem_dualWeyl ℤ lam.natW a b f hf, pol_map _ a b f⟩

theorem capE_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) : capE h lam a b ∈ presRing lam := by
  unfold capE
  refine add_mem (pol_mem_presRing lam _ _) ?_
  split_ifs
  · exact algebraMap_int_mem lam _
  · exact zero_mem _

theorem qdet_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (w : ℤ) :
    Formalism.REAL.qdet (capE h lam) (w : ℂ) ∈ presRing lam := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Subring.sum_mem _ fun σ _ => mul_mem (intCast_mem _ _) (Subring.list_prod_mem _ fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Formalism.REAL.Tm
  refine add_mem ?_ (capE_mem h lam _ _)
  split_ifs
  · have : (w : ℂ) - (k : ℂ) = ((w - (k.1 : ℤ) : ℤ) : ℂ) := by push_cast; rfl
    rw [this]; exact algebraMap_int_mem lam _
  · exact zero_mem _

theorem capF_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (i : Fin n) (v : ℤ) :
    capF h lam i v ∈ presRing lam := by
  unfold capF
  have h1 : (-((v : ℂ) - ((i.1 : ℤ) : ℂ))) = ((-(v - (i.1 : ℤ)) : ℤ) : ℂ) := by push_cast; ring
  have h2 : ((-1 : ℂ) ^ n) = (((-1 : ℤ) ^ n : ℤ) : ℂ) := by push_cast; ring
  rw [h1, h2, Algebra.smul_def]
  exact mul_mem (algebraMap_int_mem lam _) (qdet_mem h lam _)

theorem capZ_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    capZ h lam sg ∈ presRing lam := by
  unfold capZ
  refine Subring.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  refine Subring.list_prod_mem _ fun y hy => ?_
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
  exact capF_mem h lam i v

theorem capelliZ_of (hC : CapScalar) : CapelliZ := by
  intro n N h lam sg _
  refine ⟨capZ h lam sg, fun f hf => capZ_mem h lam sg f hf, ?_⟩
  intro mu _ φ hφ s hs
  exact capZ_scalar hC h lam sg mu φ hφ s hs

end PI.WGL
end
end

section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem capelli_scalar_identity : CapelliZ :=
  capelliZ_of fun h lam mu φ hφ s hs u => capScalar highest_weight_irreducible h lam mu φ hφ s hs u

end PI.WGL
end
end

section
noncomputable section

namespace PI.WGL.Adj

open Formalism.BasicNotions MvPolynomial

theorem fockF_eq_sum_of_subset {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS ?_
  intro m _ hm
  simp only [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fockF_add_left {σ : Type} [DecidableEq σ] (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  rw [fockF_eq_sum_of_subset (f + f') g _ MvPolynomial.support_add,
    fockF_eq_sum_of_subset f g _ Finset.subset_union_left,
    fockF_eq_sum_of_subset f' g _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem fockF_add_right {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (g + g') = Formalism.REAL.fockF f g + Formalism.REAL.fockF f g' := by
  unfold Formalism.REAL.fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]; ring

theorem den_pos {N : ℕ} (lam : DomWeight N) :
    0 < (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re ∧
      (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).im = 0 :=
  Formalism.GradedWeylDivisibility.fockPos _ _ (Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW)

theorem den_eq {N : ℕ} (lam : DomWeight N) :
    Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam) =
      (((Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [(den_pos lam).2])

theorem nf_eq {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f g = Formalism.REAL.fockF f g /
      (((Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re : ℝ) : ℂ) := by
  unfold normFock; rw [← den_eq]

theorem nf_herm {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam g f = star (normFock lam f g) := by
  rw [nf_eq, nf_eq, Formalism.GradedWeylDivisibility.fockHerm, star_div₀, Complex.star_def, Complex.conj_ofReal]

theorem nf_add_left {N : ℕ} (lam : DomWeight N) (f f' g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (f + f') g = normFock lam f g + normFock lam f' g := by
  unfold normFock; rw [fockF_add_left, add_div]

theorem nf_add_right {N : ℕ} (lam : DomWeight N) (f g g' : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (g + g') = normFock lam f g + normFock lam f g' := by
  unfold normFock; rw [fockF_add_right, add_div]

theorem nf_smul_left {N : ℕ} (lam : DomWeight N) (c : ℂ) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (c • f) g = c * normFock lam f g := by
  unfold normFock; rw [PI.WHw.bC_smul_left, mul_div_assoc]

theorem nf_smul_right {N : ℕ} (lam : DomWeight N) (c : ℂ) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (c • g) = star c * normFock lam f g := by
  unfold normFock; rw [PI.WHw.bC_smul_right, mul_div_assoc]

def nfL {N : ℕ} (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun f := normFock lam f g
  map_add' f f' := nf_add_left lam f f' g
  map_smul' c f := by simp [nf_smul_left]

theorem nfL_apply {N : ℕ} (lam : DomWeight N) (g f : MvPolynomial (Fin N × Fin N) ℂ) :
    nfL lam g f = normFock lam f g := rfl

theorem nf_sum_smul_left {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (∑ k ∈ S, a k • v k) g = ∑ k ∈ S, a k * normFock lam (v k) g := by
  rw [← nfL_apply, map_sum]
  simp [nfL_apply]

theorem nf_sum_smul_right {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (∑ k ∈ S, a k • v k) = ∑ k ∈ S, star (a k) * normFock lam f (v k) := by
  rw [nf_herm, nf_sum_smul_left, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', ← nf_herm]

theorem nf_sub_right {N : ℕ} (lam : DomWeight N) (f g g' : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (g - g') = normFock lam f g - normFock lam f g' := by
  rw [nf_herm, ← nfL_apply, map_sub, star_sub, nfL_apply, nfL_apply, ← nf_herm, ← nf_herm]

theorem nf_zero_right {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f 0 = 0 := by
  have := nf_smul_right lam 0 f 0
  simpa using this

theorem nf_self_im {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    (normFock lam f f).im = 0 := by
  rw [nf_eq, Complex.div_ofReal_im]
  by_cases hf : f = 0
  · subst hf; simp [Formalism.REAL.fockF]
  · rw [(Formalism.GradedWeylDivisibility.fockPos _ f hf).2, zero_div]

theorem nf_self_re_pos {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ≠ 0) :
    0 < (normFock lam f f).re := by
  rw [nf_eq, Complex.div_ofReal_re]
  exact div_pos (Formalism.GradedWeylDivisibility.fockPos _ f hf).1 (den_pos lam).1

theorem nf_self_re_nonneg {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    0 ≤ (normFock lam f f).re := by
  by_cases hf : f = 0
  · subst hf; rw [nf_zero_right]; simp
  · exact (nf_self_re_pos lam f hf).le

theorem nf_self_eq_zero {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (h : normFock lam f f = 0) : f = 0 := by
  by_contra hf
  have := nf_self_re_pos lam f hf
  rw [h] at this; simp at this

theorem nf_self_eq_re {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f f = (((normFock lam f f).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [nf_self_im])

theorem nf_extremal {N : ℕ} (lam : DomWeight N) :
    normFock lam (extremal ℂ N lam) (extremal ℂ N lam) = 1 := by
  unfold normFock
  refine div_self ?_
  intro h0
  have := (den_pos lam).1
  rw [h0] at this; simp at this

def nfCore {N : ℕ} (lam : DomWeight N) : InnerProductSpace.Core ℂ (MvPolynomial (Fin N × Fin N) ℂ) where
  inner x y := normFock lam y x
  conj_inner_symm x y := by
    show starRingEnd ℂ (normFock lam x y) = normFock lam y x
    rw [starRingEnd_apply, ← nf_herm]
  re_inner_nonneg x := nf_self_re_nonneg lam x
  add_left x y z := nf_add_right lam z x y
  smul_left x y r := by
    show normFock lam y (r • x) = starRingEnd ℂ r * normFock lam y x
    rw [nf_smul_right, starRingEnd_apply]
  definite x hx := nf_self_eq_zero lam x hx

theorem nf_cauchy_schwarz {N : ℕ} (lam : DomWeight N) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    ‖normFock lam y x‖ * ‖normFock lam x y‖ ≤ (normFock lam x x).re * (normFock lam y y).re := by
  letI : PreInnerProductSpace.Core ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nfCore lam).toCore
  exact InnerProductSpace.Core.inner_mul_inner_self_le x y

def frameCore (n : ℕ) (sg : DomWeight n) : InnerProductSpace.Core ℂ (nablaSq ℂ n sg) where
  inner x y := normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) x
  conj_inner_symm x y := by
    show starRingEnd ℂ (normFock sg (x : MvPolynomial (Fin n × Fin n) ℂ) y) = normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) x
    rw [starRingEnd_apply, ← nf_herm]
  re_inner_nonneg x := nf_self_re_nonneg sg x
  add_left x y z := by
    show normFock sg (z : MvPolynomial (Fin n × Fin n) ℂ) ((x + y : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ) = _
    rw [Submodule.coe_add, nf_add_right]
  smul_left x y r := by
    show normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) ((r • x : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ) = _
    rw [Submodule.coe_smul, nf_smul_right, starRingEnd_apply]
  definite x hx := by
    have := nf_self_eq_zero sg (x : MvPolynomial (Fin n × Fin n) ℂ) hx
    exact Subtype.ext this

theorem exists_frame (n : ℕ) (sg : DomWeight n) :
    ∃ (d : ℕ) (b : Fin d → MvPolynomial (Fin n × Fin n) ℂ), (∀ k, b k ∈ nablaSq ℂ n sg) ∧
      ∀ s ∈ nablaSq ℂ n sg, s = ∑ k, normFock sg s (b k) • b k := by
  letI : NormedAddCommGroup (nablaSq ℂ n sg) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (frameCore n sg)
  letI : InnerProductSpace ℂ (nablaSq ℂ n sg) := InnerProductSpace.ofCore (frameCore n sg).toCore
  haveI : FiniteDimensional ℂ (nablaSq ℂ n sg) := PI.WHw.bC_fd n n sg.natW
  let b := stdOrthonormalBasis ℂ (nablaSq ℂ n sg)
  refine ⟨Module.finrank ℂ (nablaSq ℂ n sg), fun k => (b k : MvPolynomial (Fin n × Fin n) ℂ),
    fun k => (b k).2, fun s hs => ?_⟩
  have h1 := congrArg Subtype.val (b.sum_repr' ⟨s, hs⟩)
  rw [Submodule.coe_sum] at h1
  exact h1.symm

end PI.WGL.Adj
end
end

section
noncomputable section

namespace PI.WGL.Adj

open Formalism.BasicNotions MvPolynomial

def gStar {N : ℕ} (g : GL (Fin N) ℂ) : GL (Fin N) ℂ where
  val := Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ)
  inv := Matrix.conjTranspose ((g⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  val_inv := by rw [← Matrix.conjTranspose_mul]; simp
  inv_val := by rw [← Matrix.conjTranspose_mul]; simp

theorem gStar_val {N : ℕ} (g : GL (Fin N) ℂ) :
    ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ) := rfl

theorem gStar_gStar {N : ℕ} (g : GL (Fin N) ℂ) : gStar (gStar g) = g := by
  ext i j; simp [gStar_val]

def cU (a : ℂˣ) : ℂˣ := Units.map (starRingEnd ℂ : ℂ →* ℂ) a

theorem cU_zpow_val (a : ℂˣ) (e : ℤ) : ((cU a ^ e : ℂˣ) : ℂ) = star ((a ^ e : ℂˣ) : ℂ) := by
  unfold cU
  rw [← map_zpow, Units.coe_map]
  rfl

theorem embGL_gStar {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    embGL ℂ n N h (gStar g) = gStar (embGL ℂ n N h g) := by
  have key : ∀ p q : Fin n ⊕ Fin 1,
      Matrix.fromBlocks (Matrix.conjTranspose (g : Matrix (Fin n) (Fin n) ℂ)) 0 0 1 p q =
        (starRingEnd ℂ) (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 1 q p) := by
    rintro (p | p) (q | q)
    · simp [Matrix.conjTranspose_apply]
    · simp
    · simp
    · have hp : p = q := Subsingleton.elim _ _
      subst hp; simp
  ext i j
  simp only [embGL, blkHom, gStar_val, Matrix.conjTranspose_apply]
  simp
  exact key _ _

theorem lastGL_cU (N : ℕ) (a : ℂˣ) : lastGL ℂ N (cU a) = gStar (lastGL ℂ N a) := by
  ext i j
  simp only [lastGL, diagGL, gStar_val, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; split_ifs <;> simp [cU]
  · have hji : j ≠ i := fun e => hij e.symm
    simp [hij, hji]

theorem detPow_gStar {N : ℕ} (g : GL (Fin N) ℂ) (k : ℤ) :
    detPow ℂ N (gStar g) k = star (detPow ℂ N g k) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, star_zpow₀]
  congr 1
  simp [gStar_val, Matrix.det_conjTranspose]

theorem sqAct_mem_nabla {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ nablaSq ℂ N lam) : sqAct ℂ N lam g f ∈ nablaSq ℂ N lam := by
  unfold sqAct
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)

theorem sqAct_smul {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (c : ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g (c • f) = c • sqAct ℂ N lam g f := by
  unfold sqAct
  rw [map_smul, smul_comm]

theorem nf_sqAct_adj {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (sqAct ℂ N lam g x) y = normFock lam x (sqAct ℂ N lam (gStar g) y) := by
  have hm : Matrix.conjTranspose (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) =
      Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j; simp [gStar_val, Matrix.conjTranspose_apply]
  have hf : Formalism.REAL.fockF (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) x) y =
      Formalism.REAL.fockF x (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) y) := by
    rw [Formalism.GradedWeylDivisibility.fockRowAdj, hm]
  unfold sqAct
  rw [nf_smul_left, nf_smul_right, detPow_gStar, star_star]
  unfold normFock
  rw [hf]

theorem nf_sqAct_adj' {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam x (sqAct ℂ N lam g y) = normFock lam (sqAct ℂ N lam (gStar g) x) y := by
  rw [nf_sqAct_adj, gStar_gStar]

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by have := lam.anti hij; linarith)

theorem extremal_mem {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ∈ nablaSq ℂ N lam :=
  Formalism.GradedWeylDivisibility.hwMem ℂ N N le_rfl lam.natW (natW_anti lam)

theorem extremal_ne {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW

end PI.WGL.Adj
end
end

section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial PI.WGL.Adj

theorem adjointBr_of (h3 : PI.HwIrred) (h5 : PI.SchurFock) (hN : Numbers) (hX : XiFacts) :
    AdjointBr := by
  intro n N h lam sg hI io hio hext hlast
  obtain ⟨hioV, hioEq⟩ := hio
  obtain ⟨hc0, hcB, -⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, hxiV, -, -, -, hxiU⟩ := hX n N h lam sg hI
  obtain ⟨d, b, hbV, hexp⟩ := exists_frame n sg
  have hdel_sg : delSq ℂ n sg = nablaSq ℂ n sg := ((h3 n sg).1).symm
  have hdel_lam : delSq ℂ N lam = nablaSq ℂ N lam := ((h3 N lam).1).symm

  let br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    ∑ k, (nfL lam (io (b k))).smulRight (b k)
  have hbr : ∀ f, br f = ∑ k, normFock lam f (io (b k)) • b k := by
    intro f
    simp [br, LinearMap.sum_apply, LinearMap.smulRight_apply, nfL_apply]
  have hbrV : ∀ f, br f ∈ nablaSq ℂ n sg := by
    intro f
    rw [hbr]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hbV k)
  have hT : ∀ s ∈ nablaSq ℂ n sg, ∀ f, normFock lam (io s) f = normFock sg s (br f) := by
    intro s hs f
    have e := hexp s hs
    calc normFock lam (io s) f = normFock lam (io (∑ k, normFock sg s (b k) • b k)) f := by rw [← e]
      _ = ∑ k, normFock sg s (b k) * normFock lam (io (b k)) f := by
          rw [map_sum]
          simp only [map_smul]
          rw [nf_sum_smul_left]
      _ = normFock sg s (br f) := by
          rw [hbr, nf_sum_smul_right]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← nf_herm, mul_comm]
  have hsep : ∀ x y, x ∈ nablaSq ℂ n sg → y ∈ nablaSq ℂ n sg →
      (∀ s ∈ nablaSq ℂ n sg, normFock sg s x = normFock sg s y) → x = y := by
    intro x y hx hy hxy
    have hd : x - y ∈ nablaSq ℂ n sg := Submodule.sub_mem _ hx hy
    have h0 : normFock sg (x - y) (x - y) = 0 := by rw [nf_sub_right, hxy _ hd, sub_self]
    exact sub_eq_zero.mp (nf_self_eq_zero sg _ h0)

  have hB4 : ∀ (g : GL (Fin n) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ),
      br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f) := by
    intro g f
    refine hsep _ _ (hbrV _) (sqAct_mem_nabla sg g _ (hbrV f)) fun s hs => ?_
    have hs' : sqAct ℂ n sg (gStar g) s ∈ nablaSq ℂ n sg := sqAct_mem_nabla sg _ s hs
    rw [← hT s hs, nf_sqAct_adj' lam (embGL ℂ n N h g) (io s) f, ← embGL_gStar, ← hioEq _ s hs,
      hT _ hs', nf_sqAct_adj' sg g s (br f)]
  have hB5 : ∀ (a : ℂˣ) (f : MvPolynomial (Fin N × Fin N) ℂ),
      br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f := by
    intro a f
    refine hsep _ _ (hbrV _) (Submodule.smul_mem _ _ (hbrV f)) fun s hs => ?_
    rw [← hT s hs, nf_sqAct_adj' lam (lastGL ℂ N a) (io s) f, ← lastGL_cU, hlast _ s hs, nf_smul_left,
      nf_smul_right, hT s hs, cU_zpow_val]

  have hextV : extremal ℂ n sg ∈ nablaSq ℂ n sg := extremal_mem sg
  have hext0 : extremal ℂ n sg ≠ 0 := extremal_ne sg
  let Tm : Module.End ℂ (nablaSq ℂ n sg) :=
    LinearMap.codRestrict (nablaSq ℂ n sg) ((br ∘ₗ io) ∘ₗ (nablaSq ℂ n sg).subtype) (fun x => hbrV _)
  haveI : FiniteDimensional ℂ (nablaSq ℂ n sg) := PI.WHw.bC_fd n n sg.natW
  haveI : Nontrivial (nablaSq ℂ n sg) :=
    ⟨⟨⟨_, hextV⟩, 0, fun h0 => hext0 (congrArg Subtype.val h0)⟩⟩
  obtain ⟨κ, hκ⟩ := Module.End.exists_eigenvalue Tm
  obtain ⟨v, hv⟩ := hκ.exists_hasEigenvector
  have hv1 : br (io (v : MvPolynomial (Fin n × Fin n) ℂ)) = κ • (v : MvPolynomial (Fin n × Fin n) ℂ) := by
    have := Module.End.HasEigenvector.apply_eq_smul hv
    exact congrArg Subtype.val this
  have hv0 : (v : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0 := fun h0 => hv.2 (Subtype.ext h0)
  let U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    nablaSq ℂ n sg ⊓ LinearMap.ker (br ∘ₗ io - κ • LinearMap.id)
  have hmemU : ∀ x, x ∈ U ↔ x ∈ nablaSq ℂ n sg ∧ br (io x) = κ • x := by
    intro x
    simp only [U, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hUst : ∀ (g : GL (Fin n) ℂ), ∀ x ∈ U, sqAct ℂ n sg g x ∈ U := by
    intro g x hx
    rw [hmemU] at hx ⊢
    refine ⟨sqAct_mem_nabla sg g x hx.1, ?_⟩
    rw [hioEq g x hx.1, hB4, hx.2, sqAct_smul]
  have hall : ∀ s ∈ nablaSq ℂ n sg, br (io s) = κ • s := by
    rcases (h3 n sg).2.1 U inf_le_left hUst with hU | hU
    · exfalso
      have hvU : (v : MvPolynomial (Fin n × Fin n) ℂ) ∈ U := (hmemU _).2 ⟨v.2, hv1⟩
      rw [hU, Submodule.mem_bot] at hvU
      exact hv0 hvU
    · intro s hs
      rw [← hU] at hs
      exact ((hmemU s).1 hs).2

  set K := normFock lam (io (extremal ℂ n sg)) (io (extremal ℂ n sg)) with hKdef
  have hnorm : ∀ s ∈ nablaSq ℂ n sg, normFock lam (io s) (io s) = K * normFock sg s s := by
    have hK : star κ = K := by
      have := hT _ hextV (io (extremal ℂ n sg))
      rw [hall _ hextV, nf_smul_right, nf_extremal, mul_one] at this
      exact this.symm
    intro s hs
    rw [hT s hs, hall s hs, nf_smul_right, hK]
  have hKre : K.re = ‖((cBr h lam sg : ℤ) : ℂ)‖ ^ 2 * (normFock lam (xi ℂ h lam sg) (xi ℂ h lam sg)).re := by
    rw [hKdef, hext, PI.GTS.re_normFock_smul]
  have hKreal : K = ((K.re : ℝ) : ℂ) := by rw [hKdef]; exact nf_self_eq_re lam _
  have hcpos : 0 < ‖((cBr h lam sg : ℤ) : ℂ)‖ := by
    rw [norm_pos_iff]; exact_mod_cast hc0
  have hKpos : 0 < K.re := by
    rw [hKre]; exact mul_pos (pow_pos hcpos 2) (nf_self_re_pos lam _ hxi0)
  have hKle : K.re ≤ brBd h lam sg ^ 2 := by
    have hc2 : ‖((cBr h lam sg : ℤ) : ℂ)‖ ^ 2 ≤ cBd h lam sg ^ 2 := by
      have hcn : ‖((cBr h lam sg : ℤ) : ℂ)‖ = |((cBr h lam sg : ℤ) : ℝ)| := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      rw [hcn]
      exact pow_le_pow_left₀ (abs_nonneg _) hcB 2
    have hSF := h5 N lam (xi ℂ h lam sg) hxiV hxiU
    have hbb : brBd h lam sg ^ 2 = cBd h lam sg ^ 2 * (Module.finrank ℂ (delSq ℂ N lam) : ℝ) := by
      unfold brBd; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hKre, hbb]
    exact mul_le_mul hc2 hSF (nf_self_re_nonneg lam _) (sq_nonneg _)
  refine ⟨?_, br, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro s hs
    rw [hnorm s hs, hKreal, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_right hKle (nf_self_re_nonneg sg s)
  ·
    intro f _
    rw [hdel_sg]; exact hbrV f
  ·
    refine ⟨io (extremal ℂ n sg), ?_, ?_⟩
    · rw [hdel_lam]; exact hioV _ hextV
    · intro h0
      have := hT _ hextV (io (extremal ℂ n sg))
      rw [h0, nf_zero_right] at this
      rw [← hKdef] at this
      rw [this] at hKpos
      simp at hKpos
  ·
    intro g f _
    exact hB4 g f
  ·
    intro a f _
    exact hB5 a f
  ·
    intro f _
    set u := br f with hu
    have huV : u ∈ nablaSq ℂ n sg := hbrV f
    have hTu : normFock lam (io u) f = normFock sg u u := hT u huV f
    have hCS := nf_cauchy_schwarz lam (io u) f
    have hnA : ‖normFock sg u u‖ = (normFock sg u u).re := by
      conv_lhs => rw [nf_self_eq_re sg u]
      exact Complex.norm_of_nonneg (nf_self_re_nonneg sg u)
    rw [nf_herm lam (io u) f, hTu, norm_star, hnA, hnorm u huV, hKreal, Complex.re_ofReal_mul] at hCS
    have hA := nf_self_re_nonneg sg u
    have hF := nf_self_re_nonneg lam f
    have hAle : (normFock sg u u).re ≤ K.re * (normFock lam f f).re := by
      rcases hA.lt_or_eq with hApos | hA0
      · refine le_of_mul_le_mul_left ?_ hApos
        nlinarith
      · rw [← hA0]; exact mul_nonneg hKpos.le hF
    calc (normFock sg u u).re ≤ K.re * (normFock lam f f).re := hAle
      _ ≤ brBd h lam sg ^ 2 * (normFock lam f f).re := mul_le_mul_of_nonneg_right hKle hF
  ·
    intro s hs f _
    exact hT s hs f

end PI.WGL
end
end

section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

namespace BrInt

open Formalism.REAL Formalism.GradedWeylDivisibility

section fock

variable {σ : Type}

theorem fockF_add_right (f g g' : MvPolynomial σ ℂ) : fockF f (g + g') = fockF f g + fockF f g' := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [MvPolynomial.coeff_add, star_add]
  ring

theorem fockF_smul_right (c : ℂ) (f g : MvPolynomial σ ℂ) : fockF f (c • g) = star c * fockF f g := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fockF_zero_right (f : MvPolynomial σ ℂ) : fockF f 0 = 0 := by
  unfold fockF
  simp

theorem fockF_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ) (c : ι → ℂ)
    (g : ι → MvPolynomial σ ℂ) :
    fockF f (∑ i ∈ s, c i • g i) = ∑ i ∈ s, star (c i) * fockF f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fockF_zero_right]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_right, fockF_smul_right, ih]

private theorem fockF_eq_sum_of_support_subset (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

theorem brFockF_map (f g : MvPolynomial σ ℚ) :
    fockF (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) g) = ((fockQ f g : ℚ) : ℂ) := by
  rw [fockF_eq_sum_of_support_subset _ _ f.support (MvPolynomial.support_map_subset _ _)]
  unfold fockQ
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [MvPolynomial.coeff_map]

theorem map_ratSmul (q : ℚ) (p : MvPolynomial σ ℚ) :
    map (algebraMap ℚ ℂ) (q • p) = ((q : ℚ) : ℂ) • map (algebraMap ℚ ℂ) p := by
  ext m
  simp [MvPolynomial.coeff_map, MvPolynomial.coeff_smul]

theorem rat_of_pairings {ι : Type*} [Fintype ι] (β : ι → MvPolynomial σ ℚ) (G : MvPolynomial σ ℂ)
    (hG : G ∈ Submodule.span ℂ (Set.range fun i => map (algebraMap ℚ ℂ) (β i)))
    (hq : ∀ i, ∃ q : ℚ, fockF (map (algebraMap ℚ ℂ) (β i)) G = (q : ℂ)) :
    ∃ G0 ∈ Submodule.span ℚ (Set.range β), G = map (algebraMap ℚ ℂ) G0 := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hG
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
  have hπq : ∀ q : ℚ, π (q : ℂ) = q := fun q => by
    have := LinearMap.congr_fun hπ q
    simpa using this
  choose r hr using hq
  set g : ι → MvPolynomial σ ℂ := fun i => map (algebraMap ℚ ℂ) (β i) with hg
  have hgg : ∀ j i, fockF (g j) (g i) = ((fockQ (β j) (β i) : ℚ) : ℂ) := fun j i =>
    brFockF_map (β j) (β i)
  have hrj : ∀ j, (r j : ℂ) = ∑ i, star (c i) * ((fockQ (β j) (β i) : ℚ) : ℂ) := by
    intro j
    rw [← hr j, fockF_sum_right]
    simp only [brFockF_map]
  have hrq : ∀ j, r j = ∑ i, fockQ (β j) (β i) * π (star (c i)) := by
    intro j
    have h1 := congrArg π (hrj j)
    rw [hπq, map_sum] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (c i) * ((fockQ (β j) (β i) : ℚ) : ℂ) = (fockQ (β j) (β i)) • star (c i) := by
      rw [Rat.smul_def, mul_comm]
    rw [this, LinearMap.map_smul, smul_eq_mul]
  set G0 : MvPolynomial σ ℚ := ∑ i, π (star (c i)) • β i with hG0
  have hG0m : map (algebraMap ℚ ℂ) G0 = ∑ i, ((π (star (c i)) : ℚ) : ℂ) • g i := by
    rw [hG0, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_ratSmul]
  set D : MvPolynomial σ ℂ := ∑ i, (c i - ((π (star (c i)) : ℚ) : ℂ)) • g i with hD
  have hDeq : ∑ i, c i • g i - map (algebraMap ℚ ℂ) G0 = D := by
    rw [hG0m, hD, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul]
  have hDj : ∀ j, fockF (g j) D = 0 := by
    intro j
    rw [hD, fockF_sum_right]
    simp only [hgg, star_sub]
    have hs : ∀ i, star (((π (star (c i)) : ℚ) : ℂ)) = ((π (star (c i)) : ℚ) : ℂ) := fun i => by simp
    simp only [hs, sub_mul, Finset.sum_sub_distrib]
    rw [← hrj j, hrq j]
    push_cast
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hDD : fockF D D = 0 := by
    have hjD : ∀ j, fockF D (g j) = 0 := fun j => by
      rw [fockHerm σ (g j) D, hDj j, star_zero]
    conv_lhs => arg 2; rw [hD]
    rw [fockF_sum_right]
    simp [hjD]
  have hD0 : D = 0 := by
    by_contra hne
    have := (fockPos σ D hne).1
    rw [hDD] at this
    simp at this
  refine ⟨G0, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [← sub_eq_zero, hDeq, hD0]

end fock

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have h := lam.anti hij
  simp only [DomWeight.natW]
  omega

private theorem map_initMinor {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    MvPolynomial.map φ (initMinor R I hs) = initMinor S I hs := by
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem map_bidet_int (R : Type) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map (Int.castRingHom R) (bideterminant ℤ sz hsz I) = bideterminant R sz hsz I := by
  unfold bideterminant
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => map_initMinor _ (I k) (hsz k)

theorem mapZC {σ : Type*} (f : MvPolynomial σ ℤ) :
    map (Int.castRingHom ℂ) f = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) f) := by
  rw [MvPolynomial.map_map]
  congr 1

theorem extremal_map {N : ℕ} (lam : DomWeight N) :
    extremal ℂ N lam = map (algebraMap ℚ ℂ) (extremal ℚ N lam) := by
  unfold extremal hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow]
  congr 1
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem normFock_map {N : ℕ} (lam : DomWeight N) (a b : MvPolynomial (Fin N × Fin N) ℚ) :
    normFock lam (map (algebraMap ℚ ℂ) a) (map (algebraMap ℚ ℂ) b) = ((normFockQ lam a b : ℚ) : ℂ) := by
  unfold normFock normFockQ
  rw [brFockF_map, extremal_map, brFockF_map]
  exact (Rat.cast_div _ _).symm

private theorem fockQ_eq_sum_of_support_subset {σ : Type*} (f g : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockQ f g = ∑ m ∈ S, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

theorem normFockQ_symm {N : ℕ} (lam : DomWeight N) (a b : MvPolynomial (Fin N × Fin N) ℚ) :
    normFockQ lam a b = normFockQ lam b a := by
  classical
  unfold normFockQ
  congr 1
  rw [fockQ_eq_sum_of_support_subset a b (a.support ∪ b.support) Finset.subset_union_left,
    fockQ_eq_sum_of_support_subset b a (a.support ∪ b.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

private theorem fockF_eq_sum_lemma {σ : Type*} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

private theorem fockF_swap_eq_star {σ : Type*} [DecidableEq σ] (f g : MvPolynomial σ ℂ) :
    fockF g f = star (fockF f g) := by
  classical
  rw [fockF_eq_sum_lemma g f (f.support ∪ g.support) Finset.subset_union_right,
    fockF_eq_sum_lemma f g (f.support ∪ g.support) Finset.subset_union_left, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', star_star, star_natCast]
  ring

theorem normFock_swap {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam g f = star (normFock lam f g) := by
  unfold normFock
  rw [star_div₀, ← fockF_swap_eq_star f g, ← fockF_swap_eq_star (extremal ℂ N lam) (extremal ℂ N lam)]

theorem fockF_ext_ne {N : ℕ} (lam : DomWeight N) :
    fockF (extremal ℂ N lam) (extremal ℂ N lam) ≠ 0 := by
  rw [extremal_map, brFockF_map]
  have hne : extremal ℚ N lam ≠ 0 := by
    unfold extremal
    exact hwNe ℚ N N le_rfl lam.natW
  have hpos := (fockQPos (Fin N × Fin N) (extremal ℚ N lam) (extremal ℚ N lam)).2 hne
  exact_mod_cast hpos.ne'

end BrInt

open BrInt Formalism.REAL Formalism.GradedWeylDivisibility in
theorem brIntegral_of (h2 : Formalism.BasicNotions.FactDelDualNabla) (h3 : PI.HwIrred) : BrIntegral := by
  intro n N h lam sg hI io br hI1 hI2 hB2 hT f hf
  have hfN : f ∈ nablaSq ℤ N lam := weylLeDual ℤ N N le_rfl lam.natW (natW_anti lam) hf
  have hFd : map (Int.castRingHom ℂ) f ∈ delSq ℂ N lam := by
    rw [← (h3 N lam).1]
    exact dualWeylMap ℤ ℂ (Int.castRingHom ℂ) N N lam.natW f hfN
  have hG : br (map (Int.castRingHom ℂ) f) ∈ nablaSq ℂ n sg := by
    rw [(h3 n sg).1]
    exact hB2 _ hFd
  have hfQ : map (Int.castRingHom ℚ) f ∈ nablaSq ℚ N lam :=
    dualWeylMap ℤ ℚ (Int.castRingHom ℚ) N N lam.natW f hfN
  have hpair : ∀ s ∈ nablaSq ℤ n sg, ∃ z : ℤ,
      normFock sg (map (Int.castRingHom ℂ) s) (br (map (Int.castRingHom ℂ) f)) = (z : ℂ) := by
    intro s hs
    have hsC : map (Int.castRingHom ℂ) s ∈ nablaSq ℂ n sg :=
      dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW s hs
    obtain ⟨fI, hfI, hio⟩ := hI1 s hs
    obtain ⟨z, hz⟩ := (h2 N lam _ hfQ).mpr ⟨f, hf, rfl⟩ fI hfI
    refine ⟨z, ?_⟩
    rw [← hT _ hsC _ hFd, hio, mapZC fI, mapZC f, normFock_map, normFockQ_symm, hz]
    push_cast
    rfl
  have : Fintype (ssIdx n n sg.natW) := (sSIdxFinite n n sg.natW).fintype
  obtain ⟨b, hWB, hb⟩ := sSBasis ℂ n n sg.natW
  have hb' : ∀ m : ssIdx n n sg.natW, ∃ p : MvPolynomial (Fin n × Fin n) ℤ,
      p ∈ nablaSq ℤ n sg ∧ map (Int.castRingHom ℂ) p = b m := by
    intro m
    obtain ⟨K, sz, hsz, I, hsh, -, hbm⟩ := (hb m).2.2
    refine ⟨bideterminant ℤ sz hsz I, ?_, ?_⟩
    · have := bidetMem ℤ n n K sz hsz I
      rw [hsh] at this
      exact this
    · rw [hbm, map_bidet_int]
  choose p hp hpb using hb'
  have hbeq : (fun m => map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) (p m))) = b := by
    funext m
    rw [← mapZC, hpb]
  have hspan : br (map (Int.castRingHom ℂ) f) ∈
      Submodule.span ℂ (Set.range fun m => map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) (p m))) := by
    rw [hbeq, hWB.2.1]
    exact hG
  have hq : ∀ m, ∃ q : ℚ, fockF (map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) (p m)))
      (br (map (Int.castRingHom ℂ) f)) = (q : ℂ) := by
    intro m
    obtain ⟨z, hz⟩ := hpair (p m) (hp m)
    refine ⟨z * fockQ (extremal ℚ n sg) (extremal ℚ n sg), ?_⟩
    unfold normFock at hz
    rw [div_eq_iff (fockF_ext_ne sg), mapZC] at hz
    rw [hz, extremal_map, brFockF_map]
    push_cast
    rfl
  obtain ⟨G0, hG0s, hG0⟩ := rat_of_pairings _ _ hspan hq
  have hG0N : G0 ∈ nablaSq ℚ n sg := by
    refine (Submodule.span_le.mpr ?_) hG0s
    rintro _ ⟨m, rfl⟩
    exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) n n sg.natW (p m) (hp m)
  obtain ⟨f0, hf0, hf0eq⟩ := (h2 n sg G0 hG0N).mp (by
    intro g hg
    obtain ⟨z, hz⟩ := hpair g hg
    refine ⟨z, ?_⟩
    apply (Rat.cast_injective (α := ℂ))
    rw [← normFock_map, ← hG0, ← mapZC, normFock_swap, hz]
    simp)
  refine ⟨f0, hf0, ?_⟩
  rw [hG0, ← hf0eq, ← mapZC]

end PI.WGL
end
end

section
noncomputable section

namespace PI.WGL

theorem gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) (h3 : PI.HwIrred) (h4 : PI.GTBranch)
    (h5 : PI.SchurFock) : PI.GTLower := by
  have hN : Numbers := numbers_dominant_large
  have hX : XiFacts := xi_coefficient_facts
  have hZ : CapelliZ := capelli_scalar_identity
  have hV : ZScalarVanish := scalar_vanishing_criterion
  exact gTLower_of_steps hN hX (ioExists_of h3 h4 hX)
    (ioIntegral_of hZ (liftMod_of h3 h4 hZ hV hN hX) hV)
    (adjointBr_of h3 h5 hN hX) (brIntegral_of h2 h3)

end PI.WGL
end
end
