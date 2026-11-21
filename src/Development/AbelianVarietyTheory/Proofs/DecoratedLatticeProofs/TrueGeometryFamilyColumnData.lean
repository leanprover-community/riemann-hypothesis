import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRootOfSUnitRatioUpToRootOfUnityClosureLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleFamilyPeriodEqPeriod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumWithLatKerEqMulSumWithKerLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientPara
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataUnitShiftRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeFramePinsFiniteIntegralLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonzeroScalarsRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankOneGramRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuadraticFamilyLevelIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueFamilyTopRowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealEqualityOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainIdealIndexProductStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteLiftCommLevelPrimeOperators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyRowsColumnsValidStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftsAllChartsEqClassSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MvZOneEqMapUnivSubst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastPeriodFactorizationOfClassData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInvertibleFamilyEvalSpan
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedThetaLiftCommutesSplitPlaceOperators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivariance
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelsCommuteTwisted
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwistStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelationStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRootOfSUnitRatioUpToRootOfUnity_closure_laws : ∀ S : ℕ → Prop, (∀ y : ℂ, y ≠ 0 → UnitRatio S y y) ∧ (∀ x y x' y' : ℂ, UnitRatio S x y → UnitRatio S x' y' → UnitRatio S (x * x') (y * y') ∧ UnitRatio S (x / x') (y / y') ∧ x ≠ 0) ∧ (∀ (x y : ℂ) (n : ℕ), y ≠ 0 → 0 < n → x ^ n = y ^ n → UnitRatio S x y) ∧ ∀ (I : Type) (s : Finset I) (x y : I → ℂ), (∀ i ∈ s, UnitRatio S (x i) (y i)) → UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) := by
  first | exact @GlobalTheory.Fam.unitRatio_laws | exact GlobalTheory.Fam.unitRatio_laws | (intros; apply GlobalTheory.Fam.unitRatio_laws <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

private theorem list_prod_map_pow_eq {α : Type} (l : List α) (f g : α → ℂ) (n : ℕ) (h : ∀ a, f a ^ n = g a ^ n) :
    (l.map f).prod ^ n = (l.map g).prod ^ n := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, mul_pow, ih, h]

private theorem list_prod_map_ne_zero {α : Type} (l : List α) (f : α → ℂ) (h : ∀ a, f a ≠ 0) :
    (l.map f).prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons]; exact mul_ne_zero (h a) ih

theorem mono_pow_eq {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ)
    (χ χ' : (AE D)ˣ →* Circle) (n : ℕ) (hn : χ ^ n = χ' ^ n) :
    o.mono r e χ ^ n = o.mono r e χ' ^ n := by
  unfold TDat.mono
  apply list_prod_map_pow_eq
  intro i
  simp only [mul_pow, chrPow]
  congr 1
  have key : ∀ μ : (AE D)ˣ →* Circle, ((μ ((o.p i).idele o.q.unit) ^ e i : Circle) : ℂ) ^ n
      = ((((μ ^ n) ((o.p i).idele o.q.unit)) ^ e i : Circle) : ℂ) := by
    intro μ
    rw [MonoidHom.pow_apply, ← Circle.coe_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  rw [key χ, key χ', hn]

theorem mono_ne_zero {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ)
    (χ : (AE D)ˣ →* Circle) (hr : ∀ i, 0 < r i) : o.mono r e χ ≠ 0 := by
  unfold TDat.mono
  apply list_prod_map_ne_zero
  intro i
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast (hr i).ne'
  · exact Circle.coe_ne_zero _

theorem mono_unitRatio : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ) (χ χ' : (AE D)ˣ →* Circle)
    (S : ℕ → Prop), (∀ i, 0 < r i) → (∃ n : ℕ, 0 < n ∧ χ ^ n = χ' ^ n) → UnitRatio S (o.mono r e χ) (o.mono r e χ') := by
  intro D c k _ _ _ _ ι o r e χ χ' S hr ⟨n, hn, hχ⟩
  exact (GlobalTheory.T.isRootOfSUnitRatioUpToRootOfUnity_closure_laws S).2.2.1 _ _ n (mono_ne_zero o r e χ' hr) hn (mono_pow_eq o r e χ χ' n hχ)

end GlobalTheory.SeeSaw
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RamUnit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def pet (vS : Vol S) (ψ ψ' : Form k n (GA D S → ℂ)) (P : Pair k n) : ℂ :=
  ∫ g in vS.𝓕, ψ P g * star (ψ' P g) ∂vS.μ

theorem rep_apply (β : Frame p S n) (g : GL n k) (f : GA D S → ℂ) (x : GA D S) :
    β.rep g f x = f (x * β.gl g) := rfl

theorem pet_const (vS : Vol S) (β : Frame p S n) {ψ ψ' : Form k n (GA D S → ℂ)} (hψ : ψ ∈ EqForm β.rep)
    (hψ' : ψ' ∈ EqForm β.rep) (hl : ∀ P, ∀ γ ∈ GQ S, ∀ g, ψ P (γ * g) = ψ P g)
    (hl' : ∀ P, ∀ γ ∈ GQ S, ∀ g, ψ' P (γ * g) = ψ' P g) (P Q : Pair k n) : pet vS ψ ψ' P = pet vS ψ ψ' Q := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
  unfold pet
  rw [hψ g P, hψ' g P]
  simp only [rep_apply]
  exact (GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S vS.μ vS.𝓕 vS.haar vS.fund (fun x => ψ P x * star (ψ' P x))
    (fun γ hγ x => by simp only [hl P γ hγ, hl' P γ hγ]) (β.gl g)).symm

theorem sum_pet_FFStar (vS : Vol S) (hS : CoCpt S) (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    (hχ : ∀ a, (starRingEnd ℂ) (χ a) = χ (-a))
    {φ ψ : Form k n (GA D S → ℂ)} (hφ : ∀ P, IsContAut S (φ P)) (hψ : ∀ P, IsContAut S (ψ P))
    (L : Submodule 𝒪[k] (n → k)) :
    ∑ P ∈ withLat L, pet vS (FFStar q χ φ) ψ P = ∑ P₁ ∈ withKer L, pet vS φ (FF q χ ψ) P₁ := by
  have hint : ∀ P₁ P, IntegrableOn (fun g => φ P₁ g * star (ψ P g)) vS.𝓕 vS.μ := fun P₁ P =>
    (GlobalTheory.CocompactParam.continuous_integral_param D S hS vS Unit (fun g _ => φ P₁ g * star (ψ P g))
      (((hφ P₁).2.mul (hψ P).2.star).comp continuous_fst)
      (fun γ hγ g _ => by simp only [(hφ P₁).1 γ hγ, (hψ P).1 γ hγ])).1 ()
  have e1 : ∀ P ∈ withLat L, pet vS (FFStar q χ φ) ψ P =
      ∑ P₁ ∈ withKer L, χ (-cross q P₁ P) * ∫ g in vS.𝓕, φ P₁ g * star (ψ P g) ∂vS.μ := by
    intro P hP
    rw [mem_withLat] at hP
    unfold pet
    rw [FFStar_apply, hP]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [integral_finset_sum _ (fun P₁ _ => (hint P₁ P).const_mul _)]
    exact Finset.sum_congr rfl fun P₁ _ => integral_const_mul _ _
  have e2 : ∀ P₁ ∈ withKer L, pet vS φ (FF q χ ψ) P₁ =
      ∑ P ∈ withLat L, χ (-cross q P₁ P) * ∫ g in vS.𝓕, φ P₁ g * star (ψ P g) ∂vS.μ := by
    intro P₁ hP₁
    rw [mem_withKer] at hP₁
    unfold pet
    rw [FF_apply, hP₁]
    have : ∀ g, φ P₁ g * star ((∑ P ∈ withLat L, χ (cross q P₁ P) • ψ P) g) =
        ∑ P ∈ withLat L, χ (-cross q P₁ P) * (φ P₁ g * star (ψ P g)) := fun g => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, Finset.mul_sum, star_mul']
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [← hχ]
      change φ P₁ g * ((starRingEnd ℂ) (χ (cross q P₁ P)) * star (ψ P g)) = _
      ring
    simp only [this]
    rw [integral_finset_sum _ (fun P _ => (hint P₁ P).const_mul _)]
    exact Finset.sum_congr rfl fun P _ => integral_const_mul _ _
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]

end GlobalTheory.FinPl.RamUnit

namespace GlobalTheory.FinPl.RamUnit

theorem ramUnitary_holds : ∀ D : D7, GlobalTheory.FinPl.RamUnitary D := by
  intro D k _ _ _ _ p n _ _ q χ hχ ε S hS vS β P φ₀ φ₀' hφ₀ hφ₀'
  obtain ⟨φ, hφ, rfl⟩ := hφ₀
  obtain ⟨φ', hφ', rfl⟩ := hφ₀'
  have hB := GlobalTheory.FinPl.ramBijective_holds D k p n q χ hχ (resChar χ hχ q) rfl ε S β P
  obtain ⟨hA, eA⟩ := hB.2.1 φ hφ
  obtain ⟨hA', eA'⟩ := hB.2.1 φ' hφ'
  rw [eA, eA']
  have hO : OperatorIdentities k n (GA D S → ℂ) q (resChar χ hχ q) :=
    ((GlobalTheory.PairOp.pairOperatorStatement k q χ hχ n).1 (GA D S → ℂ)).2
  set X := FFStar q (resChar χ hχ q) φ with hX
  set X' := FFStar q (resChar χ hχ q) φ' with hX'
  have cX : ∀ Q, IsContAut S (X Q) := fun Q => by
    have := hA.2.2 (ε⁻¹ • Q)
    rwa [dia_apply, smul_inv_smul] at this
  have cX' : ∀ Q, IsContAut S (X' Q) := fun Q => by
    have := hA'.2.2 (ε⁻¹ • Q)
    rwa [dia_apply, smul_inv_smul] at this
  have eFF : FF q (resChar χ hχ q) X' = ((resCard k : ℂ) ^ Fintype.card n) • φ' := hO.FF_FFStar_ram φ' hφ'.2.1
  have c2 : ∀ Q, IsContAut S ((FF q (resChar χ hχ q) X') Q) := fun Q => by
    rw [eFF]
    exact ⟨fun γ hγ g => by simp only [Pi.smul_apply, smul_eq_mul, (hφ'.2.2 Q).1 γ hγ],
      continuous_const.mul (hφ'.2.2 Q).2⟩
  have hsum := sum_pet_FFStar vS hS q (resChar χ hχ q) (conj_resChar hχ q) hφ.2.2 cX' P.lat
  have k1 : ∀ Q ∈ withLat P.lat, pet vS X X' Q = pet vS X X' (ε • P) := fun Q _ =>
    pet_const vS β (FFStar_mem_EqForm q _ hφ.1) (FFStar_mem_EqForm q _ hφ'.1) (fun Q => (cX Q).1)
      (fun Q => (cX' Q).1) Q (ε • P)
  have k2 : ∀ Q ∈ withKer P.lat, pet vS φ (FF q (resChar χ hχ q) X') Q = pet vS φ (FF q (resChar χ hχ q) X') P :=
    fun Q _ => pet_const vS β hφ.1 (FF_mem_EqForm q _ (FFStar_mem_EqForm q _ hφ'.1)) (fun Q => (hφ.2.2 Q).1)
      (fun Q => (c2 Q).1) Q P
  rw [Finset.sum_congr rfl k1, Finset.sum_congr rfl k2, Finset.sum_const, Finset.sum_const,
    ← card_withLat_eq_card_withKer] at hsum
  have hN : (withLat P.lat).card ≠ 0 := (Finset.card_pos.2 ⟨P, mem_withLat.2 rfl⟩).ne'
  have hpe : pet vS X X' (ε • P) = pet vS φ (FF q (resChar χ hχ q) X') P := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hsum
    exact smul_right_injective ℂ (Nat.cast_ne_zero.2 hN) hsum
  change pet vS X X' (ε • P) = _
  rw [hpe, eFF]
  unfold pet
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_pow, Complex.star_def, Complex.conj_natCast]
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

end GlobalTheory.FinPl.RamUnit
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem ratio_total_unitRatio_of_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)) (S : 𝒯 → ℕ → Prop) (s₀ : 𝒯), (∀ s, (t s).Is) → (∀ s, CVEq v (w s)) → (∀ j σ h, v.kap j σ h ≠ 0) → (∀ j, v.cG j ≠ 0) → (∀ s j, j < D.R.m → UnitRatio (S s) ((w s).sc j) ((w s₀).sc j) ∧ UnitRatio (S s) ((t s).cK j) ((t s₀).cK j)) → (∀ s j ρ, j + 2 * ρ + 2 = D.R.m → UnitRatio (S s) ((w s).cT j) ((w s₀).cT j) ∧ UnitRatio (S s) ((w s).cQ j / ((t s).cI j * (t s).cI (j + 1))) ((w s₀).cQ j / ((t s₀).cI j * (t s₀).cI (j + 1)))) → (∀ s, UnitRatio (S s) (t s).cP (t s₀).cP) → ∀ n, 2 * n = D.R.m → ∀ s, (t s).cTop n ≠ 0 ∧ (t s).cBot ≠ 0 ∧ UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
  intro D c v 𝒯 t w S s₀ hIs hCV hkap hcG hscK hTQ hcP n hn s
  obtain ⟨hrefl, hmul, -, hprod⟩ := GlobalTheory.Fam.unitRatio_laws (S s)
  have split : ∀ (f : ℕ → ℂ) (k : ℕ), ∏ j ∈ Finset.range (2 * k), f j =
      ∏ i ∈ Finset.range k, (f (2 * i) * f (2 * i + 1)) := by
    intro f k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
        Finset.prod_range_succ, mul_assoc]
  have hIs' : ∀ s j, j < D.R.m → (t s).cI j ≠ 0 := fun s j hj => (hIs s).cI j hj
  have hκ : ∀ i, i < n → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ s, (t s).cV (2 * i) =
      κ * ((w s).sc (2 * i) * (w s).sc (2 * i + 1)) * (w s).cQ (2 * i) * v.cG (2 * i) * (w s).cT (2 * i) := by
    intro i hi
    by_cases hlast : i + 1 = n
    · refine ⟨1, one_ne_zero, fun s => ?_⟩
      rw [one_mul]
      exact (hCV s).2 (2 * i) (by omega)
    · exact ⟨v.kap (2 * i) (n - i - 2) (by omega), hkap _ _ _, fun s => (hCV s).1 (2 * i) (n - i - 2) (by omega)⟩
  have hB : ∀ i, i < n → UnitRatio (S s)
      ((t s).cV (2 * i) * (t s).cK (2 * i) * (t s).cK (2 * i + 1) / ((t s).cI (2 * i) * (t s).cI (2 * i + 1)))
      ((t s₀).cV (2 * i) * (t s₀).cK (2 * i) * (t s₀).cK (2 * i + 1) / ((t s₀).cI (2 * i) * (t s₀).cI (2 * i + 1))) := by
    intro i hi
    obtain ⟨κ, hκ0, hκs⟩ := hκ i hi
    have hK0 : κ * v.cG (2 * i) ≠ 0 := mul_ne_zero hκ0 (hcG _)
    have hform : ∀ s', (t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) /
        ((t s').cI (2 * i) * (t s').cI (2 * i + 1)) =
        κ * v.cG (2 * i) *
          ((w s').sc (2 * i) * (w s').sc (2 * i + 1) * (w s').cT (2 * i) *
            ((w s').cQ (2 * i) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1))) *
            ((t s').cK (2 * i) * (t s').cK (2 * i + 1))) := by
      intro s'
      rw [hκs s']
      ring
    rw [hform s, hform s₀]
    have hsc1 := (hscK s (2 * i) (by omega)).1
    have hsc2 := (hscK s (2 * i + 1) (by omega)).1
    have homogComponent_comm_first_action := (hscK s (2 * i) (by omega)).2
    have homogComponent_comm_second_action := (hscK s (2 * i + 1) (by omega)).2
    have hcT := (hTQ s (2 * i) (n - i - 1) (by omega)).1
    have hcQ := (hTQ s (2 * i) (n - i - 1) (by omega)).2
    exact (hmul _ _ _ _ (hrefl _ hK0)
      (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ hsc1 hsc2).1 hcT).1 hcQ).1
        (hmul _ _ _ _ homogComponent_comm_first_action homogComponent_comm_second_action).1).1).1
  have hq : ∀ s', (t s').cTop n / (t s').cBot = (∏ i ∈ Finset.range n,
      ((t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1)))) *
      (t s').cP := by
    intro s'
    unfold Tup.cTop Tup.cBot
    rw [← hn, split (fun j => (t s').cI j) n, Finset.prod_div_distrib]
    ring
  have hall : UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
    rw [hq s, hq s₀]
    exact (hmul _ _ _ _ (hprod ℕ (Finset.range n) _ _ fun i hi => hB i (Finset.mem_range.mp hi)) (hcP s)).1
  have hbot : (t s).cBot ≠ 0 := by
    unfold Tup.cBot
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hIs' s j (Finset.mem_range.mp hj)
  have hne := (hmul _ _ _ _ hall hall).2.2
  refine ⟨fun h0 => hne ?_, hbot, hall⟩
  rw [h0, zero_div]

end GlobalTheory.SeeSaw
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_totalConstant_ratio_of_factor_ratios : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)) (S : 𝒯 → ℕ → Prop) (s₀ : 𝒯), (∀ s, (t s).Is) → (∀ s, CVEq v (w s)) → (∀ j σ h, v.kap j σ h ≠ 0) → (∀ j, v.cG j ≠ 0) → (∀ s j, j < D.R.m → UnitRatio (S s) ((w s).sc j) ((w s₀).sc j) ∧ UnitRatio (S s) ((t s).cK j) ((t s₀).cK j)) → (∀ s j ρ, j + 2 * ρ + 2 = D.R.m → UnitRatio (S s) ((w s).cT j) ((w s₀).cT j) ∧ UnitRatio (S s) ((w s).cQ j / ((t s).cI j * (t s).cI (j + 1))) ((w s₀).cQ j / ((t s₀).cI j * (t s₀).cI (j + 1)))) → (∀ s, UnitRatio (S s) (t s).cP (t s₀).cP) → ∀ n, 2 * n = D.R.m → ∀ s, (t s).cTop n ≠ 0 ∧ (t s).cBot ≠ 0 ∧ UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
  atlas_forward_decl GlobalTheory.SeeSaw.ratio_total_unitRatio_of_parts
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteLift_comm_levelPrimeOperators : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom c) (o : TDat c k ι) (t : Tup c) (w : VTup t), LiftExact D → c.Is → t.Is → v.Is → VForm v w → ShapeOff v o → (∀ j, j < D.R.m → ∃ μ, IsWeilDatumO c.ψ _ _ μ μ (t.kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v) → LiftS o t := by
  first | exact @GlobalTheory.SeeSaw.liftS_of_exact | exact GlobalTheory.SeeSaw.liftS_of_exact | (intros; apply GlobalTheory.SeeSaw.liftS_of_exact <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem kerX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → KerX t := by
  intro D c 𝒯 t hc ht hP
  obtain ⟨ρ, hρ, hA⟩ := hP
  intro j hj y P
  have hj1 : j + 1 ≤ D.R.m := hj
  obtain ⟨hpos, hab⟩ := hρ.rk j hj
  obtain ⟨hB, ν, hν1, hνL, hmain⟩ := GlobalTheory.T.thetaLifts_all_charts_eq_classSum D c ρ hc hρ j hj1 hab
  obtain ⟨m', y', s, hinv, havg⟩ := @GlobalTheory.KJAvg.avg_span D.what₂.Tau _ (ρ.N j) (ρ.N (j + 1)) hab hpos (ρ.lam j) (ρ.n j)
    (GinfC (c.X j)) _ _ _ _ hB ν hν1 hνL (fun k τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ) (hρ.uni j _) (ρ.fr j y).1
    (castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) P)
  have hz : ∀ i, ∀ τ, IsUnit ((fun τ => ρ.sc j τ • y' i τ) τ).det := by
    intro i τ
    simp only [Matrix.det_smul]
    exact (IsUnit.pow _ (Ne.isUnit (hρ.sc j τ))).mul (hinv i τ)
  let z : Fin m' → FrN D (ρ.N (j + 1)) := fun i => ⟨fun τ => ρ.sc j τ • y' i τ, hz i⟩
  let y'' : Fin m' → c.Fr (j + 1) := fun i => (ρ.fr (j + 1)).symm (z i)
  let cst : ℂ := ∏ τ, ((ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)
  have key := hmain 1 (fun _ => y) (fun _ => P) m' y' y'' (fun i => cst * s i)
    (by intro i τ; simp only [y'', Equiv.apply_symm_apply]; rfl)
    (by
      intro F hF Λ
      rw [Fin.sum_univ_one, havg F hF Λ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
  refine ⟨∑ i, Finsupp.single (y'' i) (cst * s i * ∏ τ, ((ρ.fr (j + 1) (y'' i)).1 τ).det ^ ρ.sD j τ), ?_⟩
  intro s' ψ hψ γ
  obtain ⟨⟨A, hA'⟩, _⟩ := hA s'
  have h1 := key (t s') A (ht s') hA' ψ hψ γ
  rw [Fin.sum_univ_one] at h1
  rw [h1]
  congr 1
  change _ = Finsupp.sum _ (fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y')
  rw [← Finsupp.sum_finset_sum_index (h := fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y')
    (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_single_index (h := fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y') (zero_smul ℂ _)]

end GlobalTheory.SeeSaw
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawKernelLiftCombination_of_definiteClassData : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → KerX t := by
  atlas_forward_decl GlobalTheory.SeeSaw.kerX_of_clsPinD
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem RealD.r_center_scalar {c : Comm D} (ρ : RealD c) (hρ : ρ.Is) (j : ℕ) (hj : j ≤ D.R.m) {z : GA D (c.X j)}
    (hz : z ∈ GinfC (c.X j)) (hzc : z ∈ Subgroup.center (GA D (c.X j))) (τ : D.what₂.Tau) :
    ρ.r j hj z τ = (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) • (1 : Matrix (Fin (ρ.N j)) (Fin (ρ.N j)) ℂ) := by
  have hu := hρ.uni j hj
  obtain ⟨ζ, hζ⟩ := GlobalTheory.CenterScalar.scalar_of_comm_unitary (ρ.r j hj z τ) fun U hU => by
    obtain ⟨k, hk⟩ := hu.onto (fun _ => U) fun _ => (Matrix.mem_unitaryGroup_iff').2 hU
    have e1 := hu.mul k ⟨z, hz⟩ τ
    have e2 := hu.mul ⟨z, hz⟩ k τ
    have hkz : (k * ⟨z, hz⟩ : GinfC (c.X j)) = ⟨z, hz⟩ * k :=
      Subtype.ext ((Subgroup.mem_center_iff.1 hzc) k.1)
    rw [hkz, e2] at e1
    have hk' : ρ.r j hj k.1 τ = U := congrFun hk τ
    rw [hk'] at e1
    exact e1.symm
  rcases Nat.eq_zero_or_pos (ρ.N j) with h0 | hpos
  · ext a
    exact absurd a.2 (by omega)
  · rw [hζ, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
      mul_div_assoc, div_self (by exact_mod_cast hpos.ne'), mul_one]

theorem rdX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → RdX t := by
  intro D c 𝒯 t hc _ hP j hj
  obtain ⟨ρ, hρ, H⟩ := hP
  refine ⟨fun z => ∏ τ, (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) ^ (∑ i, (ρ.lam j τ).w i), fun s ψ hψ α y => ?_⟩
  obtain ⟨⟨A, hA⟩, -⟩ := H s
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c (t s) ρ A hc hρ hA.1 j hj ψ hψ α
  refine ⟨h1 y, fun z hz hzc g => ?_⟩
  have hdet : ∀ τ, IsUnit (ρ.r j hj z τ).det := fun τ =>
    Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 ((hρ.uni j hj).uni ⟨z, hz⟩ τ))
  set w := (ρ.fr j y).tr (ρ.r j hj z) hdet with hw
  have e1 : (t s).rd j α ψ y (g * z) = (t s).rd j α ψ ((ρ.fr j).symm w) g :=
    h3 y _ g z hz (by rw [Equiv.apply_symm_apply]; exact Frames.isTr_tr _ hdet _)
  have e2 := (GlobalTheory.KJInf.valC_poly _ _ _ _ |>.2.2.2) _ (h4 g) (fun τ => Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) (ρ.fr j y) w
    (fun τ => by
      show ρ.r j hj z τ * (ρ.fr j y).1 τ = _
      conv_lhs => rw [ρ.r_center_scalar hρ j hj hz hzc τ]
      rw [Matrix.smul_mul, Matrix.one_mul])
  simp only [Equiv.symm_apply_apply] at e2
  rw [e1, e2]

end GlobalTheory.SeeSaw
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_scalarForms_continuous_automorphic_central : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → RdX t := by
  atlas_forward_decl GlobalTheory.SeeSaw.rdX_of_clsPinD
end

section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invertibleFamily_eval_span : ∀ (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (T : PY ι a →ₗ[ℂ] W), ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → W), (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, T F = ∑ j, evalAt (y j) F • P j := by
  first | exact @GlobalTheory.KJInf.exists_evalAt_span | exact GlobalTheory.KJInf.exists_evalAt_span | (intros; apply GlobalTheory.KJInf.exists_evalAt_span <;> assumption)
end

section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf
variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem continuous_lin_mvZ {T : Type} [TopologicalSpace T] (g : T → ι → Matrix (Fin a) (Fin a) ℂ)
    (hg : Continuous g) (h : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b) :
    ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, Continuous fun x => Λ (mvZ (g x) h P) := by
  induction P using MvPolynomial.induction_on with
  | C c => intro Λ; simp only [mvZ, aeval_C, algebraMap_eq]; exact continuous_const
  | add p q hp hq => intro Λ; simp only [map_add]; exact (hp Λ).add (hq Λ)
  | mul_X p v hp =>
    intro Λ
    have key : ∀ x, Λ (mvZ (g x) h (p * X v)) = ∑ i, ∑ j, (h v.1 i v.2.1 * g x v.1 v.2.2 j) *
        (Λ ∘ₗ LinearMap.mulRight ℂ (X (v.1, i, j))) (mvZ (g x) h p) := by
      intro x
      rw [map_mul]
      conv_lhs => rw [show mvZ (g x) h (X v) = ∑ i, ∑ j, C (h v.1 i v.2.1 * g x v.1 v.2.2 j) * X (v.1, i, j) by simp [mvZ, aeval_X]]
      simp only [Finset.mul_sum, map_sum, LinearMap.comp_apply, LinearMap.mulRight_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [C_mul', mul_smul_comm, map_smul, smul_eq_mul]
    simp_rw [key]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    refine Continuous.mul (continuous_const.mul ?_) (hp _)
    exact ((continuous_apply j).comp ((continuous_apply v.2.2).comp ((continuous_apply v.1).comp hg)))

theorem continuous_evalAt_mul (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ => evalAt (fun τ => u τ * y τ) F := by
  unfold evalAt
  refine (MvPolynomial.continuous_eval F).comp (continuous_pi fun x => ?_)
  exact (((continuous_apply x.1).matrix_mul continuous_const).matrix_elem x.2.1 x.2.2)

theorem isCompact_entries_le_one :
    IsCompact {u : ι → Matrix (Fin a) (Fin a) ℂ | ∀ τ i j, ‖u τ i j‖ ≤ 1} := by
  have : {u : ι → Matrix (Fin a) (Fin a) ℂ | ∀ τ i j, ‖u τ i j‖ ≤ 1} =
      Set.univ.pi fun _ : ι => (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a => Metric.closedBall (0:ℂ) 1 : Set (Matrix (Fin a) (Fin a) ℂ)) := by
    ext u
    constructor
    · intro hu τ _ i _ j _
      have := hu τ i j
      show dist (u τ i j) 0 ≤ 1
      simpa using this
    · intro hu τ i j
      have : dist (u τ i j) 0 ≤ 1 := hu τ trivial i trivial j trivial
      simpa using this
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem subY_eq_sum_averages : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b) (lam : ι → DomWeight a) (n : ι → ℕ) (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] (r : K → ι → Matrix (Fin a) (Fin a) ℂ), OntoUni r → ∀ y' : ι → Matrix (Fin b) (Fin b) ℂ, ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → FP ι a b), (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, ∑ j, ∫ k, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F ∂ν = Λ (subY hab y' F) := by
  intro ι _ a b hab lam n K _ _ _ _ _ ν _ r hr y'
  obtain ⟨m, y, P, hy, hT⟩ := GlobalTheory.T.exists_invertibleFamily_eval_span ι a lam n (FP ι a b) (subY hab y').toLinearMap
  refine ⟨m, y, P, hy, ?_⟩
  intro F hF Λ
  obtain ⟨h1, -, -, h4, h5, h6, -, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  have vn := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam n).2
  have hstar : ∀ k τ, star (r k τ) * r k τ = 1 := fun k τ => (Matrix.mem_unitaryGroup_iff').1 (hr.uni k τ)
  have hstar' : ∀ k τ, r k τ * star (r k τ) = 1 := fun k τ => (Matrix.mem_unitaryGroup_iff).1 (hr.uni k τ)
  have hinv : ∀ k τ, (r k τ)⁻¹ = star (r k τ) := fun k τ => Matrix.inv_eq_left_inv (hstar k τ)
  have hpt : ∀ k, ∑ j, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F
      = Λ (subY hab y' F) := by
    intro k
    have hG : subY hab y' (lft (r k) F) = ∑ j, evalAt (y j) (lft (r k) F) • P j := hT _ (vn (r k) F hF)
    have e1 : mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (subY hab y' (lft (r k) F)) = subY hab y' F := by
      rw [h1, h4]
      have ha : (fun τ => r k τ * (r k τ)⁻¹) = fun _ => (1 : Matrix (Fin a) (Fin a) ℂ) := by
        funext τ; rw [hinv, hstar']
      have hb : (fun τ => (1 : Matrix (Fin b) (Fin b) ℂ) * y' τ) = y' := by funext τ; simp
      rw [ha, hb, h5]
    rw [← e1, hG, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, h6, mul_comm]
  have hst : Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ => fun τ => star (u τ) := continuous_pi fun τ => (continuous_apply τ).star
  have hcont : ∀ j, Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ =>
      Λ (mvZ (fun τ => star (u τ)) (fun _ => 1) (P j)) * evalAt (fun τ => u τ * y j τ) F := fun j => by
    have e1 := continuous_lin_mvZ (fun u : ι → Matrix (Fin a) (Fin a) ℂ => fun τ => star (u τ)) hst (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) (P j) Λ
    exact e1.mul (continuous_evalAt_mul (y j) F)
  have hint : ∀ j ∈ Finset.univ, Integrable (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) *
      evalAt (fun τ => r k τ * y j τ) F) ν := by
    intro j _
    have hfun : (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F)
        = (fun u : ι → Matrix (Fin a) (Fin a) ℂ =>
          Λ (mvZ (fun τ => star (u τ)) (fun _ => 1) (P j)) * evalAt (fun τ => u τ * y j τ) F) ∘ r := by
      funext k; simp only [Function.comp_apply, hinv]
    rw [hfun]
    obtain ⟨C, hC⟩ := (isCompact_entries_le_one (ι := ι) (a := a)).exists_bound_of_continuousOn (hcont j).continuousOn
    refine Integrable.of_bound ((hcont j).comp hr.cont).aestronglyMeasurable C (Filter.Eventually.of_forall fun k => ?_)
    exact hC _ fun τ i i' => entry_norm_bound_of_unitary (hr.uni k τ) i i'
  rw [← integral_finset_sum _ hint]
  simp_rw [hpt]
  simp

end GlobalTheory.KJInf

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem castP_surjective {D : D7} {p q a b : ℕ} (hp : p = a) (hq : q = b) (Q : FP D.what₂.Tau a b) :
    ∃ P : PolF D q p, castP hp hq P = Q := by
  subst hp; subst hq
  refine ⟨Q, ?_⟩
  show MvPolynomial.rename _ Q = Q
  have : (fun v : D.what₂.Tau × Fin q × Fin p => (v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2)) = id := by
    funext v; simp
  rw [this, MvPolynomial.rename_id_apply]

theorem kBack_of_classData : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → t.Is → ρ.Is → A.Is →
    (∀ j, j < D.R.m → t.cK j ≠ 0) → t.KBack := by
  intro D c t ρ A hc ht hρ hA hK j hj
  refine ⟨hK j hj, fun w => ?_⟩
  have hj1 : j + 1 ≤ D.R.m := hj
  have hab : ρ.N j ≤ ρ.N (j + 1) := (hρ.rk j hj).2
  obtain ⟨hB, ν, hν, -, hL⟩ := GlobalTheory.T.thetaLifts_all_charts_eq_classSum D c ρ hc hρ j hj1 hab
  haveI := hB
  haveI := hν
  set z : D.what₂.Tau → Matrix (Fin (ρ.N (j + 1))) (Fin (ρ.N (j + 1))) ℂ :=
    fun τ => (ρ.sc j τ)⁻¹ • (ρ.fr (j + 1) w).1 τ with hz
  obtain ⟨m, ys, Ps, hinv, havg⟩ := GlobalTheory.KJInf.subY_eq_sum_averages D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) hab (ρ.lam j)
    (ρ.n j) (GinfC (c.X j)) ν (fun k => ρ.r j (Nat.le_of_succ_le hj1) k.1) (hρ.uni j _) z
  set s0 : ℂ := (∏ τ, ((ρ.fr (j + 1) w).1 τ).det ^ ρ.sD j τ)⁻¹ with hs0
  let y : Fin m → c.Fr j := fun i => (ρ.fr j).symm ⟨ys i, hinv i⟩
  have hy : ∀ i, (ρ.fr j (y i)).1 = ys i := fun i => congrArg Subtype.val ((ρ.fr j).apply_symm_apply ⟨ys i, hinv i⟩)
  have hP : ∀ i, ∃ P : PolF D (c.X (j + 1)).rank (c.X j).rank,
      castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) P = (s0 * ∏ τ, (ys i τ).det ^ ρ.sS j τ) • Ps i :=
    fun i => castP_surjective _ _ _
  choose P hP using hP
  refine ⟨m, y, P, fun ψ hψ γ => ?_⟩
  have hsc : ∀ (i : Fin 1) τ, (ρ.fr (j + 1) ((fun _ => w) i)).1 τ = ρ.sc j τ • (fun _ => z) i τ := by
    intro i τ
    simp only [hz]
    rw [smul_smul, mul_inv_cancel₀ (hρ.sc j τ), one_smul]
  have hav : ∀ F ∈ Vn (ρ.lam j) (ρ.n j), ∀ Λ : FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ,
      ∑ i, (∏ τ, ((ρ.fr j (y i)).1 τ).det ^ (-ρ.sS j τ)) *
        ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj1) k.1 τ)⁻¹) (fun _ => 1)
          (castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) (P i))) *
          evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ * (ρ.fr j (y i)).1 τ) F ∂ν =
      ∑ i : Fin 1, (fun _ => s0) i * Λ (subY hab ((fun _ => z) i) F) := by
    intro F hF Λ
    clear hL
    have h0 := havg F hF Λ
    rw [Fin.sum_univ_one, ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (∏ τ, (ys i τ).det ^ (-ρ.sS j τ)) * ∏ τ, (ys i τ).det ^ ρ.sS j τ = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hinv i τ).ne_zero)]
    beta_reduce
    simp only [hy, hP, map_smul, smul_eq_mul, mul_assoc, integral_const_mul]
    linear_combination (s0 * ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj1) k.1 τ)⁻¹) (fun _ => 1) (Ps i)) *
          evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ * ys i τ) F ∂ν) * e
  have hmain := hL m y P 1 (fun _ => z) (fun _ => w) (fun _ => s0) hsc hav t A ht hA ψ hψ γ
  have hs1 : s0 * ∏ τ, ((ρ.fr (j + 1) w).1 τ).det ^ ρ.sD j τ = 1 := by
    rw [hs0]
    refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ ((ρ.fr (j + 1) w).2 τ).ne_zero)
  rw [hmain, Fin.sum_univ_one]
  simp only [hs1, one_smul]

end GlobalTheory.SeeSaw

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawTuple_kernelBack_of_classKernelData : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → t.Is → ρ.Is → A.Is → (∀ j, j < D.R.m → t.cK j ≠ 0) → t.KBack := by
  atlas_forward_decl GlobalTheory.SeeSaw.kBack_of_classData
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem tailRd_of_clsT : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsT ρ t), A.Is → t.cP ≠ 0 → t.TailRd := by
  intro D c t ρ A hA hcP n h ψ hψ ψ' hψ' a H F
  have e1 := hA.tail n h ψ hψ F
  have e2 := hA.tail n h ψ' hψ' F
  have key : ∀ β (x : A.cl), A.ell n h β x F (ρ.low n h fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) =
      a * A.ell n h β x F (ρ.low n h fun z => t.rd n β ψ' ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) := by
    intro β x
    have : (fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) =
        a • (fun z => t.rd n β ψ' ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) := by
      funext z
      rw [H β ((ρ.fr n).symm z)]
      rfl
    rw [this, map_smul, map_smul, smul_eq_mul]
  simp_rw [key] at e1
  have e3 : t.cP * t.tail n h ψ F = t.cP * (a * t.tail n h ψ' F) := by
    rw [← e1, mul_left_comm t.cP a, ← e2]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  exact mul_left_cancel₀ hcP e3

end GlobalTheory.SeeSaw

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastPeriodClasses_give_tailReading : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsT ρ t), A.Is → t.cP ≠ 0 → t.TailRd := by
  atlas_forward_decl GlobalTheory.SeeSaw.tailRd_of_clsT
end

section
section
open ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.KernelCommTw

noncomputable section

namespace GlobalTheory.KernelCommExplicit

theorem kernelsCommuteExplicitConst : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (l' l : kˣ →* ℂˣ), IsUnram l' → IsUnram l → ∀ (P₀ : Pair k n') (Q₀ : Pair k n), ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V), (∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)) → ∃ K : EqForm π' →ₗ[ℂ] EqForm π, (∀ φ, (K φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀)) ∧ (∀ (s : 𝓀[k]ˣ) φ, (K ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 = dia s (K φ).1) ∧ ∀ φ : EqForm π', φ.1 ∈ Mram k n' V' → (K φ).1 ∈ Mram k n V ∧ (K ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1 = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q (resChar ψ hψ q) (K φ).1 := by
  intro k _ _ _ _ n n' _ _ _ _ q ψ hψ l' l hl' hl P₀ Q₀ V' V _ _ _ _ π' π θ hθ
  refine ⟨LinearMap.codRestrict (EqForm π) (KK hl hθ P₀ Q₀ ∘ₗ (EqForm π').subtype)
    fun φ => KK_mem hl hθ P₀ Q₀ φ.1, fun φ => ?_, fun s φ => KK_dia hl hθ P₀ Q₀ hl' s φ.2, fun φ h =>
      ⟨KK_ram hl hθ P₀ Q₀ hl' φ.2 h, KK_FFStar hl hθ P₀ Q₀ hl' q _ φ.2 h⟩⟩
  show KK hl hθ P₀ Q₀ φ.1 Q₀ = _
  simpa using KK_smul hl hθ P₀ Q₀ φ.1 1

end GlobalTheory.KernelCommExplicit
end
end

open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelsCommuteExplicitConstAlt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (l' l : kˣ →* ℂˣ), IsUnram l' → IsUnram l → ∀ (P₀ : Pair k n') (Q₀ : Pair k n), ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V), (∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)) → ∃ K : EqForm π' →ₗ[ℂ] EqForm π, (∀ φ, (K φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀)) ∧ (∀ (s : 𝓀[k]ˣ) φ, (K ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 = dia s (K φ).1) ∧ ∀ φ : EqForm π', φ.1 ∈ Mram k n' V' → (K φ).1 ∈ Mram k n V ∧ (K ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1 = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q (resChar ψ hψ q) (K φ).1 := by
  atlas_forward_decl GlobalTheory.KernelCommExplicit.kernelsCommuteExplicitConst
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing MeasureTheory

noncomputable section

namespace GlobalTheory.FinPl.LiftExactPf

theorem frame_card {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (α : Frame p S n) :
    Fintype.card n = S.rank := by
  have h1 := Matrix.rank_mul_le_left α.b α.b'
  have h2 := Matrix.rank_mul_le_left α.b' α.b
  rw [α.bb', Matrix.rank_one] at h1
  rw [α.b'b, Matrix.rank_one] at h2
  have h3 := Matrix.rank_le_card_width α.b
  have h4 := Matrix.rank_le_card_width α.b'
  simp only [Fintype.card_fin] at h1 h4
  omega

theorem chrPow_mul_neg {D : D7} (χ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) :
    chrPow χ a e * chrPow χ a (-e) = 1 := by
  unfold chrPow
  rw [← Circle.coe_mul, ← zpow_add, add_neg_cancel, zpow_zero, Circle.coe_one]

end GlobalTheory.FinPl.LiftExactPf

namespace GlobalTheory.FinPl

open GlobalTheory.FinPl.LiftRam GlobalTheory.FinPl.LiftExactPf in

theorem liftExact : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  intro D k _ _ _ _ p q χ hχ
  refine ⟨-1, Or.inr rfl, ?_⟩
  intro n n' _ _ _ _ ψ S T hS vS χS χT om hW hχS hχT α β P Q a ha LS LT f₀ f hOv φ₀ hφ₀ ε
  have haq : a = p.idele q.unit := Units.ext (by rw [SplitPt.idele_val, ha]; abel)
  subst haq
  obtain ⟨lS, lT, hlS, hlT, hlSq, hlTq, hlinE⟩ := GlobalTheory.T.linearModel_splitPlace_characterEquivariance D k p q ψ S T χS χT om hW
  obtain ⟨lS₀, lT₀, -, -, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  have hK := GlobalTheory.T.kernelsCommuteExplicitConstAlt k n n' q χ hχ lS lT (hlS hχT) (hlT hχS) P Q
  have hOv2 := hOv
  obtain ⟨hLS, hLT, hVac, -, -⟩ := hOv2
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hW.std S T α β LS LT hLS hLT f₀ hVac

  let F : SB (Matrix n n' k) → WO S T → ℂ := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose
  have hF : ∀ Ψ : SB (Matrix n n' k), Over ψ α β LS LT f₀ Ψ.1 (F Ψ) := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose_spec
  have hFu : ∀ (Ψ : SB (Matrix n n' k)) g, Over ψ α β LS LT f₀ Ψ.1 g → g = F Ψ :=
    fun Ψ g hg => (hex Ψ.1 Ψ.2).unique hg (hF Ψ)
  have hFth : ∀ Ψ, IsThetaFunO ψ S T (F Ψ) := fun Ψ => (hth _ _ (hF Ψ)).1
  have hFlin : ∀ (a : ℂ) (Ψ Ψ' : SB (Matrix n n' k)), F (a • Ψ + Ψ') = a • F Ψ + F Ψ' := fun a Ψ Ψ' =>
    (hFu (a • Ψ + Ψ') _ ((hlin n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ)).2.2 a Ψ'.1 (F Ψ') (hF Ψ'))).symm
  have hF0 : F 0 = 0 := by
    have h1 := hFlin 1 0 0
    simp only [one_smul, add_zero] at h1
    have h2 : F 0 + F 0 = F 0 + 0 := by rw [← h1, add_zero]
    exact add_left_cancel h2
  have hFadd : ∀ Ψ Ψ' : SB (Matrix n n' k), F (Ψ + Ψ') = F Ψ + F Ψ' := fun Ψ Ψ' => by
    simpa using hFlin 1 Ψ Ψ'
  have hFsmul : ∀ (a : ℂ) (Ψ : SB (Matrix n n' k)), F (a • Ψ) = a • F Ψ := fun a Ψ => by
    simpa [hF0] using hFlin a Ψ 0
  have hint : ∀ (v : contAutSub S) (Ψ : SB (Matrix n n' k)) h,
      IntegrableOn (fun g => om (g, h) (F Ψ) 0 * v.1 g) vS.𝓕 vS.μ :=
    fun v Ψ h => (lift_facts hS vS hW (hFth Ψ) v.2).1 h

  let θ : contAutSub S →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] (GA D T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Ψ => liftT om vS.μ vS.𝓕 v.1 (F Ψ))
      (fun v₁ v₂ Ψ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, Submodule.coe_add, mul_add]
        exact integral_add (hint v₁ Ψ h) (hint v₂ Ψ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, mul_left_comm _ a]
        exact integral_const_mul a _)
      (fun v Ψ₁ Ψ₂ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, hFadd, map_add, add_mul]
        exact integral_add (hint v Ψ₁ h) (hint v Ψ₂ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, hFsmul, map_smul, smul_eq_mul, mul_assoc]
        exact integral_const_mul a _)
  have hθ : ∀ v Ψ, θ v Ψ = liftT om vS.μ vS.𝓕 v.1 (F Ψ) := fun v Ψ => rfl
  have hEq : ∀ (g : GL n' k) (h : GL n k) (v : contAutSub S) (Ψ Ψ' : SB (Matrix n n' k)),
      (∀ x, Ψ'.1 x = (lS (Matrix.GeneralLinearGroup.det g) : ℂ) * (lT (Matrix.GeneralLinearGroup.det h) : ℂ) *
        Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (repAut α g v) Ψ' = β.rep h (θ v Ψ) := by
    intro g h v Ψ Ψ' hΨ
    have e : F Ψ' = om (α.gl g, β.gl h) (F Ψ) := by
      refine (hFu Ψ' _ ?_).symm
      have := hlinE n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ) g h
      convert this using 1
      funext x
      exact hΨ x
    funext h₁
    rw [hθ, hθ, rep_apply, liftT_apply, liftT_apply, e, repAut_val]
    simp only [rep_apply, LiftRam.om_mul]
    exact setIntegral_mul_right hS vS (fun x => om (x, h₁ * β.gl h) (F Ψ) 0 * v.1 x)
      (fun γ hγ x => by rw [om_left hW (hFth Ψ) hγ, v.2.1 γ hγ x]) (α.gl g)
  obtain ⟨K, hKval, hKdia, hKram⟩ := hK (contAutSub S) (GA D T → ℂ) (repAut α) β.rep θ hEq
  obtain ⟨φ, ⟨hφE, hφM, hφC⟩, rfl⟩ := hφ₀
  let φ' : EqForm (repAut α) := ⟨toAut hφC, fun g P₁ => Subtype.ext (hφE g P₁)⟩
  have hφ'M : φ'.1 ∈ Mram k n' (contAutSub S) := by
    letI := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun P₁ => Subtype.ext ?_
    have := (mem_Mram _).1 hφM P₁
    simpa [φ', toAut, Submodule.coe_sum] using this
  have hFf : F (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) = f := (hFu _ f hOv).symm
  have hfth : IsThetaFunO ψ S T f := hFf ▸ hFth _
  set φT : Form k n (GA D T → ℂ) := (K φ').1 with hφT
  have hφTQ : φT Q = liftT om vS.μ vS.𝓕 (φ P) f := by
    rw [hφT, hKval φ', hθ, hFf]
    rfl
  have hcQ : IsContAut T (φT Q) := by
    rw [hφTQ]
    exact (lift_facts hS vS hW hfth (hφC P)).2
  have hRam : IsRam β φT := by
    refine ⟨(K φ').2, (hKram φ' hφ'M).1, fun Q' => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q Q'
    have e : φT (g • Q) = β.rep g (φT Q) := (K φ').2 g Q
    rw [e]
    exact isContAut_mul_right hcQ (β.gl g)
  set c : ℂ := (lS q.unit : ℂ) * (lT q.unit : ℂ) with hc
  have h1 := (hKram φ' hφ'M).2
  have h2 := hKdia ε ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩
  have h3 := hKval ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩
  have key : liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f =
      c • FFStar q (resChar χ hχ q) φT (ε • Q) := by
    calc liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f
        = θ (dia ε (FFStar q (resChar χ hχ q) φ'.1) P) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) := by
          rw [hθ, hFf, dia_apply]
          exact congrArg (liftT om vS.μ vS.𝓕 · f) (toAut_FFStar q _ hφC (ε • P)).symm
      _ = (K ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩).1 Q := h3.symm
      _ = dia ε (K ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩).1 Q := by rw [h2]
      _ = c • FFStar q (resChar χ hχ q) φT (ε • Q) := by rw [h1, dia_apply]; rfl

  have hQ : (0 : ℝ) < resCard k := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  have hnT := frame_card β
  have hnS := frame_card α
  have hR : ((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2)) * ((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2)) *
      ((resCard k : ℝ) ^ ((S.rank : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add hQ, ← Real.rpow_add hQ, hnT, hnS]
    convert Real.rpow_zero (resCard k : ℝ) using 2
    ring
  have hR' : (((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) *
      (((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2) : ℝ) : ℂ) * (((resCard k : ℝ) ^ ((S.rank : ℝ) / 2) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hR
  have eS := chrPow_mul_neg χS (p.idele q.unit) (-1)
  have eT := chrPow_mul_neg χT (p.idele q.unit) 1
  simp only [neg_neg] at eS ⊢
  have hCc : ((((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) *
      chrPow χS (p.idele q.unit) (-1) * chrPow χT (p.idele q.unit) 1) * c = 1 := by
    rw [hc, hlSq, hlTq]
    linear_combination (chrPow χS (p.idele q.unit) (-1) * chrPow χS (p.idele q.unit) 1 *
      (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1))) * hR' +
      (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1)) * eS + eT
  rw [← hφTQ]
  unfold sOp
  rw [formAt_eq α hφE P, formAt_eq β hRam.1 Q, dia_apply, dia_apply, key, smul_smul, hCc, one_smul]

end GlobalTheory.FinPl

end
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLiftExactConstant_proof : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  atlas_forward_decl GlobalTheory.FinPl.liftExact
end

section
set_option maxHeartbeats 4000000
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Fam.lawsLinks_of_geo_rows_cols : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → (∀ k : Cst a, ∃ col w₀ w F, GlobalTheory.AdForm.FamCol (a.fam row col) ∧ ColOut (row := row) (col := col) k w₀ w F) → ∃ col, (a.fam row col).RowOK ∧ LawsX (a.fam row col).t ∧ ChartZero (a.fam row col) ∧ LinkTail (a.fam row col) ∧ LinkComm (a.fam row col) ∧ RatioQ (a.fam row col) := by
  intro hDS hHC hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT row hrow hsame hcol
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have hRow : ∀ col, (a.fam row col).RowOK := fun col => ⟨ha.meas, ha.last, ha.x, hrow, hsame⟩
  obtain ⟨col₀, -, -, -, -, -⟩ := hcol ⟨fun _ _ => 1, fun _ => ⟨0, Fin.elim0, Fin.elim0⟩, 0, 0, 0, 0⟩
  have hcIs : (commOf (pk W) u a.g).Is := (GlobalTheory.T.family_rows_columns_valid hDS hHC W u hW.pk (a.fam row col₀) (hRow col₀)).1
  obtain ⟨ε, op, r, e, cG, hr, hcG, hkap, hvIs, hall⟩ :=
    GlobalTheory.T.seeSaw_latticeFramePins_finiteIntegralLaws _ _ a.v a.k a.ι a.o a.n a.G hcIs ha.last ha.vis ha.shape ha.gpin
  obtain ⟨s, hs, hζ⟩ := GlobalTheory.T.nonzero_scalars_roots_of_unity _ _ _ _ _ _ _ _ _ W u (a.fam row col₀) hW.pk (hRow col₀) a.v ha.vis
    (ha.tie row col₀).1 a.n a.G a.pl ha.gpin (ha.tie row col₀).2
  choose ζ hζu hζv using hζ
  let k : Cst a := ⟨ε, op, r, e, cG, fun t j => s j * ζ t j⟩
  obtain ⟨col, w₀, w, F, hFC, hCO⟩ := hcol k
  have hQ : ∀ t p, p ∈ (w t).Q ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := by
    intro t p
    rw [(hCO.same t).1, (hCO.pins t).places p]
    obtain ⟨pl, hpl⟩ := (hCO.lev t).places
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(pl i).1, (pl i).2, (hpl i).2⟩
    · rintro ⟨PP, hPP, rfl⟩
      exact ⟨pl.symm ⟨PP, hPP⟩, by rw [(hpl _).2, Equiv.apply_symm_apply]⟩
  have hVf : ∀ t, VfAt (a.fam row col) a.v (w t) (k.sc t) := by
    intro t
    let w' : VTup ((a.fam row col₀).t t) := ⟨(w₀ t).Q, 0, (w₀ t).eQ, (w₀ t).eQT, fun _ _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ => ∅,
      fun _ => ∅, ∅, 0, 0⟩
    have h1 := hζv t w' (fun p => by rw [← (hCO.same t).1]; exact hQ t p)
      (fun j => ⟨(hCO.atQ t j).1, (hCO.atQ t j).2.1⟩) (hCO.vec t)
    obtain ⟨-, he, heT, -⟩ := hCO.same t
    refine ⟨fun j hj P b hb b' hb' => ?_, fun j h P => ?_⟩
    · rw [he]; exact h1.1 j hj P b hb b' hb'
    · rw [heT]; exact h1.2 j h P
  have hIs := GlobalTheory.T.family_rows_columns_valid hDS hHC W u hW.pk (a.fam row col) (hRow col)
  have htIs : ∀ t, ((a.fam row col).t t).Is := hIs.2 hCO.ok
  have hweil := fun t => GlobalTheory.T.family_chars_weilOK_unramified W u hW.pk (a.fam row col) a.v (hRow col) hCO.ok (ha.tie row col).1
    (fun j h => ⟨ha.shape.pre.line.1, ha.shape.pre.tau j h⟩) t (w t) (hQ t)
  have hchars : ∀ t i, (a.G i).Chars ((a.fam row col).t t) := fun t => (hweil t).2.2.2.2.2.2 a.n a.G a.pl (ha.tie row col).2
  have hrowt := fun t => GlobalTheory.T.quadratic_family_level_identity _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) a.v ha.vis (ha.tie row col).1 a.n a.G a.pl
    ha.gpin (ha.tie row col).2 t (w₀ t) (F t) (htIs t) (hCO.pins t) (hCO.lev t) (hchars t)
  have hVF : ∀ t, VForm k.v (w t) := by
    intro t
    obtain ⟨hsQ, he, heT, -, hFY, hFT⟩ := hCO.same t
    have hw := hweil t
    have hrw := hrowt t
    have htie := (ha.tie row col).1
    obtain ⟨S₀, hS⟩ := hCO.read t
    refine ⟨hw.2.2.2.2.1, hw.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrw.2.1⟩
    · intro j hj P b hb b' hb'
      rw [hCO.sc t]; exact (hVf t).1 j hj P b hb b' hb'
    · intro j h P
      rw [hCO.sc t]; exact (hVf t).2 j h P
    · intro j
      have := hCO.atQ t j
      rw [← hsQ, ← he, ← heT] at this
      exact this
    · intro j α
      obtain ⟨h1, h2⟩ := hCO.e t j α
      have hb : k.v.b j = a.g.b j := htie.b j
      refine ⟨by rw [hb]; exact h1, fun g hg => ?_⟩
      rw [hsQ]; exact h2 g hg
    · intro n h β
      obtain ⟨h1, h2⟩ := hCO.eT t n h β
      have hb : k.v.bT = a.g.bT := htie.bT.1
      refine ⟨by rw [hb]; exact h1, fun g hg => ?_⟩
      rw [hsQ]; exact h2 g hg
    · exact hCO.dd t
    · intro j hj ψ hψ α y
      refine ⟨?_, hCO.FX t j hj ψ hψ α y, hS.S j hj ψ hψ α y⟩
      show _ ∈ a.v.RamAd j
      rw [ha.shape.ram j]; exact hS.ram j (by omega) ψ hψ α y
    · intro j hj G x b hb
      obtain ⟨h1, h2⟩ := hrw.1 j hj G x b hb
      refine ⟨?_, fun κ hκ => h2 κ ?_⟩
      · rw [hFY]; exact ((hCO.FY t j _).2 h1)
      · have hoff : offP k.v (w t) = offP a.v (w₀ t) := by
          funext p
          show (p ∉ a.v.gP ∧ p ∉ (w t).Q) = (p ∉ a.v.gP ∧ p ∉ (w₀ t).Q)
          rw [hsQ]
        rw [hoff] at hκ; exact hκ
    · intro G x
      rw [hFT]; exact hCO.FT t _
  obtain ⟨hloc, hval, hlast⟩ := hall W.P.T (a.fam row col).t w fun t => ⟨htIs t, hVF t, (hweil t).1, (hrowt t).2.2, (hweil t).2.1,
    (hweil t).2.2.2.1, hchars t, (hCO.laws t).1, (hCO.laws t).2.1, (hCO.laws t).2.2, hCO.cT t, hCO.cv t⟩
  have hcls : ClsPinD (a.fam row col).t := GlobalTheory.T.true_family_top_row W u (a.fam row col) hW.tr hW.tw ha.top (hRow col) hFC
  have hlaws : LawsX (a.fam row col).t := ⟨hIs.1, htIs, hloc, GlobalTheory.T.real_equality_of_columns W u hW.pk (a.fam row col) hCO.ok, hval, hlast,
    GlobalTheory.T.seeSawKernelLiftCombination_of_definiteClassData _ _ _ _ hIs.1 htIs hcls, GlobalTheory.T.seeSawLastPeriodFactorization_of_classData _ _ _ _ hIs.1 htIs hcls, GlobalTheory.T.seeSaw_scalarForms_continuous_automorphic_central _ _ _ _ hIs.1 htIs hcls⟩
  have hheq : ∀ t, W.P.I.tup t = (I.rec7 l Z).what₂.mu0 → ∀ φ, HEq (col0 (a.fam row col) t φ) ((I.rec7 l Z).eMu u φ).1 := by
    intro t ht φ
    show HEq ((I.rec7 l Z).e0Tw u (W.P.I.tup t) _) _
    rw [ht]
    exact heq_of_eq (GlobalTheory.Mem.Col2.TC.stepZeroTwist_reference_tuple_eq_id l u _)
  refine ⟨col, hRow col, hlaws, hCO.zero, GlobalTheory.MiTop.linkTail_of_topReadAt W u (a.fam row col) ha.top hheq, ?_, ?_⟩
  · obtain ⟨ρ, hρ, hA⟩ := hcls
    choose S₀ hS₀ using hCO.read
    have hsh : ShapeOff k.v a.o := by
      have hs := ha.shape
      have hp := hs.pre
      exact ⟨⟨hp.nodup, hp.all, hp.inj, hp.tP, hp.char, hp.latT, hp.line, hp.tau, hp.lam, hp.normT, hp.topT⟩,
        fun x => ⟨(hs.good x).bf, (hs.good x).fb⟩, fun x hx => ⟨(hs.split x hx).core, (hs.split x hx).top⟩, hs.glued, hs.rep,
        hs.ram⟩
    have hne : ∀ {S : ℕ → Prop} {x y : ℂ}, UnitRatio S x y → x ≠ 0 := fun h => ((GlobalTheory.Fam.unitRatio_laws _).2.1 _ _ _ _ h h).2.2
    refine GlobalTheory.T.type_data_unit_shift_relation W u (a.fam row col) a.k a.ι a.o ε S₀ (GlobalTheory.FinPl.RamUnit.ramUnitary_holds _) hIs.1
      (fun t => ⟨htIs t, ?_, ?_, ?_, hS₀ t⟩) ha.shape.pre.nodup ha.shape.pre.all ha.shape.pre.inj ?_ ?_ ?_
    · obtain ⟨⟨A, hAI⟩, -⟩ := hA t
      exact GlobalTheory.T.seeSawTuple_kernelBack_of_classKernelData _ _ _ ρ A hIs.1 (htIs t) hρ hAI fun j hj => hne (hCO.cK t j hj)
    · obtain ⟨-, A, hAI⟩ := hA t
      exact GlobalTheory.T.lastPeriodClasses_give_tailReading _ _ _ ρ A hAI (hne (hCO.cP t))
    · exact GlobalTheory.T.definiteLift_comm_levelPrimeOperators _ _ a.k a.ι k.v a.o _ (w t) (GlobalTheory.T.splitLiftExactConstant_proof _) hIs.1 (htIs t) hvIs (hVF t) hsh
        (GlobalTheory.T.type_data_local_relation W u hW.pk (a.fam row col) a.v a.k a.ι a.o (hRow col) hCO.ok ha.vis (ha.tie row col).1 ha.shape t)
    · intro t
      obtain ⟨α₀, -⟩ := hCO.zero t
      exact ⟨α₀⟩
    · intro t φ
      obtain ⟨α₀, hα, -, h3, -⟩ := hCO.zero t
      exact ⟨(h3 φ).1, fun α y => by rw [hα α]; exact (h3 φ).2 y⟩
    · intro t
      obtain ⟨α₀, -, -, -, h4⟩ := hCO.zero t
      exact h4
  · intro n hn t
    have hsc : ∀ tt j, j < (I.rec7 l Z).R.m → UnitRatio (qPrime W tt) ((w tt).sc j) ((w W.P.A3.A.μ0).sc j) ∧
        UnitRatio (qPrime W tt) (((a.fam row col).t tt).cK j) (((a.fam row col).t W.P.A3.A.μ0).cK j) := by
      intro tt j hj
      refine ⟨?_, hCO.cK tt j hj⟩
      rw [hCO.sc tt, hCO.sc W.P.A3.A.μ0]
      obtain ⟨n₁, hn₁, e₁⟩ := hζu tt j
      obtain ⟨n₂, hn₂, e₂⟩ := hζu W.P.A3.A.μ0 j
      have hz : ζ W.P.A3.A.μ0 j ≠ 0 := fun h0 => by rw [h0, zero_pow hn₂.ne'] at e₂; exact zero_ne_one e₂
      refine (GlobalTheory.Fam.unitRatio_laws _).2.2.1 _ _ (n₁ * n₂) (mul_ne_zero (hs j) hz) (Nat.mul_pos hn₁ hn₂) ?_
      show (s j * ζ tt j) ^ (n₁ * n₂) = (s j * ζ W.P.A3.A.μ0 j) ^ (n₁ * n₂)
      rw [mul_pow, mul_pow, pow_mul (ζ tt j), e₁, mul_comm n₁ n₂, pow_mul (ζ W.P.A3.A.μ0 j), e₂, one_pow, one_pow]
    have hcI : ∀ tt j, j < (I.rec7 l Z).R.m → ((a.fam row col).t tt).cI j ≠ 0 := fun tt j hj =>
      GlobalTheory.Fam.GeoMeas.cIOf_ne_zero (lvP W) ha.meas tt j hj
    have hci := fun tt => GlobalTheory.T.chain_ideal_index_product _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) a.v ha.vis (ha.tie row col).1 tt
      (w₀ tt) (F tt) (hCO.pins tt) (hCO.lev tt)
    have hq : ∀ tt j ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m → (w tt).cQ j / (((a.fam row col).t tt).cI j * ((a.fam row col).t tt).cI (j + 1)) =
        (((a.fam row col).t W.P.A3.A.μ0).cI j * ((a.fam row col).t W.P.A3.A.μ0).cI (j + 1))⁻¹ := by
      intro tt j ρ h
      rw [(hCO.same tt).2.2.2.1, (hCO.pins tt).cQ j (by omega), ← hci tt j (by omega), ← hci tt (j + 1) (by omega),
        Finset.prod_inv_distrib, Finset.prod_mul_distrib, div_eq_mul_inv, ← mul_inv]
      congr 1
      ring
    have hct : ∀ tt j ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m → UnitRatio (qPrime W tt) ((w tt).cT j) ((w W.P.A3.A.μ0).cT j) ∧
        UnitRatio (qPrime W tt) ((w tt).cQ j / (((a.fam row col).t tt).cI j * ((a.fam row col).t tt).cI (j + 1)))
          ((w W.P.A3.A.μ0).cQ j / (((a.fam row col).t W.P.A3.A.μ0).cI j * ((a.fam row col).t W.P.A3.A.μ0).cI (j + 1))) := by
      intro tt j ρ h
      refine ⟨?_, ?_⟩
      · rw [hCO.cT tt j ρ h, hCO.cT W.P.A3.A.μ0 j ρ h, ((hrow tt).sBF j ρ h).2.2.2, ((hrow W.P.A3.A.μ0).sBF j ρ h).2.2.2]
        exact GlobalTheory.SeeSaw.mono_unitRatio _ _ a.k a.ι a.o (r j) (e j) _ _ _ (hr j)
          ((GlobalTheory.T.root_of_unity_theta_twist _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) tt).choose_spec.2.2.2 (j + 1))
      · rw [hq tt j ρ h, hq W.P.A3.A.μ0 j ρ h]
        exact (GlobalTheory.Fam.unitRatio_laws _).1 _ (inv_ne_zero (mul_ne_zero (hcI _ j (by omega)) (hcI _ (j + 1) (by omega))))
    obtain ⟨h1, -, h3⟩ := GlobalTheory.T.seeSaw_totalConstant_ratio_of_factor_ratios _ _ k.v W.P.T (a.fam row col).t w (qPrime W) W.P.A3.A.μ0 htIs hCO.cv hkap hcG hsc hct
      hCO.cP n hn t
    exact ⟨h1, h3⟩
end
end
