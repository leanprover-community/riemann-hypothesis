import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceRate
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergySum

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

def Telescoping.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (S : System R), ∃ C' ℓ₁ : ℝ, ∀ t t' : ℝ, 0 < t' → t' ≤ t → ℓ₁ ≤ ell t → ∀ x ∈ R.Yo,
      (R.r x ≤ ell t → |S.ph t x - S.ph t' x| ≤ C' * (t ^ (1 / 3 : ℝ) + errE S.C t)) ∧
      (ell t < R.r x → |S.ph t x - S.ph t' x| ≤ C' * Real.log (R.r x))

def TelescopingFamily.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (F : Family A) (Λ : ℝ),
    ∃ C' ℓ₁ : ℝ, ∀ c : Fin F.m → ℝ, ∑ i, |c i| ≤ Λ →
      ∀ t t' : ℝ, 0 < t' → t' ≤ t → ℓ₁ ≤ ell t → ∀ x ∈ F.Yo,
        (F.r x ≤ ell t →
          |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤
            C' * (t ^ (1 / 3 : ℝ) + errE C' t)) ∧
        (ell t < F.r x →
          |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤ C' * Real.log (F.r x))

theorem ell_anti {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) : ell t ≤ ell t' :=
  Real.log_le_log (inv_pos.2 (lt_of_lt_of_le ht' htt)) (inv_anti₀ ht' htt)

theorem one_le_of_exp_le {y : ℝ} (h : Real.exp 1 ≤ y) : 1 ≤ y := by
  have := Real.add_one_le_exp 1
  linarith

theorem errE_nonneg {C t : ℝ} (hC : 0 ≤ C) (h : 1 ≤ ell t) : 0 ≤ errE C t :=
  div_nonneg (mul_nonneg hC (Real.log_nonneg h)) (by linarith)

theorem errE_le {C t : ℝ} (hC : 0 ≤ C) (h : 1 ≤ ell t) : errE C t ≤ C := by
  unfold errE
  rw [div_le_iff₀ (by linarith)]
  exact mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) hC

theorem errE_mono {C C' t : ℝ} (hCC : C ≤ C') (h : 1 ≤ ell t) : errE C t ≤ errE C' t :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (Real.log_nonneg h)) (by linarith)

namespace System

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} {R : RegChartData A}
  (S : System R)

def teleConst : ℝ := 1 + |S.C| + S.C ^ 2 + |R.C|

theorem teleConst_pos : 0 < S.teleConst := by
  unfold teleConst
  have := abs_nonneg S.C
  have := abs_nonneg R.C
  have := sq_nonneg S.C
  linarith

theorem C_nonneg {t : ℝ} (ht : 0 < t) (h0 : S.ell₀ ≤ ell t) (h1 : 1 ≤ ell t) (x : X) : 0 ≤ S.C := by
  have h2 := S.ph_le t ht h0 x
  have h3 := S.le_log t ht h0 x
  nlinarith [Real.log_nonneg h1]

theorem dataC_nonneg {x : X} (hx : x ∈ R.Yo) : 0 ≤ R.C := by
  have h2 := R.φ_le x hx
  have h3 := R.le_φ x hx
  nlinarith [Real.log_nonneg (R.one_le_r x hx)]

theorem tele_near {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) (h0 : S.ell₀ ≤ ell t)
    (he : Real.exp 1 ≤ ell t) {x : X} (hx : x ∈ R.Yo) (hr : R.r x ≤ ell t) :
    |S.ph t x - S.ph t' x| ≤ S.teleConst * (t ^ (1 / 3 : ℝ) + errE S.C t) := by
  have ht : 0 < t := lt_of_lt_of_le ht' htt
  have h1 := one_le_of_exp_le he
  have h0' : S.ell₀ ≤ ell t' := le_trans h0 (ell_anti ht' htt)
  have hC := S.C_nonneg ht h0 h1 x
  have hK := dataC_nonneg hx
  have ha : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
  have he0 := errE_nonneg hC h1
  have up1 := S.near t ht h0 x hx hr
  have up2 := S.le_ph t' ht' h0' x hx
  have lo := S.mono t' t ht' htt h0 x
  have hM : S.teleConst * (t ^ (1 / 3 : ℝ) + errE S.C t) =
      (t ^ (1 / 3 : ℝ) + errE S.C t) + S.C * t ^ (1 / 3 : ℝ) + S.C * errE S.C t +
        S.C ^ 2 * (t ^ (1 / 3 : ℝ) + errE S.C t) + R.C * (t ^ (1 / 3 : ℝ) + errE S.C t) := by
    unfold teleConst
    rw [abs_of_nonneg hC, abs_of_nonneg hK]
    ring
  have p1 := mul_nonneg hC ha
  have p2 := mul_nonneg (sq_nonneg S.C) (add_nonneg ha he0)
  have p3 := mul_nonneg hK (add_nonneg ha he0)
  have p4 := mul_nonneg hC he0
  rw [hM, abs_le]
  constructor <;> linarith

theorem tele_far {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) (h0 : S.ell₀ ≤ ell t)
    (he : Real.exp 1 ≤ ell t) {x : X} (hx : x ∈ R.Yo) (hr : ell t < R.r x) :
    |S.ph t x - S.ph t' x| ≤ S.teleConst * Real.log (R.r x) := by
  have ht : 0 < t := lt_of_lt_of_le ht' htt
  have h1 := one_le_of_exp_le he
  have h0' : S.ell₀ ≤ ell t' := le_trans h0 (ell_anti ht' htt)
  have hC := S.C_nonneg ht h0 h1 x
  have hK := dataC_nonneg hx
  have hL : 1 ≤ Real.log (R.r x) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have up1 := S.ph_le t ht h0 x
  have up2 := S.le_ph t' ht' h0' x hx
  have up3 := R.le_φ x hx
  have lo := S.mono t' t ht' htt h0 x
  have hCe : S.C * errE S.C t ≤ S.C * S.C := mul_le_mul_of_nonneg_left (errE_le hC h1) hC
  have hM : S.teleConst * Real.log (R.r x) = Real.log (R.r x) + S.C * Real.log (R.r x) +
      S.C ^ 2 * Real.log (R.r x) + R.C * Real.log (R.r x) := by
    unfold teleConst
    rw [abs_of_nonneg hC, abs_of_nonneg hK]
    ring
  have q1 : S.C ≤ S.C * Real.log (R.r x) := le_mul_of_one_le_right hC hL
  have q2 : S.C ^ 2 ≤ S.C ^ 2 * Real.log (R.r x) := le_mul_of_one_le_right (sq_nonneg _) hL
  have q3 : S.C * S.C = S.C ^ 2 := (sq S.C).symm
  rw [hM, abs_le]
  constructor <;> nlinarith

end System

theorem Telescoping.proof : Telescoping.Statement := by
  intro X _ D A R S
  refine ⟨S.teleConst, max S.ell₀ (Real.exp 1), fun t t' ht' htt hℓ x hx => ⟨?_, ?_⟩⟩
  · exact S.tele_near ht' htt (le_trans (le_max_left _ _) hℓ) (le_trans (le_max_right _ _) hℓ) hx
  · exact S.tele_far ht' htt (le_trans (le_max_left _ _) hℓ) (le_trans (le_max_right _ _) hℓ) hx

theorem TelescopingFamily.proof : TelescopingFamily.Statement := by
  intro X _ D A F Λ
  set B : ℝ := ∑ i, (F.sys i).teleConst with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => ((F.sys i).teleConst_pos).le
  have hMB : ∀ i, (F.sys i).teleConst ≤ B := fun i =>
    Finset.single_le_sum (f := fun i => (F.sys i).teleConst)
      (fun i _ => ((F.sys i).teleConst_pos).le) (Finset.mem_univ i)
  have hCB : ∀ i, (F.sys i).C ≤ B := fun i => by
    refine le_trans ?_ (hMB i)
    unfold System.teleConst
    have := le_abs_self (F.sys i).C
    have := abs_nonneg (F.R i).C
    have := sq_nonneg (F.sys i).C
    linarith
  set C' : ℝ := (|Λ| + 1) * B with hC'
  have hBC' : B ≤ C' := by
    rw [hC']
    nlinarith [abs_nonneg Λ]
  refine ⟨C', ∑ i, |(F.sys i).ell₀| + Real.exp 1, fun c hc t t' ht' htt hℓ x hx => ?_⟩
  have h0 : ∀ i, (F.sys i).ell₀ ≤ ell t := fun i => by
    refine le_trans (le_trans (le_abs_self _) ?_) hℓ
    have := Finset.single_le_sum (f := fun i => |(F.sys i).ell₀|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    have := Real.exp_pos 1
    linarith
  have he : Real.exp 1 ≤ ell t := by
    refine le_trans ?_ hℓ
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (F.sys i).ell₀)
    linarith
  have h1 := one_le_of_exp_le he
  have hx' : ∀ i, x ∈ (F.R i).Yo := fun i => (F.Yo_eq i).symm ▸ hx
  have hr' : ∀ i, (F.R i).r x = F.r x := fun i => F.r_eq i x hx
  have hsum : |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤
      ∑ i, |c i| * |(F.sys i).ph t x - (F.sys i).ph t' x| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => abs_mul _ _
  have hc0 : ∑ i, |c i| ≤ |Λ| := le_trans hc (le_abs_self Λ)
  have hfin : ∀ K : ℝ, 0 ≤ K → (∀ i, |(F.sys i).ph t x - (F.sys i).ph t' x| ≤ B * K) →
      |∑ i, c i * ((F.sys i).ph t x - (F.sys i).ph t' x)| ≤ C' * K := by
    intro K hK hi
    refine le_trans hsum (le_trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hi i) (abs_nonneg (c i))) ?_)
    rw [← Finset.sum_mul, hC']
    have hBK := mul_nonneg hB0 hK
    nlinarith [mul_le_mul_of_nonneg_right hc0 hBK]
  have ht : 0 < t := lt_of_lt_of_le ht' htt
  have ha : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
  refine ⟨fun hr => hfin _ (add_nonneg ha (errE_nonneg (hB0.trans hBC') h1)) fun i => ?_,
    fun hr => hfin _ (Real.log_nonneg (le_trans h1 (le_of_lt hr))) fun i => ?_⟩
  · have hCi := (F.sys i).C_nonneg ht (h0 i) h1 x
    refine le_trans ((F.sys i).tele_near ht' htt (h0 i) he (hx' i) ((hr' i).symm ▸ hr))
      (mul_le_mul (hMB i) ?_ (add_nonneg ha (errE_nonneg hCi h1)) hB0)
    linarith [errE_mono ((hCB i).trans hBC') h1]
  · have h := (F.sys i).tele_far ht' htt (h0 i) he (hx' i) ((hr' i).symm ▸ hr)
    rw [hr' i] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (hMB i)
      (Real.log_nonneg (le_trans h1 (le_of_lt hr))))

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens chartPartMeasure
  existsPartition)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

section Objects

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

def Family.coefWeight (F : Family A) (x : Option (Fin F.m) → ℝ) (t : ℝ) : X → ℝ :=
  fun p => ∑ i, x (some i) * (F.sys i).ph t p

def Family.coefForm (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) (t : ℝ) : LocPot X :=
  F.chernForm (fun i => x (some i)) t + LocPot.rsmul (x none) a

def Family.coefRefForm (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) : LocPot X :=
  lincomb F.m (fun i => x (some i)) (fun i => (F.R i).θ) + LocPot.rsmul (x none) a

def Family.weightEnergy (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (D + 1), mInt A
    (fun i : Fin D => if (i : ℕ) < k then F.coefForm a x t else F.coefRefForm a x) (F.coefWeight x t)

def Family.arithSelfInt (F : Family A) (a : LocPot X) (a₀ : MvPolynomial (Option (Fin F.m)) ℝ)
    (δ : ℝ) (x : Option (Fin F.m) → ℝ) (t : ℝ) : ℝ :=
  (MvPolynomial.eval x a₀ + F.weightEnergy a x t) / δ

def Family.mixedProduct (F : Family A) (a : LocPot X) (x : Option (Fin F.m) → ℝ) (t t' : ℝ)
    (k : ℕ) : Fin D → LocPot X :=
  fun i => if (i : ℕ) < k then F.coefForm a x t else F.coefForm a x t'

def Family.Admissible (F : Family A) (t : ℝ) : Prop :=
  0 < t ∧ ∀ i, (F.sys i).ell₀ ≤ ell t

end Objects

section Potentials

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem isPotential_lincomb : ∀ (m : ℕ) (c : Fin m → ℝ) (P : Fin m → LocPot X),
    (∀ i, IsPotential A (P i)) → IsPotential A (lincomb m c P)
  | 0, _, _, _ => ReciprocityTheory.AnForm.M.isPotential_ofFun A _ fun _ => contDiffOn_const
  | m + 1, c, P, hP => ReciprocityTheory.AnForm.M.isPotentialAdd A _ _
      (ReciprocityTheory.AnForm.M.isPotentialRsmul A (c 0) (P 0) (hP 0))
      (isPotential_lincomb m _ _ fun i => hP i.succ)

theorem Family.coefForm_isPotential (F : Family A) {a : LocPot X} (ha : IsPotential A a)
    (x : Option (Fin F.m) → ℝ) {t : ℝ} (ht : F.Admissible t) : IsPotential A (F.coefForm a x t) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd A _ _
    (isPotential_lincomb _ _ _ fun i => ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (F.R i).θ_pot
      (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ ((F.sys i).smooth t ht.1 (ht.2 i))))
    (ReciprocityTheory.AnForm.M.isPotentialRsmul A _ a ha)

theorem Family.mixedProduct_isPotential (F : Family A) {a : LocPot X} (ha : IsPotential A a)
    (x : Option (Fin F.m) → ℝ) {t t' : ℝ} (ht : F.Admissible t) (ht' : F.Admissible t') (k : ℕ)
    (i : Fin D) : IsPotential A (F.mixedProduct a x t t' k i) := by
  unfold Family.mixedProduct
  split_ifs
  · exact F.coefForm_isPotential ha x ht
  · exact F.coefForm_isPotential ha x ht'

end Potentials

def Convergence.TVHyp {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {A : FinHolAtlas D X} (F : Family A) (a : LocPot X)
    (Λ M CE L₀ : ℝ) : Prop :=
  ∀ x : Option (Fin F.m) → ℝ, ∑ o, |x o| ≤ Λ → ∀ t t' : ℝ, 0 < t' → t' ≤ t → L₀ ≤ ell t →
    ∀ k ≤ D, TVBounds A (F.mixedProduct a x t t' k) F.Yo F.r M CE

def WeightCocycle.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (F : Family A) (a : LocPot X), IsPotential A a → ∀ (x : Option (Fin F.m) → ℝ) (t t' : ℝ),
    F.Admissible t → F.Admissible t' →
      F.weightEnergy a x t - F.weightEnergy a x t' =
        ∑ k ∈ Finset.range (D + 1),
          mInt A (F.mixedProduct a x t t' k) fun p => F.coefWeight x t p - F.coefWeight x t' p

def PolynomialInWeights.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (F : Family A) (a : LocPot X), IsPotential A a → ∀ t : ℝ, F.Admissible t →
      ∃ p : MvPolynomial (Option (Fin F.m)) ℝ, p.totalDegree ≤ D + 1 ∧
        ∀ x, MvPolynomial.eval x p = F.weightEnergy a x t

def Convergence.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (D : ℕ) (A : FinHolAtlas D X) (F : Family A) (a : LocPot X)
    (a₀ : MvPolynomial (Option (Fin F.m)) ℝ) (δ Λ M CE L₀ : ℝ),
    IsPotential A a → 0 < δ → (∀ i, (F.sys i).ell₀ ≤ L₀) → 0 ≤ M → 0 ≤ CE →
    Convergence.TVHyp F a Λ M CE L₀ →
    ∃ C L₁ : ℝ, ∀ x : Option (Fin F.m) → ℝ, ∑ o, |x o| ≤ Λ → ∀ t t' : ℝ, 0 < t' → t' ≤ t →
      L₁ ≤ ell t → |F.arithSelfInt a a₀ δ x t - F.arithSelfInt a a₀ δ x t'| ≤ convRate D C t

def CoefficientLimit.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (D : ℕ) (A : FinHolAtlas D X) (F : Family A) (a : LocPot X)
    (a₀ : MvPolynomial (Option (Fin F.m)) ℝ) (δ L₀ : ℝ),
    IsPotential A a → a₀.totalDegree ≤ D + 1 → 0 < δ → (∀ i, (F.sys i).ell₀ ≤ L₀) →
    (∀ Λ : ℝ, ∃ M CE : ℝ, 0 ≤ M ∧ 0 ≤ CE ∧ Convergence.TVHyp F a Λ M CE L₀) →
    ∃ P : MvPolynomial (Option (Fin F.m)) ℝ, P.totalDegree ≤ D + 1 ∧
      (∀ x, Tendsto (fun t => F.arithSelfInt a a₀ δ x t) (𝓝[>] 0) (𝓝 (MvPolynomial.eval x P))) ∧
      ∀ p : ℝ → MvPolynomial (Option (Fin F.m)) ℝ,
        (∀ᶠ t in 𝓝[>] 0, (p t).totalDegree ≤ D + 1 ∧
          ∀ x, MvPolynomial.eval x (p t) = F.arithSelfInt a a₀ δ x t) →
        ∀ α, Tendsto (fun t => (p t).coeff α) (𝓝[>] 0) (𝓝 (P.coeff α))

section Inhabitants

open ReciprocityTheory.AnForm (fsDens levi maDens_one fsDens_pos)
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineCharts projLineCharts_potential_zero isPsh_const)

attribute [local instance] projectiveLineBorel projectiveLine_borelSpace

def projectiveLineDataEmptyDivisor : RegChartData p1 where
  toRegCharts := projLineCharts
  Yo := Set.univ
  isOpen_Yo := isOpen_univ
  S _ := ∅
  mem_Yo_iff _ z _ := by simp [ReciprocityTheory.AnForm.A.coordDiv]
  r _ := Real.exp 1
  f _ _ := 0
  f_cont _ := continuousOn_const
  f_bdd _ := ⟨0, fun _ _ => by simp⟩
  r_chart _ _ _ := by simp
  one_le_r _ _ := Real.one_le_exp zero_le_one
  φ _ := 0
  φ_smooth _ := contDiffOn_const
  psh j := by
    show ReciprocityTheory.AnForm.A.IsPsh _ (projLineCharts.u (fun _ => 0) j)
    rw [projLineCharts_potential_zero]
    exact isPsh_const _ 0
  C := 0
  φ_le _ _ := le_rfl
  le_φ _ _ := by simp
  grad j z _ := by
    show ‖fderiv ℝ (projLineCharts.u (fun _ => 0) j) z‖ ≤ _
    rw [projLineCharts_potential_zero]
    simp

def projectiveLineSystemEmptyDivisor : System projectiveLineDataEmptyDivisor where
  ph _ _ := 0
  C := 0
  ell₀ := 1
  smooth _ _ _ _ := contDiffOn_const
  le_ph _ _ _ _ _ := le_rfl
  ph_le _ _ _ _ := le_rfl
  le_log _ _ _ _ := by simp
  thGe t _ _ := by
    intro x k y _ w
    have h : ((fun z => projectiveLineDataEmptyDivisor.θ.φ x z + (fun _ : OnePoint ℂ => (0 : ℝ)) z) ∘ (p1.chart k).symm) =
        fun _ => (0 : ℝ) := by
      funext z
      show (0 : ℝ) + 0 = 0
      simp
    rw [h, levi_const, errE_zero]
    simp
  near t ht _ _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  far t ht _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t * _
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  mono _ _ _ _ _ _ := by simp
  c2 _ _ _ _ := ⟨tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _,
    tendstoUniformlyOn_self _ _ _⟩

def projectiveLineFamilyEmptyDivisor : Family p1 where
  m := 1
  R _ := projectiveLineDataEmptyDivisor
  sys _ := projectiveLineSystemEmptyDivisor
  Yo := Set.univ
  r _ := Real.exp 1
  om := fsPot
  Yo_eq _ := rfl
  r_eq _ _ _ := rfl
  om_eq _ := rfl

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
