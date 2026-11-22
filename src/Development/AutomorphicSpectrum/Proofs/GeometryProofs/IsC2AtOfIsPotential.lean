module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentialsStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PushAFinsumInter
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffOnFubiniStudyProfileInvNormSqFirst
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm
  ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo
  GlobalTheory.CompanionTheory.Ar.PB

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_combLine {σ : Type} [Fintype σ] {A : σ → HermLine ι} (hA : ∀ a, IsSmoothHerm (A a))
    (n : σ → ℤ) : IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.PB.combLine A n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (A a).h z ≠ 0 := ((A a).pos z hz).ne'
  have hf := hA a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {P : LocPot X}
    (hP : IsPotential A P) (x : X) : IsTwiceDifferentiableAt A P x := by
  intro j hj
  have hm : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
    ⟨(A.chart j).map_source hj, by
      rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact P.mem_U x⟩
  exact (contDiffAt_of_isPotential A P hP x j hm).of_le (by
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

end Lines

section Coef

variable {Ψ : Type} [DecidableEq Ψ] {N : ℕ}

def rootCoef (r p : Ψ × Fin N) : ℤ :=
  (if p.1 = r.1 ∧ (p.2 : ℕ) + 1 = r.2 then 1 else 0) - (if p = r then 1 else 0)

theorem sum_rootCoef_mul [Fintype Ψ] (r : Ψ × Fin N) (f : Ψ × Fin N → ℤ) :
    ∑ p, rootCoef r p * f p =
      (if h : 0 < (r.2 : ℕ) then f (r.1, ⟨(r.2 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) r.2.isLt⟩) else 0) - f r := by
  obtain ⟨τ, i⟩ := r
  simp only [rootCoef, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  congr 1
  · split_ifs with h
    · rw [Finset.sum_eq_single (τ, ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩)]
      · rw [if_pos ⟨rfl, by simp only; omega⟩]
      · rintro ⟨τ', l⟩ - hne
        rw [if_neg]
        rintro ⟨h1, h2⟩
        simp only at h1 h2
        subst h1
        exact hne (by simp only [Prod.mk.injEq, true_and]; ext; simp only; omega)
      · simp
    · refine Finset.sum_eq_zero fun p _ => if_neg ?_
      rintro ⟨-, h2⟩
      have h2' : (p.2 : ℕ) + 1 = i := h2
      omega
  · simp

theorem sum_neg_mul_rootCoef [Fintype Ψ] (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    ∑ r, -lam r * (rootCoef r p : ℝ) = GlobalTheory.CompanionTheory.Ar.PB.gap lam p := by
  obtain ⟨τ, l⟩ := p
  have h2 : ∑ r : Ψ × Fin N, lam r * (if (τ, l) = r then (1 : ℝ) else 0) = lam (τ, l) := by simp
  have h1 : ∑ r : Ψ × Fin N, lam r * (if (τ, l).1 = r.1 ∧ (((τ, l).2 : Fin N) : ℕ) + 1 = r.2 then (1 : ℝ) else 0) =
      if h : (l : ℕ) + 1 < N then lam (τ, ⟨(l : ℕ) + 1, h⟩) else 0 := by
    split_ifs with h
    · rw [Finset.sum_eq_single (τ, ⟨(l : ℕ) + 1, h⟩)]
      · simp
      · rintro ⟨τ', m⟩ - hne
        rw [if_neg, mul_zero]
        rintro ⟨h1, h2⟩
        simp only at h1 h2
        subst h1
        exact hne (by simp only [Prod.mk.injEq, true_and]; ext; simp only; omega)
      · simp
    · refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg, mul_zero]
      rintro ⟨-, h2⟩
      have := r.2.isLt
      simp only at h2
      omega
  have h3 : GlobalTheory.CompanionTheory.Ar.PB.gap lam (τ, l) =
      lam (τ, l) - if h : (l : ℕ) + 1 < N then lam (τ, ⟨(l : ℕ) + 1, h⟩) else 0 := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.gap gapX
    split_ifs with h <;> simp [h]
  rw [h3, ← h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [rootCoef]
  push_cast
  ring

end Coef

section Real

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end Real

section Main

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

end Main

end GlobalTheory.CompanionTheory.Ar.Cmp
