import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
import Formalism.FlagUnipotentLattices.KappaAssemblyOf
import Formalism.FlagUnipotentLattices.CuspThresholdBound

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

abbrev cu_mu (X : CData) : Measure X.I.GA := X.I.muA X.μf

instance cu_sfin (X : CData) : SigmaFinite (cu_mu X) := by
  unfold cu_mu AutInst.muA
  infer_instance


def cu_cst (X : CData) (ν : Measure X.I.GA) (f : X.I.GA → ℂ) (x : X.I.GA) : ℂ := ∫ m, f (m * x) ∂ν

structure cu_NObj (X : CData) where
  μN : ∀ v : InfinitePlace X.I.F, Measure (Formalism.REAL.UJ (X.I.ε v))
  [sN : ∀ v, SigmaFinite (μN v)]
  μNf : Measure X.I.Gf
  [sNf : SigmaFinite μNf]
  lam : Measure X.I.GA

attribute [instance] cu_NObj.sN cu_NObj.sNf

namespace cu_NObj

variable {X : CData} (O : cu_NObj X)

def μNA : Measure X.I.GA := (Measure.pi O.μN).prod O.μNf

def IsOn (W : Submodule X.I.E (Fin X.I.n → X.I.E)) : Prop := O.μNA (X.I.NA W)ᶜ = 0

def IsWeil : Prop :=
  ∀ F : X.I.GA → ℂ, Integrable F (cu_mu X) → ∫ y, F y ∂(cu_mu X) = ∫ y, ∫ n, F (n * y) ∂O.μNA ∂O.lam

def CstInv (ν : Measure X.I.GA) (f : X.I.GA → ℂ) : Prop :=
  ∀ᵐ y ∂O.lam, ∃ c : ℂ, ∀ᵐ n ∂O.μNA, cu_cst X ν f (n * y) = c

def PhPZero (x : X.I.GA) : Prop :=
  ∃ v, ∀ᵐ y ∂O.lam, ∫ n, phLoc (X.I.ε v) (X.σ v) (X.w v) ((x.1 v)⁻¹ * (n * y.1 v)) ∂(O.μN v) = 0

theorem inner_eq (x y : X.I.GA) :
    ∫ n, X.φ (x⁻¹ * (n * y)) ∂O.μNA =
      (∏ v, ∫ n, phLoc (X.I.ε v) (X.σ v) (X.w v) ((x.1 v)⁻¹ * (n * y.1 v)) ∂(O.μN v)) *
        ∫ n, X.e (x.2⁻¹ * (n * y.2)) ∂O.μNf := by
  unfold μNA
  rw [← integral_fintype_prod_eq_prod (𝕜 := ℂ) (μ := O.μN)
    (fun v n => phLoc (X.I.ε v) (X.σ v) (X.w v) ((x.1 v)⁻¹ * (n * y.1 v)))]
  rw [← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  show X.φ (x⁻¹ * (n * y)) = _
  unfold CData.φ phe
  rw [X.phOf_eq_prod]
  rfl

theorem inner_zero {x : X.I.GA} (h : O.PhPZero x) : ∀ᵐ y ∂O.lam, ∫ n, X.φ (x⁻¹ * (n * y)) ∂O.μNA = 0 := by
  obtain ⟨v, hv⟩ := h
  filter_upwards [hv] with y hy
  rw [O.inner_eq, Finset.prod_eq_zero (Finset.mem_univ v) hy, zero_mul]

end cu_NObj

def cu_Repro (X : CData) (ν : Measure X.I.GA) (f : X.I.GA → ℂ) : Prop :=
  ∀ᵐ x ∂(cu_mu X),
    Integrable (fun p : X.I.GA × X.I.GA => f (p.1 * x * p.2) * X.φ p.2) (ν.prod (cu_mu X)) ∧
      ∀ᵐ m ∂ν, f (m * x) = ∫ g, f (m * x * g) * X.φ g ∂(cu_mu X)



namespace cu

variable (X : CData)

def ReproStep : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ ν : Measure X.I.GA, X.I.IsNQuotMeas W ν →
      cu_Repro X ν (X.I.ext Fv)

def UnipStep : Prop :=
  ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∃ O : cu_NObj X, O.IsOn W ∧ O.IsWeil ∧
    (∀ x, O.PhPZero x) ∧
    ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
      ∀ ν : Measure X.I.GA, X.I.IsNQuotMeas W ν → O.CstInv ν (X.I.ext Fv)

end cu


def cu_wt (X : CData) (s : ℝ) (g : X.I.GA) : ℝ := Real.exp (s * ∑ v, cartanDistance (X.I.ε v) (g.1 v))

namespace cu

variable (X : CData)

def HaarGrowth : Prop :=
  ∀ s : ℝ, 0 ≤ s →
    (∀ v, 1 ≤ q0At X.I v →
      2 * (X.I.n : ℝ) * Real.sqrt (2 * (q0At X.I v : ℝ)) + s < X.h / 8 / Real.sqrt (2 * (q0At X.I v : ℝ))) →
    Integrable (fun g => ‖X.φ g‖ * cu_wt X s g) (cu_mu X)

def GrowthStep : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ ν : Measure X.I.GA, X.I.IsNQuotMeas W ν →
      ∀ᵐ x ∂(cu_mu X), ∃ B : ℝ, ∀ᵐ p ∂(ν.prod (cu_mu X)), X.φ p.2 ≠ 0 →
        ‖X.I.ext Fv (p.1 * x * p.2)‖ ≤ B * cu_wt X (2 * (X.I.n : ℝ) ^ 2) p.2

def MeasStep : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ ν : Measure X.I.GA, X.I.IsNQuotMeas W ν →
      ∀ᵐ x ∂(cu_mu X), AEStronglyMeasurable (fun p : X.I.GA × X.I.GA => X.I.ext Fv (p.1 * x * p.2)) (ν.prod (cu_mu X))

def PointRepro : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ ν : Measure X.I.GA, X.I.IsNQuotMeas W ν →
      ∀ᵐ x ∂(cu_mu X), ∀ᵐ m ∂ν,
        X.I.ext Fv (m * x) = ∫ g, X.I.ext Fv (m * x * g) * X.φ g ∂(cu_mu X)

end cu





def cu_absS (X : CData) (x : X.I.GA) : ℝ≥0∞ := ∑' γ : X.I.GFset, ‖X.φ (x⁻¹ * (γ : X.I.GA) * x)‖ₑ

def cu_Kc (X : CData) (B : ℝ) : ℝ := (Real.exp B / (1 - Real.exp (-B))) ^ Fintype.card (InfinitePlace X.I.F)

theorem cu_one_le_Kc (X : CData) {B : ℝ} (hB : 0 < B) : 1 ≤ cu_Kc X B := by
  unfold cu_Kc
  apply one_le_pow₀
  have h1 : 0 < Real.exp (-B) := Real.exp_pos _
  have h2 : Real.exp (-B) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h3 : 1 ≤ Real.exp B := Real.one_le_exp hB.le
  rw [le_div_iff₀ (by linarith)]
  linarith

open Classical in

theorem cu_absS_le (X : CData) (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower)
    (hE : X.LowProj) {q₀ : ℕ} (hq : ∀ v, q0At X.I v = q₀) {Ac B : ℝ} (hAc : 0 ≤ Ac) (hB : 0 < B)
    (hr : 1 ≤ q₀ → 16 * B * Real.sqrt (2 * (q₀ : ℝ)) ≤ X.h) {x : X.I.GA} (hcnt : X.FarCount Ac B {x}) :
    cu_absS X x ≤ ENNReal.ofReal (fdegAll X.I X.σ X.w * (X.e 1).re * (Ac * cu_Kc X B)) := by
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  set k0 : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hk0
  have hk0n : 0 ≤ k0 := mul_nonneg X.fdegAll_nonneg (X.e_one_nonneg hp)
  set bd : X.I.GFset → ℝ := fun γ => ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp X.h q₀ (X.dist x γ v))) with hbd
  have hbdn : ∀ γ, 0 ≤ bd γ := fun γ => Finset.prod_nonneg fun v _ => (Real.exp_pos _).le
  unfold cu_absS
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set S : Finset X.I.GFset := s.filter (fun γ : X.I.GFset => X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) with hS
  have hterm : ∀ γ ∈ s, ‖X.φ (x⁻¹ * (γ : X.I.GA) * x)‖ₑ ≤
      (if X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 then ENNReal.ofReal (k0 * bd γ) else 0) := by
    intro γ _
    by_cases h0 : X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0
    · simp [h0]
    · rw [if_pos h0, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (X.norm_φ_le D hdec hX h1 hE hq _)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, ← ENNReal.ofReal_sum_of_nonneg (fun γ _ => mul_nonneg hk0n (hbdn γ)), ← Finset.mul_sum]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hk0n)
  have hc : ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, X.dist x γ v ≤ r v).card : ℝ) ≤ Ac * Real.exp (B * ∑ v, r v) := by
    intro r hr0
    refine hcnt x rfl r hr0 _ fun γ hγ => ?_
    have h3 := Finset.mem_filter.1 hγ
    exact ⟨(Finset.mem_filter.1 h3.1).2, h3.2⟩
  rcases Nat.eq_zero_or_pos q₀ with h0 | hq1
  ·
    have hd : ∀ γ v, X.dist x γ v = 0 := fun γ v => cartan_distance_eq_zero_of_definite (by have := hq v; rw [h0] at this; exact this) _
    have hb1 : ∀ γ, bd γ = 1 := fun γ => by
      simp only [hbd, hd, Formalism.HermitianLatticeCounting.S7.decExp]
      simp
    have h4 := hc (fun _ => 0) (fun _ => le_rfl)
    simp only [hd, le_refl, implies_true, Finset.filter_true, Finset.sum_const_zero, mul_zero, Real.exp_zero,
      mul_one] at h4
    simp only [hb1, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact le_trans h4 (le_mul_of_one_le_right hAc (cu_one_le_Kc X hB))
  · exact Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.allSumRate (InfinitePlace X.I.F) X.I.GFset S (X.dist x) Ac B X.h q₀ hq1 hAc hB (hr hq1)
      (fun γ _ v => cartan_distance_nonneg _ _) hc


namespace cu

variable (X : CData)

def Act (t : ℝ) : ℝ := (3 * Real.sqrt (X.I.n : ℝ) / t ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f)

def SizeStep : Prop :=
  ∃ τ : X.I.GA → ℝ, (∀ y, 0 < τ y) ∧ (∀ γ ∈ X.I.GFset, ∀ y, τ (γ * y) = τ y) ∧
    (∀ y, X.FarCount (Act X (τ y)) (2 * (X.I.n : ℝ) ^ 2) {y}) ∧
    (∀ y g, X.φ g ≠ 0 → τ y * Real.exp (-(1 / (X.I.f : ℝ)) * ∑ v, cartanDistance (X.I.ε v) (g.1 v)) ≤ τ (y * g)) ∧
    ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ x, ∃ c : ℝ, 0 < c ∧ ∀ m ∈ X.I.NA W, c ≤ τ (m * x)

def NullStep : Prop :=
  ∀ Z : Set X.I.GA, X.μ Z = 0 → ∀ ν : Measure X.I.GA, IsFiniteMeasure ν →
    ∀ᵐ x ∂(cu_mu X), ∀ᵐ p ∂(ν.prod (cu_mu X)), X.I.rep X.fund (p.1 * x * p.2) ∉ Z

def FinStep : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → FiniteDimensional ℂ (X.rg T)

end cu




namespace cu

variable (X : CData)

def MeasMul : Prop := Measurable fun p : X.I.GA × X.I.GA => p.1 * p.2

def CountGF : Prop := (X.I.GFset).Countable

def ExtMeas : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T, AEStronglyMeasurable (X.I.ext Fv) (cu_mu X)

def ReproAE : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∀ᵐ z ∂(cu_mu X), X.I.ext Fv z = ∫ g, X.I.ext Fv (z * g) * X.φ g ∂(cu_mu X)

end cu

section Gen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]



end Gen







namespace cu_NObj

variable {X : CData} (O : cu_NObj X)

def IsWeilNull : Prop :=
  ∀ Z : Set X.I.GA, cu_mu X Z = 0 → ∀ᵐ y ∂O.lam, ∀ᵐ n ∂O.μNA, n * y ∉ Z

def RInv (v : InfinitePlace X.I.F) : Prop :=
  ∀ᵐ n₀ ∂(O.μN v), ∀ F : Formalism.REAL.UJ (X.I.ε v) → ℂ, ∫ n, F (n * n₀) ∂(O.μN v) = ∫ n, F n ∂(O.μN v)

def LocZero (v : InfinitePlace X.I.F) : Prop :=
  ∀ a : Formalism.REAL.UJ (X.I.ε v), ∀ᵐ b ∂(Formalism.REAL.muG (X.I.ε v)),
    ∫ n, phLoc (X.I.ε v) (X.σ v) (X.w v) (a⁻¹ * (n * b)) ∂(O.μN v) = 0


end cu_NObj

namespace cu

variable (X : CData)

def ExtInv : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∃ f' : X.I.GA → ℂ, (∀ γ ∈ X.I.GFset, ∀ y, f' (γ * y) = f' y) ∧ X.I.ext Fv =ᵐ[cu_mu X] f'

def UnipFine : Prop :=
  ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∃ O : cu_NObj X, O.IsOn W ∧ O.IsWeil ∧ O.IsWeilNull ∧
    O.μNA ≠ 0 ∧ ∃ v, O.RInv v ∧ O.LocZero v

end cu



namespace cu

def Fine (X : CData) : Prop :=
  UnipFine X ∧ HaarGrowth X ∧ SizeStep X ∧ X.KernelDiag ∧ ReproAE X ∧ ExtInv X ∧ ExtMeas X ∧ MeasMul X ∧ CountGF X

end cu


def cu_StepsCusp (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → cu.Fine X



end Formalism.MainNotions.LeviCoordinates
