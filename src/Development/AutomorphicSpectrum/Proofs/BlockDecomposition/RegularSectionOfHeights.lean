import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightRightTranslateCompactBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartz
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerIntegrableWeylOrbit
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientLeviEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientUnipotentLeviInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulRight

section
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FamMajorant

theorem fam_majorant : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
    ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ → IsLaw χ s₁ φ →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  rintro D n H hH ⟨C, hC, hcov⟩ χ s₁ φ hφ hlaw
  have hHpos : ∀ g, 0 < (H g : ℝ) := fun g => NNReal.coe_pos.2 (hH.2.1 g)
  have hpos : ∀ g, 0 < (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := fun g => Real.rpow_pos_of_pos (hHpos g) _
  have hcont : Continuous fun g => ‖φ g‖ / (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) :=
    hφ.norm.div ((NNReal.continuous_coe.comp hH.1).rpow_const fun g => Or.inl (hHpos g).ne') fun g => (hpos g).ne'
  obtain ⟨δ, hδ⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  have hB0 : 0 ≤ max δ 0 := le_max_right _ _
  have hon : ∀ c ∈ C, ‖φ c‖ ≤ max δ 0 * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    intro c hc
    have h1 := (hδ c hc).trans (le_max_left δ 0)
    rwa [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (hpos c).le), div_le_iff₀ (hpos c)] at h1
  have hall : ∀ g, ‖φ g‖ ≤ max δ 0 * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    intro g
    obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
    have hr : 0 < absA D (Matrix.GeneralLinearGroup.det a) := hom_pos _ _
    rw [hlaw q hq a ha c, hH.2.2 q hq a ha c]
    have e1 : ‖npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)‖ =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
      rw [norm_npow hr]; congr 1; simp
    have e2 : ((absA D (Matrix.GeneralLinearGroup.det a) * H c : ℝ≥0) : ℝ) ^ (s₁.re + (n : ℝ) / 2) =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
      rw [NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    rw [e2, norm_mul, norm_mul, e1]
    simp only [Circle.norm_coe, one_mul]
    have h0 : 0 ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) :=
      Real.rpow_nonneg (NNReal.coe_nonneg _) _
    calc _ ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) *
          (max δ 0 * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2)) := mul_le_mul_of_nonneg_left (hon c hc) h0
      _ = _ := by ring
  refine ⟨max δ 0, hB0, fun z g => ?_⟩
  have e3 : ‖npow (H g) (z - s₁)‖ = (H g : ℝ) ^ (z.re - s₁.re) := by
    rw [norm_npow (hH.2.1 g)]; congr 1
  have e4 : (H g : ℝ) ^ (z.re + (n : ℝ) / 2) = (H g : ℝ) ^ (z.re - s₁.re) * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    rw [← Real.rpow_add (hHpos g)]; congr 1; ring
  have h0 : 0 ≤ (H g : ℝ) ^ (z.re - s₁.re) := (Real.rpow_pos_of_pos (hHpos g) _).le
  simp only [fam]
  rw [norm_mul, e3, e4]
  calc _ ≤ (H g : ℝ) ^ (z.re - s₁.re) * (max δ 0 * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (hall g) h0
    _ = _ := by ring

end GlobalTheory.CompanionTheory.FamMajorant

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_family_height_bound : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ → IsLaw χ s₁ φ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FamMajorant.fam_majorant
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_right_translate_compact_bound : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ C : Set (G D n), IsCompact C → ∃ κ : ℝ, 1 ≤ κ ∧ ∀ c ∈ C, ∀ x : G D n, (H (x * c) : ℝ) ≤ κ * (H x : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le | exact GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le | (intros; apply GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le <;> assumption)
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ShearGrowth

open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply block_diagonal_mul mat_mul')
open GlobalTheory.CompanionTheory.FourierN (mat_injective)

def rr {ι : Type} [Fintype ι] {a b : ℕ} (z : ι → Fin a → Fin b → ℂ) : ℝ :=
  1 + ∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2

theorem one_le_rr {ι : Type} [Fintype ι] {a b : ℕ} (z : ι → Fin a → Fin b → ℂ) : 1 ≤ rr z := by
  unfold rr
  have : 0 ≤ ∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith

theorem norm_le_rr {ι : Type} [Fintype ι] {a b : ℕ} (z : ι → Fin a → Fin b → ℂ) : ‖z‖ ≤ rr z := by
  have h0 : (0 : ℝ) ≤ rr z := zero_le_one.trans (one_le_rr z)
  refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun i =>
    (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have h1 : ‖z τ i j‖ ^ 2 ≤ ∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2 := by
    have hj : ‖z τ i j‖ ^ 2 ≤ ∑ j, ‖z τ i j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖z τ i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    have hi : ∑ j, ‖z τ i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖z τ i j‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ∑ j, ‖z τ i j‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
    have ht : ∑ i, ∑ j, ‖z τ i j‖ ^ 2 ≤ ∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2 :=
      Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, ‖z τ i j‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ τ)
    linarith
  unfold rr
  nlinarith [sq_nonneg (‖z τ i j‖ - 1)]

theorem rr_temperate {ι : Type} [Fintype ι] {a b : ℕ} (L : ℕ) :
    (fun z : ι → Fin a → Fin b → ℂ => ((rr z : ℝ) : ℂ) ^ L).HasTemperateGrowth := by
  have hc : ∀ (τ : ι) (i : Fin a) (j : Fin b),
      (fun z : ι → Fin a → Fin b → ℂ => ‖z τ i j‖ ^ 2).HasTemperateGrowth := fun τ i j => by
    let P : (ι → Fin a → Fin b → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin b => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin b → ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin a → Fin b → ℂ) τ))
    exact (Function.hasTemperateGrowth_norm_sq ℂ).comp P.hasTemperateGrowth
  have hr : (fun z : ι → Fin a → Fin b → ℂ => rr z).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (1 : ℝ)).add
      (Function.HasTemperateGrowth.sum fun τ _ => Function.HasTemperateGrowth.sum fun i _ =>
        Function.HasTemperateGrowth.sum fun j _ => hc τ i j)
  exact (Complex.ofRealCLM.hasTemperateGrowth.comp hr).pow L

theorem pow_bound {Γ : Type} [Group Γ] (h : Γ → ℝ) (e : ℝ → Γ) (he : ∀ u v, e (u + v) = e u * e v)
    (κ : ℝ) (hκ : 1 ≤ κ) (hb : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ x, h (x * e u) ≤ κ * h x) (hpos : ∀ x, 0 ≤ h x) :
    ∀ (k : ℕ) (u : ℝ), |u| ≤ k → ∀ x, h (x * e u) ≤ κ ^ k * h x := by
  have he0 : e 0 = 1 := by
    have := he 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  intro k
  induction k with
  | zero =>
    intro u hu x
    have : u = 0 := by simpa using hu
    simp [this, he0]
  | succ k ih =>
    intro u hu x
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hu' : |u| ≤ (k : ℝ) + 1 := by simpa using hu
    have hw : u / (k + 1) ∈ Set.Icc (-1 : ℝ) 1 := by
      have : |u / ((k : ℝ) + 1)| ≤ 1 := by
        rw [abs_div, abs_of_pos hk, div_le_one hk]; exact hu'
      exact abs_le.1 this
    have hv : |u - u / (k + 1)| ≤ k := by
      have : u - u / ((k : ℝ) + 1) = u / ((k : ℝ) + 1) * k := by field_simp; ring
      rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have h1 : |u / ((k : ℝ) + 1)| ≤ 1 := abs_le.2 hw
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have e1 : u = u / (k + 1) + (u - u / (k + 1)) := by ring
    calc h (x * e u) = h (x * e (u / (k + 1)) * e (u - u / (k + 1))) := by
          rw [mul_assoc, ← he, ← e1]
      _ ≤ κ ^ k * h (x * e (u / (k + 1))) := ih _ hv _
      _ ≤ κ ^ k * (κ * h x) := by gcongr; exact hb _ hw x
      _ = κ ^ (k + 1) * h x := by ring

theorem exists_compact_fin (D : D7) (θ : InfFam D) (ρ p : ℕ) (Φ : Mx D ρ p → ℂ) (hΦ : Φ ∈ schwartzA θ ρ p) :
    ∃ S : Set (Fin ρ → Fin p → Af D.host.F ⊗[D.host.F] D.host.E), IsCompact S ∧
      ∀ y, Φ y ≠ 0 → (fun i j => finPart D (y i j)) ∈ S := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨tsupport g, hg.2, fun y hy => subset_tsupport _ ?_⟩
    exact fun h0 => hy (by simp only [h0, mul_zero])
  | zero => exact ⟨∅, isCompact_empty, fun y hy => absurd rfl hy⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨S₁, c₁, s₁⟩ := h1
    obtain ⟨S₂, c₂, s₂⟩ := h2
    refine ⟨S₁ ∪ S₂, c₁.union c₂, fun y hy => ?_⟩
    by_cases h : Φ y = 0
    · exact Or.inr (s₂ y fun h' => hy (by simp [h, h']))
    · exact Or.inl (s₁ y h)
  | smul c Φ _ h =>
    obtain ⟨S, cS, sS⟩ := h
    exact ⟨S, cS, fun y hy => sS y fun h' => hy (by simp [h'])⟩

section Dil

variable {R : Type} [CommRing R] {n ρ p : ℕ}

theorem blockMatrix_smul_one_mul (hn : ρ + p = n) (α β : R) :
    HMul.hMul (bl hn (α • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) (bl hn (β • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) =
      bl hn ((α * β) • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1 := by
  rw [blockMatrix_multiply]
  congr 1
  · simp [smul_smul, mul_comm]
  · simp
  · simp
  · simp

theorem blockMatrix_conj_upperUnipotent (hn : ρ + p = n) (α β : R) (h : α * β = 1) (y : Matrix (Fin ρ) (Fin p) R) :
    HMul.hMul (HMul.hMul (bl hn (α • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) (bl hn 1 y 0 1))
        (bl hn (β • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) = bl hn 1 (α • y) 0 1 := by
  rw [blockMatrix_multiply, blockMatrix_multiply]
  congr 1
  · simp [smul_smul, mul_comm β α, h]
  · simp
  · simp
  · simp

theorem blockMatrix_conj_lowerUnipotent (hn : ρ + p = n) (α β : R) (h : α * β = 1) (c : Matrix (Fin p) (Fin ρ) R) :
    HMul.hMul (HMul.hMul (bl hn (β • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) (bl hn 1 0 c 1))
        (bl hn (α • (1 : Matrix (Fin ρ) (Fin ρ) R)) 0 0 1) = bl hn 1 0 (α • c) 1 := by
  rw [blockMatrix_multiply, blockMatrix_multiply]
  congr 1
  · simp [smul_smul, h, mul_comm β α]
  · simp
  · simp
  · simp

end Dil

theorem exists_real_idele (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) :
    ∃ a : ℝ → AE D, Continuous a ∧ (∀ u v, a u * a v = a (u + v)) ∧ a 0 = 1 ∧
      (∀ u τ, θ τ (infPart D (a u)) = (Real.exp u : ℂ)) ∧ ∀ u, finPart D (a u) = 1 := by
  obtain ⟨e1, he1⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ 1 1
  have hinj : ∀ x x' : AE D, (∀ τ, θ τ (infPart D x) = θ τ (infPart D x')) → finPart D x = finPart D x' → x = x' := by
    intro x x' h1 h2
    have : (Matrix.of fun _ _ => x : Mx D 1 1) = Matrix.of fun _ _ => x' := by
      apply e1.injective
      rw [he1, he1]
      refine Prod.ext ?_ ?_
      · funext τ i j; exact h1 τ
      · funext i j; exact h2
    exact congrFun (congrFun this 0) 0
  let pt : ℝ → (D.what₂.Tau → Fin 1 → Fin 1 → ℂ) × (Fin 1 → Fin 1 → GlobalTheory.RegSch.IkSchwartz.AEf D) :=
    fun u => (fun _ _ _ => (Real.exp u : ℂ), fun _ _ => 1)
  have hpt : Continuous pt := by
    refine Continuous.prodMk ?_ continuous_const
    exact continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ =>
      Complex.continuous_ofReal.comp Real.continuous_exp
  let a : ℝ → AE D := fun u => e1.symm (pt u) 0 0
  have ha1 : ∀ u τ, θ τ (infPart D (a u)) = (Real.exp u : ℂ) := fun u τ => by
    have := congrArg Prod.fst (he1 (e1.symm (pt u)))
    rw [e1.apply_symm_apply] at this
    exact (congrFun (congrFun (congrFun this τ) 0) 0).symm
  have ha2 : ∀ u, finPart D (a u) = 1 := fun u => by
    have := congrArg Prod.snd (he1 (e1.symm (pt u)))
    rw [e1.apply_symm_apply] at this
    exact (congrFun (congrFun this 0) 0).symm
  refine ⟨a, (e1.symm.continuous.comp hpt).matrix_elem 0 0, fun u v => hinj _ _ (fun τ => ?_) ?_, hinj _ _ (fun τ => ?_) ?_, ha1, ha2⟩
  · rw [map_mul, map_mul, ha1, ha1, ha1, Real.exp_add, Complex.ofReal_mul]
  · rw [map_mul, ha2, ha2, ha2, one_mul]
  · rw [ha1, map_one, map_one]; simp
  · rw [ha2, map_one]

set_option maxHeartbeats 1000000 in

theorem dil_exists : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn),
    ∃ e : ℝ → G D n, Continuous e ∧ (∀ u v, e (u + v) = e u * e v) ∧
      ∀ (u : ℝ) (y y' : Mx D ρ p), (∀ τ i j, compAt θ τ y' i j = (Real.exp u : ℂ) * compAt θ τ y i j) →
        (∀ i j, finPart D (y' i j) = finPart D (y i j)) → M.sh y' = e u * M.sh y * e (-u) := by
  intro D θ hθ n ρ p hn M
  obtain ⟨a, hac, hmul, ha0, ha1, ha2⟩ := exists_real_idele D θ hθ
  obtain ⟨e0, he0⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ ρ p
  let A : ℝ → Mx D n n := fun u => bl hn (a u • (1 : Mx D ρ ρ)) 0 0 1
  have hA : ∀ u v, A u * A v = A (u + v) := fun u v => by
    show HMul.hMul _ _ = _
    rw [blockMatrix_smul_one_mul, hmul]
  have hA0 : A 0 = 1 := by
    show bl hn (a 0 • (1 : Mx D ρ ρ)) 0 0 1 = 1
    rw [ha0, one_smul]; exact GlobalTheory.CompanionTheory.PcB.blockMatrix_one hn
  have hAc : Continuous A := by
    have h1 : Continuous fun u => a u • (1 : Mx D ρ ρ) := by
      haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
      exact continuous_matrix fun i j => (hac.mul continuous_const : Continuous fun u => a u * (1 : Mx D ρ ρ) i j)
    exact (h1.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_submatrix _ _
  have hex : ∀ u, ∃ g : G D n, mat g = blk4 (A u) 0 0 (adj (A (-u))) := fun u =>
    GlobalTheory.StdUnn.Model.exists_levi ⟨A u, A (-u), by rw [hA, add_neg_cancel, hA0], by rw [hA, neg_add_cancel, hA0]⟩
  choose e he using hex
  have hadd : ∀ u v, e (u + v) = e u * e v := fun u v => by
    apply mat_injective
    rw [mat_mul', he, he, he, block_diagonal_mul]
    congr 1
    · exact (hA u v).symm
    · show _ = adj (A (-u)) * adj (A (-v))
      rw [← adj_mul, hA, neg_add_rev, add_comm (-v)]
  have he0' : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hinv : ∀ u, (e u)⁻¹ = e (-u) := fun u => by
    rw [inv_eq_iff_mul_eq_one, ← hadd, add_neg_cancel, he0']
  have hmc : Continuous fun u => mat (e u) := by
    simp only [he]
    exact ((hAc.matrix_fromBlocks continuous_const continuous_const
      (GlobalTheory.CompanionTheory.JacobiMaps.continuous_adjR.comp (hAc.comp continuous_neg))).matrix_submatrix _ _)
  refine ⟨e, GlobalTheory.StdUnn.continuous_of_mat_pt hmc ?_, hadd, fun u y y' h1 h2 => ?_⟩
  · simp only [hinv]
    exact hmc.comp continuous_neg
  have hy : y' = a u • y := by
    apply e0.injective
    rw [he0, he0]
    refine Prod.ext ?_ ?_
    · funext τ i j
      show compAt θ τ y' i j = θ τ (infPart D (a u * y i j))
      rw [h1, map_mul, map_mul, ha1]; rfl
    · funext i j
      show finPart D (y' i j) = finPart D (a u * y i j)
      rw [h2, map_mul, ha2, one_mul]
  apply mat_injective
  rw [mat_mul', mat_mul', he, he, M.sh_mat, M.sh_mat, block_diagonal_mul, block_diagonal_mul]
  have hau : a u * a (-u) = 1 := by rw [hmul, add_neg_cancel, ha0]
  have hcu : cA D (a u) * cA D (a (-u)) = 1 := by rw [← map_mul, hau, map_one]
  have hadjA : ∀ v, adj (A v) = bl hn (cA D (a v) • (1 : Mx D ρ ρ)) 0 0 1 := fun v => by
    show adj (bl hn (a v • (1 : Mx D ρ ρ)) 0 0 1) = _
    rw [GlobalTheory.CompanionTheory.JacobiMaps.adj_bl, adj_zero, adj_zero, adj_one, GlobalTheory.MixModel.adj_smul, adj_one]
  congr 1
  · rw [hy]
    exact (blockMatrix_conj_upperUnipotent hn (a u) (a (-u)) hau y).symm
  · rw [neg_neg, hadjA, hadjA, hy]
    have := blockMatrix_conj_lowerUnipotent hn (cA D (a u)) (cA D (a (-u))) hcu (-adj y)
    rw [this]
    congr 2
    rw [GlobalTheory.MixModel.adj_smul, smul_neg]

theorem exists_shear_bound (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (θ : InfFam D) (hθ : IsInfFam θ)
    (H : G D n → ℝ≥0) (hH : IsHt H) (hC : ∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c)
    (Φ : Mx D ρ p → ℂ) (hΦ : Φ ∈ schwartzA θ ρ p) :
    ∃ (A : ℝ) (N : ℕ), 0 < A ∧ ∀ (x : G D n) (y : Mx D ρ p), Φ y ≠ 0 →
      (H (x * M.sh y) : ℝ) ≤ A * rr (fun τ i j => compAt θ τ y i j) ^ N * (H x : ℝ) := by
  obtain ⟨e, hec, hea, hes⟩ := dil_exists D θ hθ n ρ p hn M
  obtain ⟨S, hS, hsupp⟩ := exists_compact_fin D θ ρ p Φ hΦ
  obtain ⟨e0, he0⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ ρ p
  have hB : IsCompact (e0.symm '' (Metric.closedBall (0 : D.what₂.Tau → Fin ρ → Fin p → ℂ) 1 ×ˢ {0})) :=
    ((isCompact_closedBall _ _).prod isCompact_singleton).image e0.symm.continuous
  have hCf : IsCompact (e0.symm '' (({0} : Set (D.what₂.Tau → Fin ρ → Fin p → ℂ)) ×ˢ S)) :=
    (isCompact_singleton.prod hS).image e0.symm.continuous
  obtain ⟨κ₀, hκ₀, hb₀⟩ := GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le D n H hH hC _ ((hB.union hCf).image M.sh_cont)
  obtain ⟨κ₁, hκ₁, hb₁⟩ := GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le D n H hH hC _
    (isCompact_Icc.image hec : IsCompact (e '' Set.Icc (-1 : ℝ) 1))
  have hpw := pow_bound (fun x => (H x : ℝ)) e hea κ₁ hκ₁ (fun u hu x => hb₁ _ ⟨u, hu, rfl⟩ x) (fun x => NNReal.coe_nonneg _)
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.log κ₁)
  have hκE : κ₁ ≤ Real.exp N := by
    calc κ₁ = Real.exp (Real.log κ₁) := (Real.exp_log (lt_of_lt_of_le one_pos hκ₁)).symm
      _ ≤ _ := Real.exp_le_exp.2 hN

  have hg : ∀ (r : ℝ), 1 ≤ r → ∀ u, |u| = Real.log r → ∀ x, (H (x * e u) : ℝ) ≤ Real.exp N * r ^ N * (H x : ℝ) := by
    intro r hr u hu x
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    have hl : 0 ≤ Real.log r := Real.log_nonneg hr
    have h1 := hpw ⌈|u|⌉₊ u (Nat.le_ceil _) x
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (NNReal.coe_nonneg _))
    have hc : (⌈|u|⌉₊ : ℝ) ≤ Real.log r + 1 := by
      have h := Nat.ceil_lt_add_one (abs_nonneg u)
      exact h.le.trans (by rw [hu])
    calc κ₁ ^ ⌈|u|⌉₊ ≤ Real.exp N ^ ⌈|u|⌉₊ := pow_le_pow_left₀ (zero_le_one.trans hκ₁) hκE _
      _ = Real.exp ((N : ℝ) * (⌈|u|⌉₊ : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp ((N : ℝ) * (Real.log r + 1)) := Real.exp_le_exp.2 (by gcongr)
      _ = Real.exp N * r ^ N := by
        rw [mul_add, mul_one, Real.exp_add, mul_comm, mul_comm (N : ℝ), Real.exp_mul, Real.exp_log hr0, Real.rpow_natCast]
  refine ⟨κ₀ ^ 2 * Real.exp N ^ 2, 2 * N, by positivity, fun x y hy => ?_⟩
  set z : D.what₂.Tau → Fin ρ → Fin p → ℂ := fun τ i j => compAt θ τ y i j with hz
  set f : Fin ρ → Fin p → Af D.host.F ⊗[D.host.F] D.host.E := fun i j => finPart D (y i j) with hf
  have hey : e0 y = (z, f) := he0 y
  set r := rr z with hr
  have hr1 : 1 ≤ r := one_le_rr z
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  set y₀ := e0.symm (r⁻¹ • z, 0) with hy₀
  set y₁ := e0.symm (z, 0) with hy₁
  set y₂ := e0.symm (0, f) with hy₂
  have hsum : y = y₁ + y₂ := by
    apply e0.injective
    rw [map_add, hy₁, hy₂, e0.apply_symm_apply, e0.apply_symm_apply, hey]
    simp
  have hc₀ : ∀ τ i j, compAt θ τ y₀ i j = r⁻¹ • z τ i j := fun τ i j => by
    have := congrArg Prod.fst (he0 y₀)
    rw [hy₀, e0.apply_symm_apply] at this
    exact (congrFun (congrFun (congrFun this τ) i) j).symm
  have hc₁ : ∀ τ i j, compAt θ τ y₁ i j = z τ i j := fun τ i j => by
    have := congrArg Prod.fst (he0 y₁)
    rw [hy₁, e0.apply_symm_apply] at this
    exact (congrFun (congrFun (congrFun this τ) i) j).symm
  have hf₀ : ∀ i j, finPart D (y₀ i j) = 0 := fun i j => by
    have := congrArg Prod.snd (he0 y₀)
    rw [hy₀, e0.apply_symm_apply] at this
    exact (congrFun (congrFun this i) j).symm
  have hf₁ : ∀ i j, finPart D (y₁ i j) = 0 := fun i j => by
    have := congrArg Prod.snd (he0 y₁)
    rw [hy₁, e0.apply_symm_apply] at this
    exact (congrFun (congrFun this i) j).symm
  have hsh₁ : M.sh y₁ = e (Real.log r) * M.sh y₀ * e (-Real.log r) := by
    refine hes _ y₀ y₁ (fun τ i j => ?_) (fun i j => by rw [hf₀, hf₁])
    rw [hc₀, hc₁, Real.exp_log hr0, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (by exact_mod_cast hr0.ne'), one_mul]
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hy₀B : M.sh y₀ ∈ M.sh '' ((e0.symm '' (Metric.closedBall (0 : D.what₂.Tau → Fin ρ → Fin p → ℂ) 1 ×ˢ {0})) ∪
      (e0.symm '' (({0} : Set (D.what₂.Tau → Fin ρ → Fin p → ℂ)) ×ˢ S))) := by
    refine ⟨y₀, Or.inl ⟨(r⁻¹ • z, 0), ⟨?_, rfl⟩, rfl⟩, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le]
    exact inv_mul_le_one_of_le₀ (norm_le_rr z) hr0.le
  have hy₂C : M.sh y₂ ∈ M.sh '' ((e0.symm '' (Metric.closedBall (0 : D.what₂.Tau → Fin ρ → Fin p → ℂ) 1 ×ˢ {0})) ∪
      (e0.symm '' (({0} : Set (D.what₂.Tau → Fin ρ → Fin p → ℂ)) ×ˢ S))) :=
    ⟨y₂, Or.inr ⟨(0, f), ⟨rfl, hsupp y hy⟩, rfl⟩, rfl⟩
  have hexp : M.sh y = e (Real.log r) * M.sh y₀ * e (-Real.log r) * M.sh y₂ := by
    rw [← hsh₁, GlobalTheory.CompanionTheory.FJE.sh_add, ← hsum]
  have hE : 0 ≤ Real.exp N * r ^ N := by positivity
  have hκ₀' : 0 ≤ κ₀ := zero_le_one.trans hκ₀
  have s1 := hb₀ _ hy₂C (x * e (Real.log r) * M.sh y₀ * e (-Real.log r))
  have s2 := hg r hr1 (-Real.log r) (by rw [abs_neg, abs_of_nonneg hl]) (x * e (Real.log r) * M.sh y₀)
  have s3 := hb₀ _ hy₀B (x * e (Real.log r))
  have s4 := hg r hr1 (Real.log r) (abs_of_nonneg hl) x
  have e1 : x * M.sh y = x * e (Real.log r) * M.sh y₀ * e (-Real.log r) * M.sh y₂ := by
    rw [hexp]; simp only [mul_assoc]
  rw [e1]
  calc (H (x * e (Real.log r) * M.sh y₀ * e (-Real.log r) * M.sh y₂) : ℝ)
      ≤ κ₀ * (Real.exp N * r ^ N * (κ₀ * (Real.exp N * r ^ N * (H x : ℝ)))) := by
        refine s1.trans (mul_le_mul_of_nonneg_left ?_ hκ₀')
        refine s2.trans (mul_le_mul_of_nonneg_left ?_ hE)
        exact s3.trans (mul_le_mul_of_nonneg_left s4 hκ₀')
    _ = κ₀ ^ 2 * Real.exp N ^ 2 * r ^ (2 * N) * (H x : ℝ) := by ring

theorem height_shear_majorant : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (θ : InfFam D), IsInfFam θ →
  ∀ H : G D n → ℝ≥0, IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ Φ ∈ schwartzA θ ρ p, ∀ τ : ℝ, 0 ≤ τ → ∃ W : Mx D ρ p → ℝ, Integrable W m.μ ∧
    ∀ (x : G D n) (y : Mx D ρ p), (H (x * M.sh y) : ℝ) ^ τ * ‖Φ y‖ ≤ W y * (H x : ℝ) ^ τ := by
  intro D n ρ p hn M m θ hθ H hH hC Φ hΦ τ hτ
  obtain ⟨A, N, hA, hb⟩ := exists_shear_bound D n ρ p hn M θ hθ H hH hC Φ hΦ
  set L := ⌈(N : ℝ) * τ⌉₊ with hL
  have hmem := GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA D θ ρ p _ (rr_temperate (ι := D.what₂.Tau) (a := ρ) (b := p) L) Φ hΦ
  have hint := GlobalTheory.SchwartzAInt.integrable_of_mem D θ hθ ρ p m.μ m.𝓕 m.hμ _ hmem
  refine ⟨fun y => A ^ τ * ‖((rr (fun τ i j => compAt θ τ y i j) : ℝ) : ℂ) ^ L * Φ y‖, hint.norm.const_mul _, fun x y => ?_⟩
  have hH0 : ∀ g, (0 : ℝ) ≤ (H g : ℝ) := fun g => NNReal.coe_nonneg _
  by_cases hy : Φ y = 0
  · simp [hy]
  set r := rr (fun τ i j => compAt θ τ y i j) with hr
  have hr1 : 1 ≤ r := one_le_rr _
  have hr0 : 0 ≤ r := by linarith
  have h1 : (H (x * M.sh y) : ℝ) ^ τ ≤ (A * r ^ N * (H x : ℝ)) ^ τ :=
    Real.rpow_le_rpow (hH0 _) (hb x y hy) hτ
  have h2 : (A * r ^ N * (H x : ℝ)) ^ τ = A ^ τ * (r ^ N) ^ τ * (H x : ℝ) ^ τ := by
    rw [Real.mul_rpow (by positivity) (hH0 _), Real.mul_rpow hA.le (by positivity)]
  have h3 : (r ^ N) ^ τ ≤ r ^ L := by
    rw [← Real.rpow_natCast r N, ← Real.rpow_mul hr0, ← Real.rpow_natCast r L]
    exact Real.rpow_le_rpow_of_exponent_le hr1 (Nat.le_ceil _)
  have h4 : ‖((r : ℝ) : ℂ) ^ L * Φ y‖ = r ^ L * ‖Φ y‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
  show _ ≤ A ^ τ * ‖((r : ℝ) : ℂ) ^ L * Φ y‖ * _
  rw [h4]
  have hAτ : 0 ≤ A ^ τ := Real.rpow_nonneg hA.le _
  have hHτ : 0 ≤ (H x : ℝ) ^ τ := Real.rpow_nonneg (hH0 _) _
  calc (H (x * M.sh y) : ℝ) ^ τ * ‖Φ y‖ ≤ (A ^ τ * (r ^ N) ^ τ * (H x : ℝ) ^ τ) * ‖Φ y‖ := by
        rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (A ^ τ * r ^ L * (H x : ℝ) ^ τ) * ‖Φ y‖ := by gcongr
    _ = A ^ τ * (r ^ L * ‖Φ y‖) * (H x : ℝ) ^ τ := by ring

end GlobalTheory.CompanionTheory.ShearGrowth
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_height_majorant_integrable : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (θ : InfFam D), IsInfFam θ →
  ∀ H : G D n → ℝ≥0, IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ Φ ∈ schwartzA θ ρ p, ∀ τ : ℝ, 0 ≤ τ → ∃ W : Mx D ρ p → ℝ, Integrable W m.μ ∧
    ∀ (x : G D n) (y : Mx D ρ p), (H (x * M.sh y) : ℝ) ^ τ * ‖Φ y‖ ≤ W y * (H x : ℝ) ^ τ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ShearGrowth.height_shear_majorant
end

section
section
open MeasureTheory Filter
open scoped Topology

namespace GlobalTheory.CompanionTheory.Param

theorem continuousOn_differentiableOn_integral :
    ∀ {Y T : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
      [TopologicalSpace T] [FirstCountableTopology T] (μ : Measure Y) (U : Set ℂ), IsOpen U →
      ∀ F : ℂ → T → Y → ℂ,
      ContinuousOn (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (U ×ˢ Set.univ) →
      (∀ t y, DifferentiableOn ℂ (fun z => F z t y) U) →
      (∀ z₀ ∈ U, ∀ t₀ : T, ∃ V ∈ 𝓝 z₀, ∃ N ∈ 𝓝 t₀, ∃ w : Y → ℝ, Integrable w μ ∧
        ∀ z ∈ V, ∀ t ∈ N, ∀ y, ‖F z t y‖ ≤ w y) →
      ContinuousOn (fun u : ℂ × T => ∫ y, F u.1 u.2 y ∂μ) (U ×ˢ Set.univ) ∧
        ∀ t, DifferentiableOn ℂ (fun z => ∫ y, F z t y ∂μ) U := by
  intro Y T _ _ _ _ _ μ U hU F hF hdiff hdom
  have hGat : ∀ z ∈ U, ∀ (t : T) (y : Y),
      ContinuousAt (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (z, t, y) := fun z hz t y =>
    hF.continuousAt ((hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz (Set.mem_univ _)))
  have hslice : ∀ z ∈ U, ∀ t : T, Continuous (fun y => F z t y) := fun z hz t =>
    hF.comp_continuous (f := fun y : Y => (z, t, y)) (by fun_prop)
      fun y => Set.mk_mem_prod hz (Set.mem_univ _)
  refine ⟨?_, fun t => ?_⟩
  · rintro ⟨z₀, t₀⟩ ⟨hz₀, -⟩
    obtain ⟨V, hV, N, hN, w, hw, hbound⟩ := hdom z₀ hz₀ t₀
    refine ContinuousAt.continuousWithinAt ?_
    refine MeasureTheory.continuousAt_of_dominated (bound := w) ?_ ?_ hw ?_
    · have hmem : U ×ˢ (Set.univ : Set T) ∈ 𝓝 (z₀, t₀) :=
        (hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz₀ (Set.mem_univ _))
      filter_upwards [hmem] with x hx
      exact (hslice x.1 hx.1 x.2).aestronglyMeasurable
    · have hmem : V ×ˢ N ∈ 𝓝 (z₀, t₀) := by
        rw [nhds_prod_eq]
        exact Filter.prod_mem_prod hV hN
      filter_upwards [hmem] with x hx
      exact Filter.Eventually.of_forall fun y => hbound x.1 hx.1 x.2 hx.2 y
    · exact Filter.Eventually.of_forall fun y =>
        ContinuousAt.comp_of_eq (f := fun x : ℂ × T => (x.1, x.2, y)) (hGat z₀ hz₀ t₀ y)
          (by fun_prop) rfl
  · obtain ⟨h, -⟩ := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ)
      (F := fun y z => F z t y) hU (fun z hz => (hslice z hz t).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => hdiff t y) (fun z hz => by
        obtain ⟨V, hV, N, hN, w, hw, hb⟩ := hdom z hz t
        exact ⟨V, hV, w, hw, Filter.Eventually.of_forall fun y z' hz' =>
          hb z' hz' t (mem_of_mem_nhds hN) y⟩)
    exact h

end GlobalTheory.CompanionTheory.Param
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_differentiableOn_parameter_integral : ∀ {Y T : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [TopologicalSpace T]
    [FirstCountableTopology T] (μ : Measure Y) (U : Set ℂ), IsOpen U → ∀ F : ℂ → T → Y → ℂ,
  ContinuousOn (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (U ×ˢ Set.univ) →
  (∀ t y, DifferentiableOn ℂ (fun z => F z t y) U) →
  (∀ z₀ ∈ U, ∀ t₀ : T, ∃ V ∈ 𝓝 z₀, ∃ N ∈ 𝓝 t₀, ∃ w : Y → ℝ, Integrable w μ ∧ ∀ z ∈ V, ∀ t ∈ N, ∀ y, ‖F z t y‖ ≤ w y) →
  ContinuousOn (fun u : ℂ × T => ∫ y, F u.1 u.2 y ∂μ) (U ×ˢ Set.univ) ∧
    ∀ t, DifferentiableOn ℂ (fun z => ∫ y, F z t y ∂μ) U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Param.continuousOn_differentiableOn_integral
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CentreChar

theorem continuous_and_norm_chz : ∀ (D : D7) (ρ : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
  Continuous (chz ψ b₀) ∧ ∀ z, ‖chz ψ b₀ z‖ = 1 := fun _ _ _ hψ b₀ =>
  ⟨GlobalTheory.CompanionTheory.PcB.continuous_chz hψ b₀, GlobalTheory.CompanionTheory.PcB.chz_norm hψ b₀⟩

end GlobalTheory.CompanionTheory.CentreChar
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_character_continuous_unit : ∀ (D : D7) (ρ : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
  Continuous (chz ψ b₀) ∧ ∀ z, ‖chz ψ b₀ z‖ = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz
end

section
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn.Model

namespace GlobalTheory.CompanionTheory.PcB

open GlobalTheory.CompanionTheory.FourierN (mat_injective)

theorem blockMatrix_zero' {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  simp only [bl]
  rw [Matrix.fromBlocks_zero]
  rfl

theorem lowerUnipotent_mul_blockDiagonal {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 c 1) (bl hn 1 0 0 d) = bl hn 1 0 c d := by
  rw [blockMatrix_multiply]
  congr 1 <;> simp

theorem blockMatrix_diagonal_mul_lowerUnipotent {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 0 d) (bl hn 1 0 c 1) = bl hn 1 0 (HMul.hMul d c) d := by
  rw [blockMatrix_multiply]
  congr 1 <;> simp

theorem upperUnipotent_mul_blockDiagonal {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (y : Matrix (Fin ρ) (Fin p) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 y 0 1) (bl hn 1 0 0 d) = bl hn 1 (HMul.hMul y d) 0 d := by
  rw [blockMatrix_multiply]
  congr 1 <;> simp

theorem blockMatrix_diagonal_mul_upperUnipotent {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (y : Matrix (Fin ρ) (Fin p) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 0 d) (bl hn 1 y 0 1) = bl hn 1 y 0 d := by
  rw [blockMatrix_multiply]
  congr 1 <;> simp

theorem sh_emb_levi (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₀ : G D p)
    (a : GL (Fin p) (AE D)) (h : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) (y : Mx D ρ p) :
    M.sh y * M.emb g₀ = M.emb g₀ * M.sh (HMul.hMul y a.1 : Mx D ρ p) := by
  have hinv : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (adj a.1 : Mx D p p) = (1 : Mx D p p) := by
    have h1 : HMul.hMul (a.1 : Mx D p p) ((a⁻¹).1 : Mx D p p) = (1 : Mx D p p) := by
      exact congrArg Units.val (mul_inv_cancel a)
    rw [← adj_mul, h1]
    exact adj_one
  apply mat_injective
  rw [mat_mul', mat_mul', M.sh_mat, M.sh_mat, M.emb_mat g₀ _ _ _ _ h, blockMatrix_zero', block_diagonal_mul, block_diagonal_mul]
  congr 1
  · rw [upperUnipotent_mul_blockDiagonal, blockMatrix_diagonal_mul_upperUnipotent]
  · have hk : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (adj (HMul.hMul y a.1 : Mx D ρ p)) = adj y := by
      rw [adj_mul, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hk' : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (-adj (HMul.hMul y a.1 : Mx D ρ p)) = -adj y := by
      rw [Matrix.mul_neg, hk]
    rw [lowerUnipotent_mul_blockDiagonal, blockMatrix_diagonal_mul_lowerUnipotent, hk']

end GlobalTheory.CompanionTheory.PcB
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_commutes_levi_embedding : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ y : Mx D ρ p, M.sh y * M.emb g₀ = M.emb g₀ * M.sh (HMul.hMul y a.1 : Mx D ρ p) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PcB.sh_emb_levi
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_levi_equivariance : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
  (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ x : G D n, Wz M m ψ b₀ f (M.emb g₀ * x) =
    (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) * Wz M m ψ b₀ f x := by
  first | exact @GlobalTheory.CompanionTheory.WzLevi.wz_emb | exact GlobalTheory.CompanionTheory.WzLevi.wz_emb | (intros; apply GlobalTheory.CompanionTheory.WzLevi.wz_emb <;> assumption)
end

section
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.EisCovar PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.ThTw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ShEmbUnip

set_option maxHeartbeats 1000000 in

theorem sh_emb_unip : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₁ : G D p) (b : Mx D p p), mat g₁ = blk4 1 b 0 1 →
    ∀ y : Mx D ρ p, ∃ (z₀ : hermA D ρ) (x₀ : Mx D ρ p), M.sh y * M.emb g₁ = M.nzx z₀ x₀ * M.emb g₁ * M.sh y ∧
      z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) := by
  intro D n ρ p hn M g₁ b hg y
  have hb : adj b = b := (GlobalTheory.StdUnn.Model.exists_unip b).1 ⟨g₁, hg⟩
  have hE := M.emb_mat g₁ _ _ _ _ hg
  refine ⟨⟨HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y), ?_⟩, HMul.hMul y b, ?_, rfl⟩
  · show adj _ = _
    rw [adj_mul, adj_mul, adj_adj, hb, Matrix.mul_assoc]
  · apply mat_injective'
    rw [mat_mul' (M.sh y), mat_mul' _ (M.sh y), mat_mul' (M.nzx _ _), M.sh_mat, M.nzx_mat, hE, blockMatrix_zero, blockRowSubstitution_one,
      submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, block_mul₂, bl_add,
      adj_mul, hb, Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg, add_neg_cancel, neg_add_cancel]

end GlobalTheory.CompanionTheory.ShEmbUnip

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_unipotent_levi_commutator : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₁ : G D p) (b : Mx D p p), mat g₁ = blk4 1 b 0 1 →
  ∀ y : Mx D ρ p, ∃ (z₀ : hermA D ρ) (x₀ : Mx D ρ p), M.sh y * M.emb g₁ = M.nzx z₀ x₀ * M.emb g₁ * M.sh y ∧
    z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ShEmbUnip.sh_emb_unip
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_unipotent_levi_invariance : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₁ : G D p) (b : Mx D p p),
  mat g₁ = blk4 1 b 0 1 → ∀ (z₀ : hermA D ρ) (x₀ : Mx D ρ p) (x : G D n),
    Wz M m ψ b₀ f (M.nzx z₀ x₀ * M.emb g₁ * x) = chz ψ b₀ z₀ * Wz M m ψ b₀ f x := by
  first | exact @GlobalTheory.CompanionTheory.WzHeis.wz_heis | exact GlobalTheory.CompanionTheory.WzHeis.wz_heis | (intros; apply GlobalTheory.CompanionTheory.WzHeis.wz_heis <;> assumption)
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ChzConj

theorem chz_conj : ∀ (D : D7) (ρ p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (b : Mx D p p) (y : Mx D ρ p) (z₀ : hermA D ρ),
  z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) →
    chz ψ b₀ z₀ = ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) := by
  intro D ρ p ψ b₀ b y z₀ hz
  unfold chz pr
  rw [hz]
  congr 2
  change Matrix.trace (Matrix.map b₀.1 (incA D) * ((y * b) * adj y)) = Matrix.trace (b * (adj y * (Matrix.map b₀.1 (incA D) * y)))
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.ChzConj

end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_character_quadratic_trace : ∀ (D : D7) (ρ p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (b : Mx D p p) (y : Mx D ρ p) (z₀ : hermA D ρ),
  z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) →
    chz ψ b₀ z₀ = ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ChzConj.chz_conj
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_unipotent_levi_factor : ∀ (D : D7) (p : ℕ) (q : G D p), q ∈ P D p → ∀ a : GL (Fin p) (AE D), blkA (mat q) = a.1 →
  ∃ (g₁ g₂ : G D p) (b : Mx D p p), q = g₁ * g₂ ∧ mat g₁ = blk4 1 b 0 1 ∧ mat g₂ = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi | exact GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi | (intros; apply GlobalTheory.CompanionTheory.SiegelNM.unip_mul_levi <;> assumption)
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CompanionTheory.RSecPf

variable {D : D7} {n ρ p : ℕ}

theorem rpow_le_add {r τ τ₁ τ₂ : ℝ} (hr : 0 < r) (h₁ : τ₁ ≤ τ) (h₂ : τ ≤ τ₂) : r ^ τ ≤ r ^ τ₁ + r ^ τ₂ := by
  rcases le_total r 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge hr h h₁).trans (le_add_of_nonneg_right (Real.rpow_nonneg hr.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le h h₂).trans (le_add_of_nonneg_left (Real.rpow_nonneg hr.le _))

theorem shear_pt {a b τ τ₁ τ₂ W₁ W₂ c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (h₁ : τ₁ ≤ τ) (h₂ : τ ≤ τ₂)
    (hW₁ : a ^ τ₁ * c ≤ W₁ * b ^ τ₁) (hW₂ : a ^ τ₂ * c ≤ W₂ * b ^ τ₂) :
    a ^ τ * c ≤ (W₁ + W₂) * (b ^ τ₁ + b ^ τ₂) := by
  have hr : 0 < a / b := div_pos ha hb
  have e : ∀ t : ℝ, a ^ t = (a / b) ^ t * b ^ t := fun t => by
    rw [← Real.mul_rpow hr.le hb.le, div_mul_cancel₀ _ hb.ne']
  have key : ∀ {t W : ℝ}, a ^ t * c ≤ W * b ^ t → (a / b) ^ t * c ≤ W := fun {t W} h => by
    have hbt : 0 < b ^ t := Real.rpow_pos_of_pos hb t
    rw [e t] at h
    have : (a / b) ^ t * c * b ^ t ≤ W * b ^ t := by linarith [h]
    exact le_of_mul_le_mul_right this hbt
  have k₁ := key hW₁
  have k₂ := key hW₂
  have n₁ : 0 ≤ W₁ := (mul_nonneg (Real.rpow_nonneg hr.le _) hc).trans k₁
  have n₂ : 0 ≤ W₂ := (mul_nonneg (Real.rpow_nonneg hr.le _) hc).trans k₂
  have h3 : (a / b) ^ τ * c ≤ W₁ + W₂ := by
    have := mul_le_mul_of_nonneg_right (rpow_le_add hr h₁ h₂) hc
    linarith
  have h4 : b ^ τ ≤ b ^ τ₁ + b ^ τ₂ := rpow_le_add hb h₁ h₂
  have hbt : 0 ≤ b ^ τ := Real.rpow_nonneg hb.le _
  calc a ^ τ * c = (a / b) ^ τ * c * b ^ τ := by rw [e τ]; ring
    _ ≤ (W₁ + W₂) * b ^ τ := mul_le_mul_of_nonneg_right h3 hbt
    _ ≤ (W₁ + W₂) * (b ^ τ₁ + b ^ τ₂) := mul_le_mul_of_nonneg_left h4 (add_nonneg n₁ n₂)

theorem local_tau (hn : ρ + p = n) {z₀ : ℂ} (hz : ((ρ : ℝ) - p) / 2 < z₀.re) :
    ∃ V ∈ 𝓝 z₀, ∃ τ₁ τ₂ : ℝ, (ρ : ℝ) < τ₁ ∧ τ₁ ≤ τ₂ ∧
      ∀ z ∈ V, τ₁ ≤ z.re + (n : ℝ) / 2 ∧ z.re + (n : ℝ) / 2 ≤ τ₂ := by
  obtain ⟨ε, hε, hε'⟩ : ∃ ε : ℝ, 0 < ε ∧ ε = (z₀.re - ((ρ : ℝ) - p) / 2) / 2 := ⟨_, by linarith, rfl⟩
  have hnr : (n : ℝ) = ρ + p := by rw [← hn]; push_cast; ring
  refine ⟨Metric.ball z₀ ε, Metric.ball_mem_nhds _ hε, z₀.re - ε + n / 2, z₀.re + ε + n / 2, ?_, ?_, fun z hz' => ?_⟩
  · rw [hnr]; linarith
  · linarith
  · have h : |(z - z₀).re| < ε := (Complex.abs_re_le_norm _).trans_lt (by simpa [dist_eq_norm] using hz')
    rw [Complex.sub_re, abs_lt] at h
    constructor <;> linarith [h.1, h.2]

theorem continuous_fam {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) (s₁ : ℂ) :
    Continuous fun u : ℂ × G D n => fam H φ s₁ u.1 u.2 := by
  unfold fam npow
  refine Continuous.mul (Continuous.cpow ?_ (continuous_fst.sub continuous_const) ?_) (hφ.comp continuous_snd)
  · exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (hH.1.comp continuous_snd))
  · exact fun u => Complex.ofReal_mem_slitPlane.2 (NNReal.coe_pos.2 (hH.2.1 _))

theorem differentiable_fam {H : G D n → ℝ≥0} (hH : IsHt H) (φ : G D n → ℂ) (s₁ : ℂ) (g : G D n) :
    Differentiable ℂ fun z => fam H φ s₁ z g := by
  have h : ((H g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hH.2.1 g).ne'
  unfold fam npow
  exact ((differentiable_id.sub_const s₁).const_cpow (Or.inl h)).mul_const _

theorem fam_le {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} {s₁ : ℂ} {B κ τ₂ : ℝ} (hB : 0 ≤ B) (hκ : 1 ≤ κ)
    (hf : ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2))
    {z : ℂ} (h0 : 0 ≤ z.re + (n : ℝ) / 2) (h2 : z.re + (n : ℝ) / 2 ≤ τ₂) {x c : G D n}
    (hc : (H (x * c) : ℝ) ≤ κ * (H x : ℝ)) :
    ‖fam H φ s₁ z (x * c)‖ ≤ B * κ ^ τ₂ * (H x : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  have hx : (0 : ℝ) < H x := NNReal.coe_pos.2 (hH.2.1 x)
  have hxc : (0 : ℝ) ≤ H (x * c) := NNReal.coe_nonneg _
  have hκ0 : 0 ≤ κ := by linarith
  calc ‖fam H φ s₁ z (x * c)‖ ≤ B * (H (x * c) : ℝ) ^ (z.re + (n : ℝ) / 2) := hf z _
    _ ≤ B * (κ * (H x : ℝ)) ^ (z.re + (n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxc hc h0) hB
    _ = B * κ ^ (z.re + (n : ℝ) / 2) * (H x : ℝ) ^ (z.re + (n : ℝ) / 2) := by
        rw [Real.mul_rpow hκ0 hx.le]; ring
    _ ≤ B * κ ^ τ₂ * (H x : ℝ) ^ (z.re + (n : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hB) (Real.rpow_nonneg hx.le _)
        exact Real.rpow_le_rpow_of_exponent_le hκ h2

section Main

variable {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (b₀ : HermE D ρ)

theorem continuous_jacobi_map_origin : Continuous fun ζ : hermA D ρ => M.nzx ζ 0 :=
  M.nzx_cont.comp (continuous_id.prodMk continuous_const)

theorem wz_family (hψ : IsCharAF D.host.F ψ) {H : G D n → ℝ≥0} (hH : IsHt H)
    (hcpt : ∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c)
    {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (hφ : Continuous φ) (hlaw : IsLaw χ s₁ φ) :
    ContinuousOn (fun u : ℂ × G D n => Wz M m ψ b₀ (fam H φ s₁ u.1) u.2)
        ({z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} ×ˢ Set.univ) ∧
      ∀ c, DifferentiableOn ℂ (fun z => Wz M m ψ b₀ (fam H φ s₁ z) c) {z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} := by
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  obtain ⟨B, hB, hf⟩ := GlobalTheory.T.eisenstein_family_height_bound D n H hH hcpt χ s₁ φ hφ hlaw
  obtain ⟨hcz, hnz⟩ := GlobalTheory.T.centre_character_continuous_unit D ρ ψ hψ b₀
  have hU : IsOpen {z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine GlobalTheory.T.continuousOn_differentiableOn_parameter_integral (Y := hermA D ρ) (T := G D n) m.lz _ hU
    (fun z c ζ => fam H φ s₁ z (M.w * M.nzx ζ 0 * c) * conj (chz ψ b₀ ζ)) ?_ ?_ ?_
  · refine Continuous.continuousOn (Continuous.mul ?_ ?_)
    · refine (continuous_fam hH hφ s₁).comp (continuous_fst.prodMk ?_)
      exact (continuous_const.mul ((continuous_jacobi_map_origin M).comp (continuous_snd.comp continuous_snd))).mul
        (continuous_fst.comp continuous_snd)
    · exact Complex.continuous_conj.comp (hcz.comp (continuous_snd.comp continuous_snd))
  · exact fun c ζ => ((differentiable_fam hH φ s₁ _).mul_const _).differentiableOn
  · intro z₀ hz₀ c₀
    obtain ⟨V, hV, τ₁, τ₂, h1, h12, hτ⟩ := local_tau hn hz₀
    obtain ⟨N, hN, hNm⟩ := exists_compact_mem_nhds c₀
    obtain ⟨κ, hκ, hκc⟩ := GlobalTheory.T.height_right_translate_compact_bound D n H hH hcpt N hN
    have hρ : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
    have I₁ := GlobalTheory.T.height_power_integrable_weyl_orbit D n ρ p hn M m H hH hcpt τ₁ h1
    have I₂ := GlobalTheory.T.height_power_integrable_weyl_orbit D n ρ p hn M m H hH hcpt τ₂ (h1.trans_le h12)
    refine ⟨V, hV, N, hNm, fun ζ => B * κ ^ τ₂ * ((H (M.w * M.nzx ζ 0) : ℝ) ^ τ₁ + (H (M.w * M.nzx ζ 0) : ℝ) ^ τ₂),
      (I₁.add I₂).const_mul _, fun z hz c hc ζ => ?_⟩
    have hx : (0 : ℝ) < H (M.w * M.nzx ζ 0) := NNReal.coe_pos.2 (hH.2.1 _)
    have h0 : 0 ≤ z.re + (n : ℝ) / 2 := by linarith [(hτ z hz).1]
    rw [norm_mul, RCLike.norm_conj, hnz, mul_one]
    refine (fam_le hH hB hκ hf h0 (hτ z hz).2 (hκc c hc _)).trans ?_
    refine mul_le_mul_of_nonneg_left (rpow_le_add hx (hτ z hz).1 (hτ z hz).2) ?_
    exact mul_nonneg hB (Real.rpow_nonneg (by linarith) _)

end Main

theorem isLaw_fam {H : G D n → ℝ≥0} (hH : IsHt H) {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (hl : IsLaw χ s₁ φ) (z : ℂ) :
    IsLaw χ z (fam H φ s₁ z) := by
  intro q hq a ha g
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) * absA D (Matrix.GeneralLinearGroup.det a)⁻¹ = 1 := by
    rw [← map_mul]; simp
  have hne : (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ≠ 0 := by
    exact_mod_cast left_ne_zero_of_mul_eq_one h1
  have hc : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  simp only [fam]
  rw [hH.2.2 q hq a ha g, hl q hq a ha g]
  unfold npow
  push_cast
  rw [Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  have e : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ (z + (n : ℂ) / 2) =
      ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ (z - s₁) *
        ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ (s₁ + (n : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hc]; congr 1; ring
  rw [e]; ring

section Main2

variable {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (b₀ : HermE D ρ)

theorem rsec_family (hψ : IsCharAF D.host.F ψ) {χ χ' : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ)
    {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) {H : G D n → ℝ≥0} (hH : IsHt H)
    (hcpt : ∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c)
    {s₁ : ℂ} {φ : G D n → ℂ} (hφ : Continuous φ) (hlaw : IsLaw χ s₁ φ) (g : G D n) :
    ContinuousOn (fun u : ℂ × G D p => Rsec M m ψ b₀ (fam H φ s₁ u.1) g Ω u.2)
        ({z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} ×ˢ Set.univ) ∧
      ∀ h, DifferentiableOn ℂ (fun z => Rsec M m ψ b₀ (fam H φ s₁ z) g Ω h) {z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} := by
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  obtain ⟨hc1, hd1⟩ := wz_family M m b₀ hψ hH hcpt hφ hlaw
  obtain ⟨B, hB, hf⟩ := GlobalTheory.T.eisenstein_family_height_bound D n H hH hcpt χ s₁ φ hφ hlaw
  obtain ⟨hcz, hnz⟩ := GlobalTheory.T.centre_character_continuous_unit D ρ ψ hψ b₀
  have hU : IsOpen {z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine GlobalTheory.T.continuousOn_differentiableOn_parameter_integral (Y := Mx D ρ p) (T := G D p) m.μ _ hU
    (fun z h y => Wz M m ψ b₀ (fam H φ s₁ z) (M.sh y * M.emb h * g) * conj (Ω h y)) ?_ ?_ ?_
  · refine ContinuousOn.mul ?_ (Continuous.continuousOn ?_)
    · refine hc1.comp (f := fun u : ℂ × G D p × Mx D ρ p => (u.1, M.sh u.2.2 * M.emb u.2.1 * g))
        (Continuous.continuousOn (continuous_fst.prodMk ?_)) fun u hu => ⟨hu.1, trivial⟩
      exact ((M.sh_cont.comp (continuous_snd.comp continuous_snd)).mul
        (M.emb_cont.comp (continuous_fst.comp continuous_snd))).mul continuous_const
    · exact Complex.continuous_conj.comp (hΩ.cont.comp continuous_snd)
  · exact fun h y => (hd1 _).mul_const _
  · intro z₀ hz₀ h₀
    obtain ⟨V, hV, τ₁, τ₂, h1, h12, hτ⟩ := local_tau hn hz₀
    obtain ⟨N, hN, hNm⟩ := exists_compact_mem_nhds h₀
    have hCc : IsCompact ((fun h => M.emb h * g) '' N) := hN.image (M.emb_cont.mul continuous_const)
    obtain ⟨κ, hκ, hκc⟩ := GlobalTheory.T.height_right_translate_compact_bound D n H hH hcpt _ hCc
    obtain ⟨Φ, hΦ, hmaj⟩ := hΩ.maj N hN
    have hρ : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
    obtain ⟨W₁, iW₁, hW₁⟩ := GlobalTheory.T.schwartz_height_majorant_integrable D n ρ p hn M m θ hθ H hH hcpt Φ hΦ τ₁ (by linarith)
    obtain ⟨W₂, iW₂, hW₂⟩ := GlobalTheory.T.schwartz_height_majorant_integrable D n ρ p hn M m θ hθ H hH hcpt Φ hΦ τ₂ (by linarith)
    have I₁ := GlobalTheory.T.height_power_integrable_weyl_orbit D n ρ p hn M m H hH hcpt τ₁ h1
    have I₂ := GlobalTheory.T.height_power_integrable_weyl_orbit D n ρ p hn M m H hH hcpt τ₂ (h1.trans_le h12)
    have IA := I₁.add I₂
    refine ⟨V, hV, N, hNm, fun y => B * κ ^ τ₂ * (W₁ y + W₂ y) *
      ∫ ζ : hermA D ρ, ((H (M.w * M.nzx ζ 0) : ℝ) ^ τ₁ + (H (M.w * M.nzx ζ 0) : ℝ) ^ τ₂) ∂m.lz,
      ((iW₁.add iW₂).const_mul _).mul_const _, fun z hz h hh y => ?_⟩
    have h0 : 0 ≤ z.re + (n : ℝ) / 2 := by linarith [(hτ z hz).1]
    rw [norm_mul, RCLike.norm_conj]
    have hκ0 : 0 ≤ B * κ ^ τ₂ := mul_nonneg hB (Real.rpow_nonneg (by linarith) _)
    have key : ‖Wz M m ψ b₀ (fam H φ s₁ z) (M.sh y * M.emb h * g)‖ * ‖Φ y‖ ≤ B * κ ^ τ₂ * (W₁ y + W₂ y) *
        ∫ ζ : hermA D ρ, ((H (M.w * M.nzx ζ 0) : ℝ) ^ τ₁ + (H (M.w * M.nzx ζ 0) : ℝ) ^ τ₂) ∂m.lz := by
      have e : ‖Wz M m ψ b₀ (fam H φ s₁ z) (M.sh y * M.emb h * g)‖ * ‖Φ y‖ =
          ‖∫ ζ : hermA D ρ, (fam H φ s₁ z (M.w * M.nzx ζ 0 * (M.sh y * M.emb h * g)) * conj (chz ψ b₀ ζ)) *
            ((‖Φ y‖ : ℝ) : ℂ) ∂m.lz‖ := by
        rw [integral_mul_const, norm_mul, Complex.norm_real, norm_norm]; rfl
      rw [e, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (IA.const_mul _) (.of_forall fun ζ => ?_)
      rw [norm_mul, norm_mul, RCLike.norm_conj, hnz, mul_one, Complex.norm_real, norm_norm]
      have e2 : M.w * M.nzx ζ 0 * (M.sh y * M.emb h * g) = (M.w * M.nzx ζ 0 * M.sh y) * (M.emb h * g) := by
        simp only [mul_assoc]
      rw [e2]
      have hb := fam_le hH hB hκ hf h0 (hτ z hz).2 (hκc _ ⟨h, hh, rfl⟩ (M.w * M.nzx ζ 0 * M.sh y))
      have hp := shear_pt (NNReal.coe_pos.2 (hH.2.1 (M.w * M.nzx ζ 0 * M.sh y))) (NNReal.coe_pos.2 (hH.2.1 (M.w * M.nzx ζ 0)))
        (norm_nonneg (Φ y)) (hτ z hz).1 (hτ z hz).2 (hW₁ _ y) (hW₂ _ y)
      calc _ ≤ (B * κ ^ τ₂ * (H (M.w * M.nzx ζ 0 * M.sh y) : ℝ) ^ (z.re + (n : ℝ) / 2)) * ‖Φ y‖ :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = B * κ ^ τ₂ * ((H (M.w * M.nzx ζ 0 * M.sh y) : ℝ) ^ (z.re + (n : ℝ) / 2) * ‖Φ y‖) := by ring
        _ ≤ B * κ ^ τ₂ * ((W₁ y + W₂ y) * ((H (M.w * M.nzx ζ 0) : ℝ) ^ τ₁ + (H (M.w * M.nzx ζ 0) : ℝ) ^ τ₂)) :=
            mul_le_mul_of_nonneg_left hp hκ0
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_left (hmaj h hh y) (norm_nonneg _)).trans key

end Main2

section Law

variable {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (b₀ : HermE D ρ)

theorem npow_add' {r : ℝ≥0} (hr : (r : ℝ) ≠ 0) (s t : ℂ) : npow r (s + t) = npow r s * npow r t := by
  unfold npow
  exact Complex.cpow_add _ _ (by exact_mod_cast hr)

theorem conj_npow_ofReal (r : ℝ≥0) (t : ℝ) : conj (npow r (t : ℂ)) = npow r (t : ℂ) := by
  unfold npow
  rw [← Complex.ofReal_cpow (NNReal.coe_nonneg r), Complex.conj_ofReal]

theorem rsec_levi {χ χ' : (AE D)ˣ →* Circle} {θ : InfFam D} {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ' θ b₀ m.μ Ω)
    {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f) (g : G D n) (g₀ : G D p) (a : GL (Fin p) (AE D))
    (ha : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) (h : G D p) :
    Rsec M m ψ b₀ f g Ω (g₀ * h) = ((χ * χ'⁻¹) (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (p : ℂ) / 2) * Rsec M m ψ b₀ f g Ω h := by
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) * absA D (Matrix.GeneralLinearGroup.det a)⁻¹ = 1 := by
    rw [← map_mul]; simp
  have hne : (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ≠ 0 := by
    exact_mod_cast left_ne_zero_of_mul_eq_one h1
  have e : ∀ y : Mx D ρ p, Wz M m ψ b₀ f (M.sh y * M.emb (g₀ * h) * g) * conj (Ω (g₀ * h) y) =
      ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) *
        conj ((χ' (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) ((ρ : ℂ) / 2))) *
      (fun y' : Mx D ρ p => Wz M m ψ b₀ f (M.sh y' * M.emb h * g) * conj (Ω h y')) (HMul.hMul y a.1 : Mx D ρ p) := by
    intro y
    have e1 : M.sh y * M.emb (g₀ * h) * g = M.emb g₀ * (M.sh (HMul.hMul y a.1 : Mx D ρ p) * M.emb h * g) := by
      rw [map_mul, ← mul_assoc, GlobalTheory.T.shift_commutes_levi_embedding D n ρ p hn M g₀ a ha y]
      simp only [mul_assoc]
    rw [e1, GlobalTheory.T.coefficient_levi_equivariance D n ρ p hn M m ψ b₀ χ z f hf g₀ a ha, hΩ.levi g₀ a ha h y]
    simp only [map_mul]
    ring
  unfold Rsec
  simp_rw [e]
  rw [integral_const_mul, GlobalTheory.RightMulJac.integral_mul_right D ρ p m.μ m.𝓕 m.hμ a
    (fun y' : Mx D ρ p => Wz M m ψ b₀ f (M.sh y' * M.emb h * g) * conj (Ω h y'))]
  have hnr : (n : ℂ) = ρ + p := by rw [← hn]; push_cast; ring
  have hs : npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (p : ℂ) / 2) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (((ρ / 2 : ℝ) : ℂ)) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(ρ : ℂ)) := by
    rw [← npow_add' hne, ← npow_add' hne]
    congr 1
    rw [hnr]; push_cast; ring
  have hc : conj (npow (absA D (Matrix.GeneralLinearGroup.det a)) ((ρ : ℂ) / 2)) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (((ρ / 2 : ℝ) : ℂ)) := by
    have := conj_npow_ofReal (absA D (Matrix.GeneralLinearGroup.det a)) (ρ / 2 : ℝ)
    push_cast at this ⊢
    exact this
  rw [hs, map_mul, hc, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul,
    Circle.coe_inv_eq_conj]
  ring

theorem rsec_unip (hψ : IsCharAF D.host.F ψ) {χ χ' : (AE D)ˣ →* Circle} {θ : InfFam D} {Ω : G D p → Mx D ρ p → ℂ}
    (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f) (g : G D n) (g₁ : G D p) (b : Mx D p p)
    (hb : mat g₁ = blk4 1 b 0 1) (h : G D p) : Rsec M m ψ b₀ f g Ω (g₁ * h) = Rsec M m ψ b₀ f g Ω h := by
  unfold Rsec
  refine integral_congr_ae (.of_forall fun y => ?_)
  obtain ⟨z₀, x₀, e1, e2⟩ := GlobalTheory.T.shift_unipotent_levi_commutator D n ρ p hn M g₁ b hb y
  have e3 : M.sh y * M.emb (g₁ * h) * g = M.nzx z₀ x₀ * M.emb g₁ * (M.sh y * M.emb h * g) := by
    rw [map_mul, ← mul_assoc, e1]
    simp only [mul_assoc]
  show Wz M m ψ b₀ f (M.sh y * M.emb (g₁ * h) * g) * conj (Ω (g₁ * h) y) =
    Wz M m ψ b₀ f (M.sh y * M.emb h * g) * conj (Ω h y)
  rw [e3, GlobalTheory.T.coefficient_unipotent_levi_invariance D n ρ p hn M m ψ hψ b₀ χ z f hf g₁ b hb, hΩ.unip g₁ b hb h y, GlobalTheory.T.centre_character_quadratic_trace D ρ p ψ b₀ b y z₀ e2, map_mul]
  have hu : ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) *
      conj (ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p)))) = 1 := by
    rw [Complex.mul_conj', hψ.2.1]; simp
  linear_combination (Wz M m ψ b₀ f (M.sh y * M.emb h * g) * conj (Ω h y)) * hu

theorem rsec_law (hψ : IsCharAF D.host.F ψ) {χ χ' : (AE D)ˣ →* Circle} {θ : InfFam D} {Ω : G D p → Mx D ρ p → ℂ}
    (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f) (g : G D n) :
    IsLaw (χ * χ'⁻¹) z (Rsec M m ψ b₀ f g Ω) := by
  intro q hq a ha h
  obtain ⟨g₁, g₂, b, rfl, h1, h2⟩ := GlobalTheory.T.parabolic_unipotent_levi_factor D p q hq a ha
  rw [mul_assoc, rsec_unip M m b₀ hψ hΩ hf g g₁ b h1, rsec_levi M m b₀ hΩ hf g g₂ a h2]

end Law

theorem rSec_of_htExist : HtExist → RSec := by
  intro hHt D n ρ p hn M m ψ hψ b₀ _ χ χ' _ _ θ hθ Ω hΩ H hH s₁ φ hφ hlaw g
  obtain ⟨h1, h2⟩ := rsec_family M m b₀ hψ hθ hΩ hH (hHt D n).2 hφ hlaw g
  exact ⟨h1, h2, fun z _ => rsec_law M m b₀ hψ hΩ (isLaw_fam hH hlaw z) g⟩

end GlobalTheory.CompanionTheory.RSecPf

end
end

open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_of_heights : HtExist → RSec := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist
end
