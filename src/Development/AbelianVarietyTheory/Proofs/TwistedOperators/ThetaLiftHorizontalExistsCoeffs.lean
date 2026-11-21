import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory

namespace GlobalTheory.KernelApprox

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem thetaKO_sub (g : GA D S) (h : GA D T) (f f' : WO S T → ℂ) :
    thetaKO om g h f - thetaKO om g h f' = thetaKO om g h (f - f') := by
  simp only [thetaKO, map_sub, Pi.sub_apply]

theorem exists_kernel_approx (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om) (P : (WO S T → ℂ) → Prop)
    {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ)
    (hden : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → Φ ∈ GlobalTheory.Size.thetaLevel ψ S T U →
      ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε →
        ∃ X, P X ∧ X ∈ GlobalTheory.Size.thetaLevel ψ S T U ∧ GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ) < ENNReal.ofReal ε) :
    ∃ a : ℕ, ∀ ε : ℝ, 0 < ε → ∃ X, P X ∧ ∀ g h,
      ‖thetaKO om g h X - thetaKO om g h Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a := by
  obtain ⟨a, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D S.rank T.rank
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne S T
  obtain ⟨C, hC0, hC⟩ := (H _ _ rfl rfl).real ψ hθ hU
  refine ⟨a, fun ε hε => ?_⟩
  have hK : 0 < (C + 1) * 4 ^ a := by positivity
  obtain ⟨X, hPX, hXU, hsob⟩ := hden U hU hΦU μ 𝓕 hμ d (ε / ((C + 1) * 4 ^ a)) (div_pos hε hK)
  refine ⟨X, hPX, fun g h => ?_⟩
  have hΨ : X - Φ ∈ GlobalTheory.Size.thetaLevel ψ S T U := Submodule.sub_mem _ hXU hΦU
  rw [thetaKO_sub]
  obtain ⟨-, hb⟩ := hC _ _ _ hω μ 𝓕 hμ (X - Φ) hΨ
  have hsr : (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal ≤ ε / ((C + 1) * 4 ^ a) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsob.le
    rwa [ENNReal.toReal_ofReal (div_pos hε hK).le] at this
  obtain ⟨γ, hγ, h1⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight T h
  rw [← GlobalTheory.ChainOnto.ThetaSwap.thetaKO_left_fst hω hΨ.1 γ hγ g h,
    ← GlobalTheory.Chain.LiftConv.thetaKO_left hω hΨ.1 (γ * g) γ' hγ' h]
  have hq1 := GlobalTheory.Grow.quotHeight_pos S g
  have hq2 := GlobalTheory.Grow.quotHeight_pos T h
  have hh1 := GlobalTheory.Grow.height_pos S (γ * g)
  have hh2 := GlobalTheory.Grow.height_pos T (γ' * h)
  have hs0 : 0 ≤ (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal := ENNReal.toReal_nonneg
  have hpow : (GlobalTheory.Grow.height S (γ * g) * GlobalTheory.Grow.height T (γ' * h)) ^ a ≤
      4 ^ a * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a) := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) a
  have hne : (C + 1) * 4 ^ a ≠ 0 := hK.ne'
  calc ‖thetaKO om (γ * g) (γ' * h) (X - Φ)‖
      ≤ C * (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal *
          (GlobalTheory.Grow.height S (γ * g) * GlobalTheory.Grow.height T (γ' * h)) ^ a := hb _ _
    _ ≤ (C + 1) * (ε / ((C + 1) * 4 ^ a)) * (4 ^ a * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a)) :=
        mul_le_mul (mul_le_mul (by linarith) hsr hs0 (by linarith)) hpow (pow_nonneg (mul_pos hh1 hh2).le a)
          (mul_nonneg (by linarith) (div_pos hε hK).le)
    _ = ((C + 1) * 4 ^ a) * (ε / ((C + 1) * 4 ^ a)) * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a) := by
        ring
    _ = ε * GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a := by
        rw [mul_div_cancel₀ _ hne]; ring

end GlobalTheory.KernelApprox

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ArrowFockDense

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity

theorem dense_level : ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ (t : T) i j, i ≤ D.R.m → j < D.R.m → ∀ (U : AddSubgroup (WO (G.V i j).V (G.V i (j + 1)).V)), IsOpen (U : Set (WO (G.V i j).V (G.V i (j + 1)).V)) → ∀ Φ ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ (μ : Measure (WO (G.V i j).V (G.V i (j + 1)).V)) (𝓕 : Set (WO (G.V i j).V (G.V i (j + 1)).V)), IsCovolOne (ratL (G.V i (j + 1)).V (G.V i j).V) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U ∧ GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d ((∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - Φ) < ENNReal.ofReal ε := by
  intro D G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj U hU Φ hΦ μ 𝓕 hm d ε hε
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  have hψ : IsStdChar D R.ψ (-1) := hω.std
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D (G.V i (j + 1)).V (G.V i j).V
  haveI : BorelSpace (WO (G.V i j).V (G.V i (j + 1)).V) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL R.ψ _ _ (toB hψ Φ hΦ.1) = Φ := coe_toB hψ Φ hΦ.1
  have hF : toB hψ Φ hΦ.1 ∈ (thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U).comap (coeL R.ψ _ _) := by
    rw [Submodule.mem_comap, e0]
    exact hΦ
  obtain ⟨g, h1, h2, h3⟩ := dense_vec h hψ (Fr.ofModel (G.V i j).M) (Fr.ofModel (G.V i (j + 1)).M) hU
    (toL2 _ _ (μ.restrict 𝓕))
    (fun v F => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ μ 𝓕 hm.1 hm.2.1 _ F)
    (fun a : D.what₂.Tau × Fin (G.V i (j + 1)).V.rank × Fin (G.V i j).V.rank × Bool =>
      atPl a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) d hF
    (ENNReal.ofReal_pos.2 hε)
  have e1 : ∀ F : BB R.ψ (G.V i j).V (G.V i (j + 1)).V,
      l2O μ 𝓕 (coeL R.ψ _ _ F) = ‖toL2 _ _ (μ.restrict 𝓕) F‖ₑ := fun F =>
    (eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (μ.restrict 𝓕) ℂ F.1)).symm.trans (Lp.enorm_def _).symm
  have e2 : Φ - coeL R.ψ _ _ g = coeL R.ψ _ _ (toB hψ Φ hΦ.1 - g) := by rw [LinearMap.map_sub, e0]
  have hS : sobO R.ψ R.θ μ 𝓕 d (Φ - coeL R.ψ _ _ g) < ENNReal.ofReal ε := by
    refine lt_of_eq_of_lt ?_ h3
    simp only [sobO, wordSum, e2, coe_word h hψ hU _ (sub_mem hF h2), e1]

  obtain ⟨n, c, gs, hgs⟩ := Submodule.mem_span_set'.1 (Submodule.mem_comap.1 h1)
  choose f₀ P hv hl hP using fun l => (gs l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => hv l, ?_, ?_⟩
  · have e3 : (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f₀ l) (c l • P l)) = coeL R.ψ _ _ g := by
      rw [← hgs]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hP l, map_smul]
      rfl
    rw [e3]
    exact h2
  · have e3 : (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f₀ l) (c l • P l)) - Φ =
        (-1 : ℂ) • (Φ - coeL R.ψ _ _ g) := by
      rw [← hgs, neg_one_smul, neg_sub]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hP l, map_smul]
      rfl
    rw [e3, sobO_smul, enorm_neg, enorm_one, one_mul]
    exact hS

end GlobalTheory.ArrowFockDense
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridDownArrow_thetaFunction_fock_dense_of_level : ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ (t : T) i j, i ≤ D.R.m → j < D.R.m → ∀ (U : AddSubgroup (WO (G.V i j).V (G.V i (j + 1)).V)), IsOpen (U : Set (WO (G.V i j).V (G.V i (j + 1)).V)) → ∀ Φ ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ (μ : Measure (WO (G.V i j).V (G.V i (j + 1)).V)) (𝓕 : Set (WO (G.V i j).V (G.V i (j + 1)).V)), IsCovolOne (ratL (G.V i (j + 1)).V (G.V i j).V) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U ∧ GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d ((∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - Φ) < ENNReal.ofReal ε := by
  atlas_forward_decl GlobalTheory.ArrowFockDense.dense_level
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaArrowApprox

theorem thetaKO_approx_fock : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - thetaKO (G.th t i j).ω h g Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  intro _ _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨a, ha⟩ := GlobalTheory.KernelApprox.exists_kernel_approx hRB.inf hω
    (fun X => ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank),
      (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧
        X = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) hΦ
    (fun U hU hΦU μ 𝓕 hμ d ε hε => by
      obtain ⟨n, fs, ps, h1, h2, h3⟩ := GlobalTheory.T.gridDownArrow_thetaFunction_fock_dense_of_level D G₀ Pl0 T A Ks R G hRB hG t i j hi hj U hU Φ hΦU μ 𝓕 hμ d ε hε
      exact ⟨_, ⟨n, fs, ps, h1, rfl⟩, h2, h3⟩)
  refine ⟨a, a, fun ε hε => ?_⟩
  obtain ⟨X, ⟨n, fs, ps, hfs, rfl⟩, hX⟩ := ha ε hε
  exact ⟨n, fs, ps, hfs, fun h g => hX h g⟩

end GlobalTheory.ThetaArrowApprox

end
end
