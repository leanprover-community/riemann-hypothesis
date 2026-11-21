import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumThetaTransformEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeMemFockAlgebraicThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerThetaDatumHeisenbergOriented
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} [AddCommGroup Z]
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z) (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ),
    IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + Φ') (f + f') := by
  first | exact @GlobalTheory.SquareAgree.isDatum_add | exact GlobalTheory.SquareAgree.isDatum_add | (intros; apply GlobalTheory.SquareAgree.isDatum_add <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∀ f : WO S X → ℂ, IsDatum M ψ cS ΦD f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        ∃ ΦD' ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD' (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  first | exact @GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD | exact GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD | (intros; apply GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_derivative_mem_fockAlgebraicThetaVectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X), ∀ f ∈ algF ψ θ ε A B, ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      dRho (heisO ψ (sgn ε S) X) θ τ z f ∈ algF ψ θ ε A B := by
  first | exact @GlobalTheory.SquareComm.dRho_mem_algF | exact GlobalTheory.SquareComm.dRho_mem_algF | (intros; apply GlobalTheory.SquareComm.dRho_mem_algF <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerThetaDatum_heisenberg_oriented : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ), IsDatum M ψ cS Φ f →
        ∀ w : Matrix (Fin S.rank) (Fin d) (AE D), IsDatum M ψ cS (M.co.rho ψ w Φ) (heisO ψ (sgn ε S) X (cS w) f) := by
  first | exact @GlobalTheory.SquareAgree.HeisCov.isDatum_rho | exact GlobalTheory.SquareAgree.HeisCov.isDatum_rho | (intros; apply GlobalTheory.SquareAgree.HeisCov.isDatum_rho <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ThetaLinePure

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

variable {F : Type} [Field F] [NumberField F]

section Helpers
open scoped Classical

theorem norm_le_mul {V : Type} [NormedAddCommGroup V] (z a : V) : ‖z‖ ≤ (1 + ‖a‖) * (1 + ‖z + a‖) := by
  have h1 : ‖z‖ ≤ ‖z + a‖ + ‖a‖ := by
    calc ‖z‖ = ‖(z + a) - a‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖z + a‖ + ‖a‖ := norm_sub_le _ _
  nlinarith [norm_nonneg a, norm_nonneg (z + a), mul_nonneg (norm_nonneg a) (norm_nonneg (z + a))]

theorem exists_summable_decay {κ : Type} [Fintype κ] {R : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hR : R ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : ∃ m : ℕ, ∀ a : κ → mixedEmbedding.mixedSpace F,
      Summable fun ξ : κ → F =>
        ‖R (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ / (1 + ‖(fun i => mixedEmbedding F (ξ i)) + a‖) ^ m := by
  obtain ⟨B, hB⟩ := hR.1.continuous.bounded_above_of_compact_support hR.2
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hR.2.isCompact
  haveI := discreteTopology_denomLattice F κ hN
  set L := denomLattice F κ N
  refine ⟨Module.finrank ℤ L + 1, fun a => ?_⟩
  set m := Module.finrank ℤ L + 1
  have hw := ZLattice.summable_norm_pow_inv L m (Nat.lt_succ_self _)
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ L}
  have hsupp : ∀ ξ : κ → F, ξ ∉ Set.range (Subtype.val : S → κ → F) →
      ‖R (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ / (1 + ‖(fun i => mixedEmbedding F (ξ i)) + a‖) ^ m = 0 := by
    intro ξ hξ
    by_contra h0
    apply hξ
    have h0' : R (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ≠ 0 := by
      intro h; apply h0; rw [h, norm_zero, zero_div]
    refine ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0') i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff hsupp).1 ?_
  let j : S → L := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun x y h => Subtype.ext (funext fun i =>
    mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hs : Summable fun ξ : S => max B 0 * (1 + ‖a‖) ^ m * ‖j ξ‖⁻¹ ^ m :=
    (hw.comp_injective hj).mul_left _
  refine Summable.of_norm_bounded_eventually hs ?_
  have h0S : (fun i => mixedEmbedding F ((0 : κ → F) i)) ∈ L := by
    simp only [Pi.zero_apply, map_zero]; exact L.zero_mem
  filter_upwards [Filter.eventually_cofinite_ne (⟨0, h0S⟩ : S)] with ξ hne
  have hz : j ξ ≠ 0 := fun h => hne (hj (h.trans (Subtype.ext (funext fun i => (map_zero (mixedEmbedding F)).symm))))
  have hzn : ‖j ξ‖ = ‖((j ξ : L) : κ → mixedEmbedding.mixedSpace F)‖ := by simp
  have key : ∀ z : κ → mixedEmbedding.mixedSpace F, 0 < ‖z‖ → ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      ‖‖R y‖ / (1 + ‖z + a‖) ^ m‖ ≤ max B 0 * (1 + ‖a‖) ^ m * ‖z‖⁻¹ ^ m := by
    intro z hz0 y
    have hY : 0 < ‖z‖ ^ m := pow_pos hz0 m
    have hX : 0 < (1 + ‖z + a‖) ^ m := pow_pos (by linarith [norm_nonneg (z + a)]) m
    have hYX : ‖z‖ ^ m ≤ (1 + ‖a‖) ^ m * (1 + ‖z + a‖) ^ m := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_mul z a) m
    have hinv : ((1 + ‖z + a‖) ^ m)⁻¹ ≤ (1 + ‖a‖) ^ m * (‖z‖ ^ m)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hY, ← div_eq_inv_mul, div_le_iff₀ hX]; exact hYX
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hX.le), inv_pow, div_eq_mul_inv, mul_assoc]
    exact mul_le_mul (le_max_of_le_left (hB _)) hinv (inv_nonneg.2 hX.le) (le_max_right _ _)
  have h := key _ (hzn ▸ norm_pos_iff.2 hz) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i))
  rw [← hzn] at h
  exact h

theorem bound_aux {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : V → ℂ) (C : ℝ) (m : ℕ)
    (hC : ∀ p, (1 + ‖p‖) ^ m * ‖h p‖ ≤ C) (p X : V) (t : ℝ) (ht : |t| ≤ 1) (b : ℝ) (hb : 0 ≤ b) :
    ‖h (p + t • X)‖ * b ≤ C * (1 + ‖X‖) ^ m * (b / (1 + ‖p‖) ^ m) := by
  set q := p + t • X
  have htX : ‖t • X‖ ≤ ‖X‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) ht
  have hpq : ‖p‖ ≤ ‖q‖ + ‖X‖ := by
    calc ‖p‖ = ‖q - t • X‖ := by simp [q]
      _ ≤ ‖q‖ + ‖t • X‖ := norm_sub_le _ _
      _ ≤ ‖q‖ + ‖X‖ := by linarith
  have hq : 1 + ‖p‖ ≤ (1 + ‖X‖) * (1 + ‖q‖) := by
    nlinarith [norm_nonneg X, norm_nonneg q, mul_nonneg (norm_nonneg X) (norm_nonneg q)]
  have hP : 0 < (1 + ‖p‖) ^ m := pow_pos (by linarith [norm_nonneg p]) m
  have H : ‖h q‖ * (1 + ‖p‖) ^ m ≤ C * (1 + ‖X‖) ^ m := by
    calc ‖h q‖ * (1 + ‖p‖) ^ m ≤ ‖h q‖ * ((1 + ‖X‖) ^ m * (1 + ‖q‖) ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith [norm_nonneg p]) hq m
      _ = (1 + ‖X‖) ^ m * ((1 + ‖q‖) ^ m * ‖h q‖) := by ring
      _ ≤ (1 + ‖X‖) ^ m * C :=
          mul_le_mul_of_nonneg_left (hC q) (pow_nonneg (by linarith [norm_nonneg X]) m)
      _ = C * (1 + ‖X‖) ^ m := by ring
  rw [← mul_div_assoc, le_div_iff₀ hP]
  calc ‖h q‖ * b * (1 + ‖p‖) ^ m = (‖h q‖ * (1 + ‖p‖) ^ m) * b := by ring
    _ ≤ (C * (1 + ‖X‖) ^ m) * b := mul_le_mul_of_nonneg_right H hb

end Helpers

theorem realAd_add (t s : ℝ) : realAd F (t + s) = realAd F t + realAd F s := by
  unfold realAd; rw [map_add, map_add, map_add]; rfl

theorem realAd_zero : realAd F 0 = 0 := by
  unfold realAd; rw [map_zero, map_zero, map_zero]; rfl

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t := by
  simp [evI, realAd]

theorem at_realAd_smul {V : Type} [AddCommGroup V] [Module (AF F) V] (t : ℝ) (x : V) :
    At (evI F) (realAd F t • x) := by
  intro b hb
  have hb1 : b.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hb
  have : b * realAd F t = 0 := by
    change ((b.1 * _, b.2 * (0 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) =
      ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
    rw [hb1, zero_mul, mul_zero]
  rw [smul_smul, this, zero_smul]

theorem evFin_eq_zero {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (v : HeightOneSpectrum (𝓞 F)) (i : κ) :
    evFin F v (z i) = 0 := by
  have hb : evI F (pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h := congrArg (evFin F v) (congrFun (hz _ hb) i)
  change evFin F v (pairA F 0 1 * z i) = evFin F v 0 at h
  rw [map_mul, map_zero] at h
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 1 = 1
    exact map_one _
  rwa [h1, one_mul] at h

section Line

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)

theorem rho_apply (w : Matrix (Fin n) (Fin d) (AE F E)) (Ψ : (Fin n × Fin d → AF F) → ℂ) (z : Fin n × Fin d → AF F) :
    M.co.rho ψ w Ψ z =
      ψ (z ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) * Ψ (z + (M.co.e w).1) := rfl

theorem heisLine_add (u : Matrix (Fin n) (Fin d) (AE F E)) (t s : ℝ) (Ψ : (Fin n × Fin d → AF F) → ℂ) :
    M.heisLine ψ u (t + s) Ψ = M.heisLine ψ u t (M.heisLine ψ u s Ψ) := by
  funext z
  simp only [Model.heisLine, rho_apply, realAd_add, add_smul, map_add, map_smul, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc z]
  congr 2
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  linear_combination (realAd F t * realAd F s * ((M.co.e u).1 ⬝ᵥ (M.co.e u).2)) * invOf_mul_self (2 : AF F)

theorem heisLine_zero (u : Matrix (Fin n) (Fin d) (AE F E)) (Ψ : (Fin n × Fin d → AF F) → ℂ) :
    M.heisLine ψ u 0 Ψ = Ψ := by
  funext z
  simp [Model.heisLine, rho_apply, realAd_zero]

theorem hasDerivAt_heisLine (u : Matrix (Fin n) (Fin d) (AE F E)) {Φ Φ₁ : (Fin n × Fin d → AF F) → ℂ}
    (hD : ∀ x, HasDerivAt (fun t => M.heisLine ψ u t Φ x) (Φ₁ x) 0) (t : ℝ) (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun τ => M.heisLine ψ u τ Φ x) (M.heisLine ψ u t Φ₁ x) t := by
  set w := M.co.e (realAd F t • u)
  set c := ψ (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))
  have h1 : HasDerivAt (fun τ => M.heisLine ψ u (τ - t) Φ (x + w.1)) (Φ₁ (x + w.1)) t :=
    HasDerivAt.comp_sub_const t t (by simpa using hD (x + w.1))
  have hf : (fun τ => M.heisLine ψ u τ Φ x) = fun τ => c * M.heisLine ψ u (τ - t) Φ (x + w.1) := by
    funext τ
    conv_lhs => rw [show τ = t + (τ - t) by ring, heisLine_add]
    rfl
  rw [hf]
  exact h1.const_mul c

end Line

theorem finprod_add {κ : Type} (φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ) (x z : κ → AF F)
    (hz : At (evI F) z) :
    (∏ᶠ v, φ v fun i => evFin F v ((x + z) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  congr 1; funext v; congr 1; funext i; rw [Pi.add_apply, map_add, evFin_eq_zero hz, add_zero]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b := map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_algebraMap (x : F) : evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

theorem hasDerivAt_thetaSum_heisLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → ∀ (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
    ∀ (g g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (Fin n × Fin d → v.adicCompletion F) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) g g₁ →
      ∀ u' : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
        HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u' (M.heisLine ψ u t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))))
          (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ))) 0 := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ hM u _hu g g₁ φ hSB hφ hAD u'
  classical
  have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hφ.and hM.std).mono fun v h => h.1.trans h.2
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := fun x z hz => finprod_add φ x z hz
  have hrest : Rest (evI F) g r := ⟨hr, GlobalTheory.TensUniq.pure_mem_schA g φ hSB hstd⟩
  have hD : ∀ x, HasDerivAt (fun t => M.heisLine ψ u t (pure g φ) x) (pure g₁ φ x) 0 := hAD r hrest
  set c := (M.co.e u').1
  set X : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i)
  have hnorm : ∀ (h : SInf F (Fin n × Fin d)) (t : ℝ) (z : Fin n × Fin d → AF F),
      ‖M.co.rho ψ u' (M.heisLine ψ u t (pure h φ)) z‖ = ‖h ((fun i => evI F (z i + c i)) + t • X)‖ * ‖r (z + c)‖ := by
    intro h t z
    rw [rho_apply, Model.heisLine, rho_apply, norm_mul, norm_mul, GlobalTheory.StdCharFromIsStd.norm_psi hψ,
      GlobalTheory.StdCharFromIsStd.norm_psi hψ, one_mul, one_mul, map_smul, Prod.smul_fst]
    have hz : r (z + c + realAd F t • (M.co.e u).1) = r (z + c) := hr _ _ (at_realAd_smul t _)
    show ‖h (fun i => evI F ((z + c + realAd F t • (M.co.e u).1) i)) * r (z + c + realAd F t • (M.co.e u).1)‖ = _
    rw [hz, norm_mul]
    congr 3
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [evI_add, evI_mul, evI_realAd, ← Algebra.smul_def]

  let R' : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ := fun y =>
    ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i + (c i).2)
  have hR' : R' ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) :=
    ⟨(GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd).comp_continuous
        (Homeomorph.addRight (fun i => (c i).2)).continuous,
      (GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd).comp_homeomorph
        (Homeomorph.addRight (fun i => (c i).2))⟩
  obtain ⟨m, hm⟩ := exists_summable_decay hR'
  have hsum := hm (fun i => evI F (c i))
  have key : ∀ (h : SInf F (Fin n × Fin d)) (C : ℝ), (∀ p, (1 + ‖p‖) ^ m * ‖h p‖ ≤ C) → ∀ t : ℝ, |t| ≤ 1 →
      ∀ ξ : Fin n × Fin d → F,
        ‖M.co.rho ψ u' (M.heisLine ψ u t (pure h φ)) (fun i => algebraMap F (AF F) (ξ i))‖ ≤
          C * (1 + ‖X‖) ^ m * (‖R' (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ /
            (1 + ‖(fun i => mixedEmbedding F (ξ i)) + fun i => evI F (c i)‖) ^ m) := by
    intro h C hC t ht ξ
    rw [hnorm]
    have hp : (fun i => evI F (algebraMap F (AF F) (ξ i) + c i)) =
        (fun i => mixedEmbedding F (ξ i)) + fun i => evI F (c i) :=
      funext fun i => by rw [evI_add, evI_algebraMap]; rfl
    rw [hp]
    exact bound_aux h C m hC _ X t ht _ (norm_nonneg _)
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.SchwartzDecay.schwartz_bound g₁ m
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.SchwartzDecay.schwartz_bound g m
  have hderiv : ∀ (ξ : Fin n × Fin d → F), ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun t => M.co.rho ψ u' (M.heisLine ψ u t (pure g φ)) (fun i => algebraMap F (AF F) (ξ i)))
        (M.co.rho ψ u' (M.heisLine ψ u y (pure g₁ φ)) (fun i => algebraMap F (AF F) (ξ i))) y := by
    intro ξ y _
    simp only [rho_apply]
    exact (hasDerivAt_heisLine M ψ u hD y _).const_mul _
  have hbd : ∀ (ξ : Fin n × Fin d → F), ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      ‖M.co.rho ψ u' (M.heisLine ψ u y (pure g₁ φ)) (fun i => algebraMap F (AF F) (ξ i))‖ ≤
        C₁ * (1 + ‖X‖) ^ m * (‖R' (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ /
            (1 + ‖(fun i => mixedEmbedding F (ξ i)) + fun i => evI F (c i)‖) ^ m) :=
    fun ξ y hy => key g₁ C₁ hC₁ y (abs_le.2 ⟨hy.1.le, hy.2.le⟩) ξ
  have hs0 : Summable fun ξ : Fin n × Fin d → F =>
      M.co.rho ψ u' (M.heisLine ψ u 0 (pure g φ)) (fun i => algebraMap F (AF F) (ξ i)) :=
    Summable.of_norm_bounded (hsum.mul_left (C₀ * (1 + ‖X‖) ^ m)) fun ξ => key g C₀ hC₀ 0 (by simp) ξ
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have := hasDerivAt_tsum_of_isPreconnected (hsum.mul_left (C₁ * (1 + ‖X‖) ^ m)) isOpen_Ioo isPreconnected_Ioo
    hderiv hbd h0 hs0 h0
  rw [heisLine_zero] at this
  exact this

end GlobalTheory.ThetaLinePure
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_thetaSum_archimedeanHeisenbergLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → ∀ (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
    ∀ (g g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (Fin n × Fin d → v.adicCompletion F) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) g g₁ →
      ∀ u' : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
        HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u' (M.heisLine ψ u t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))))
          (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ))) 0 := by
  atlas_forward_decl GlobalTheory.ThetaLinePure.hasDerivAt_thetaSum_heisLine
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_heisenbergOp_archimedean_sum_realPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
    ∀ w : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w → ∀ x : WO S T,
      HasDerivAt (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x)
        (∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x) 0 := by
  first | exact @GlobalTheory.ArchLineSum.hasDerivAt_realAd_smul | exact GlobalTheory.ArchLineSum.hasDerivAt_realAd_smul | (intros; apply GlobalTheory.ArchLineSum.hasDerivAt_realAd_smul <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.SchDeriv

theorem exists_mem_algF_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ u : Matrix (Fin S.rank) (Fin d) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
        ∀ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ u) g g₁ →
        ∃ f₁ ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) f₁ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψB Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hφ hvac f hf hD u hu g₁ hg₁
  subst hψB
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hBs.std
  have hψ : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hstd
  have hth : ∀ Φ ∈ algF Bs.ψ θ ε A B, IsThetaFunO Bs.ψ (sgn ε S) X Φ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  have hsm : ∀ (a : AF D.host.F) (v : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • v) = a • cS v := by
    intro a v
    rw [hcS, hcS]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, Finset.smul_sum,
      smul_mul_assoc, id]
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (cS u) := by
    intro a ha
    rw [← hsm, hu a ha, map_zero]
  refine ⟨∑ τ, dRho (heisO Bs.ψ (sgn ε S) X) θ τ (compAt θ τ (cS u)) f,
    Submodule.sum_mem _ fun τ _ => GlobalTheory.T.heisenberg_derivative_mem_fockAlgebraicThetaVectors D Bs.ψ θ hψ hθ ε S X A B f hf τ _, ?_, fun u' => ?_⟩
  · exact GlobalTheory.TensUniq.pure_mem_schA g₁ φ hφ ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)
  · have h2 := GlobalTheory.T.hasDerivAt_thetaSum_archimedeanHeisenbergLine M Bs.ψ hstd hM u hu g g₁ φ hφ hvac hg₁ u'
    have h3 := GlobalTheory.T.hasDerivAt_heisenbergOp_archimedean_sum_realPlaces D Bs.ψ θ hψ hθ (sgn ε S) X f (hth f hf) (cS u) hAt (cS u')
    have heq : (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u' (M.heisLine Bs.ψ u t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)))) =
        fun t : ℝ => heisO Bs.ψ (sgn ε S) X (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u) f (cS u') := by
      funext t
      have h4 := (GlobalTheory.T.schrodingerThetaDatum_heisenberg_oriented D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f hD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)).2 u'
      rw [hsm] at h4
      exact h4
    rw [heq] at h2
    rw [h2.unique h3, Finset.sum_apply]

end GlobalTheory.SquareAgree.SchDeriv

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicVector_thetaTransform_heisenbergDerivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ u : Matrix (Fin S.rank) (Fin d) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
        ∀ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ u) g g₁ →
        ∃ f₁ ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) f₁ := by
  first | exact @GlobalTheory.SquareAgree.SchDeriv.exists_mem_algF_deriv | exact GlobalTheory.SquareAgree.SchDeriv.exists_mem_algF_deriv | (intros; apply GlobalTheory.SquareAgree.SchDeriv.exists_mem_algF_deriv <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem isDatum_zero_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z) :
    IsDatum M ψ crd 0 0 := by
  refine ⟨zero_mem _, fun u => ?_⟩
  simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem isDatum_smul_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z)
    {Φ : (Fin n × Fin d → AF F) → ℂ} {f : Z → ℂ} (h : IsDatum M ψ crd Φ f) (c : ℂ) :
    IsDatum M ψ crd (c • Φ) (c • f) := by
  refine ⟨Submodule.smul_mem _ _ h.1, fun u => ?_⟩
  rw [Pi.smul_apply, ← h.2 u]
  simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

theorem algVec_correspond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      (∀ Φ ∈ algF ψ θ ε A B, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD Φ) ∧
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ ε A B, IsDatum M ψ cS ΦD Φ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hBs.std
  have hadd : ∀ {Φ Φ' : (Fin S.rank × Fin d → AF D.host.F) → ℂ} {f f' : WO S X → ℂ},
      IsDatum M ψ cS Φ f → IsDatum M ψ cS Φ' f' → IsDatum M ψ cS (Φ + Φ') (f + f') :=
    fun h h' => GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz M ψ hstd cS _ _ _ _ h h'

  set Aop := aPlusAll (heisO ψ (sgn ε S) X) θ (fun τ => cplxO ((frSgn ε A).cart τ) (B.cart τ)) A.onb B.onb with hAop
  have hfock : ∀ f P, fockF ψ θ ε A B f P = pureTensorL Aop f P := fun f P => rfl
  have step : ∀ g : WO S X → ℂ, (∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD g) →
      ∀ k, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD (Aop k g) := by
    rintro g ⟨ΦD, hD, hd⟩ k
    obtain ⟨a, ha, h1⟩ := GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS ΦD hD g hd k.1
      (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)
    obtain ⟨b, hb, h2⟩ := GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS ΦD hD g hd k.1
      (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2))
    refine ⟨((fockScale D k.1 : ℂ)⁻¹) • (a + (-Complex.I) • b),
      Submodule.smul_mem _ _ (add_mem ha (Submodule.smul_mem _ _ hb)), ?_⟩
    have e1 := isDatum_smul_smul M ψ cS (hadd h1 (isDatum_smul_smul M ψ cS h2 (-Complex.I))) ((fockScale D k.1 : ℂ)⁻¹)
    convert e1 using 1
    simp only [hAop, aPlusAll, aPlus, crea, sub_eq_add_neg, neg_smul]
  have gen : ∀ f, IsFinF ψ θ ε A B f → ∀ P, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD (fockF ψ θ ε A B f P) := by
    intro f hf P
    have h0 := GlobalTheory.T.exists_algebraicDatum_thetaTransform_eq D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS f hf
    have hl : ∀ l : List (FVar D X.rank S.rank), ∃ ΦD ∈ algD M Bs.ψ Bs.emb,
        IsDatum M ψ cS ΦD (l.foldr (fun i g => Aop i g) f) := by
      intro l
      induction l with
      | nil => exact h0
      | cons k l ih => exact step _ ih k
    rw [hfock]
    induction P using MvPolynomial.induction_on' with
    | monomial u a =>
      have em : MvPolynomial.monomial u a = a • MvPolynomial.basisMonomials (FVar D X.rank S.rank) ℂ u := by
        rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      obtain ⟨ΦD, hD, hd⟩ := hl (Multiset.toList (Finsupp.toMultiset u))
      refine ⟨a • ΦD, Submodule.smul_mem _ _ hD, ?_⟩
      rw [em, map_smul]
      unfold pureTensorL
      rw [Module.Basis.constr_basis]
      exact isDatum_smul_smul M ψ cS hd a
    | add p q hp hq =>
      obtain ⟨a, ha, h1⟩ := hp
      obtain ⟨b, hb, h2⟩ := hq
      exact ⟨a + b, add_mem ha hb, by rw [map_add]; exact hadd h1 h2⟩
  have fin_mem : ∀ f, IsFinF ψ θ ε A B f → f ∈ algF ψ θ ε A B := by
    intro f hf
    refine Submodule.subset_span ⟨f, 1, hf, ?_⟩
    have e1 : (1 : MvPolynomial (FVar D X.rank S.rank) ℂ) = MvPolynomial.basisMonomials (FVar D X.rank S.rank) ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]; rfl
    rw [hfock, e1]
    unfold pureTensorL
    rw [Module.Basis.constr_basis]
    simp [opPow]
  refine ⟨fun Φ hΦ => ?_, fun ΦD hΦD => ?_⟩
  · induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact gen f hf P
    | zero => exact ⟨0, zero_mem _, isDatum_zero_zero M ψ cS⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, h1⟩ := hx
      obtain ⟨b, hb, h2⟩ := hy
      exact ⟨a + b, add_mem ha hb, hadd h1 h2⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, h1⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, isDatum_smul_smul M ψ cS h1 c⟩
  · have pure_add : ∀ (g g' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g + g') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ := by
      intro g g' φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
    have pure_smul : ∀ (c : ℂ) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • g) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
      intro c g φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    have pure_zero : ∀ (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) φ = 0 := by
      intro φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    let N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) :=
      { carrier := {g | ∀ (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
          ∃ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f}
        zero_mem' := fun φ _ _ => ⟨0, zero_mem _, by rw [pure_zero]; exact isDatum_zero_zero M ψ cS⟩
        add_mem' := by
          intro g g' hg hg' φ h1 h2
          obtain ⟨a, ha, d1⟩ := hg φ h1 h2
          obtain ⟨b, hb, d2⟩ := hg' φ h1 h2
          exact ⟨a + b, add_mem ha hb, by rw [pure_add]; exact hadd d1 d2⟩
        smul_mem' := by
          intro c g hg φ h1 h2
          obtain ⟨a, ha, d1⟩ := hg φ h1 h2
          exact ⟨c • a, Submodule.smul_mem _ _ ha, by rw [pure_smul]; exact isDatum_smul_smul M ψ cS d1 c⟩ }
    have hPol : M.Pol Bs.ψ Bs.emb ≤ N := by
      refine sInf_le ⟨fun g₀ hg₀ φ h1 h2 => ?_, fun u hu g hg g₁ hg₁ φ h1 h2 => ?_⟩
      · obtain ⟨f, hf, hd⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS g₀ φ hg₀ h1 h2
        exact ⟨f, fin_mem f hf, hd⟩
      · obtain ⟨f, hf, hd⟩ := hg φ h1 h2
        exact GlobalTheory.T.exists_algebraicVector_thetaTransform_heisenbergDerivative D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS g φ h1 h2 f hf hd u hu g₁ hg₁
    induction hΦD using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, φ, hg, h1, h2, rfl⟩ := hx
      exact hPol hg φ h1 h2
    | zero => exact ⟨0, zero_mem _, isDatum_zero_zero M ψ cS⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, h1⟩ := hx
      obtain ⟨b, hb, h2⟩ := hy
      exact ⟨a + b, add_mem ha hb, hadd h1 h2⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, h1⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, isDatum_smul_smul M ψ cS h1 c⟩

end GlobalTheory.SquareAgree

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicVectors_correspond_schrodinger_thetaMap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      (∀ Φ ∈ algF ψ θ ε A B, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD Φ) ∧
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ ε A B, IsDatum M ψ cS ΦD Φ := by
  atlas_forward_decl GlobalTheory.SquareAgree.algVec_correspond
end
