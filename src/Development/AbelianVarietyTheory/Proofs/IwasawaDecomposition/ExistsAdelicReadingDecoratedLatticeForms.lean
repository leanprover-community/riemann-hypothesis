import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStdWtCast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvReductionMulFlagTranslationMemRowLevelGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelCharacterTranslationEqFlagCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdelicUnitaryConjIntegralFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceSupportLevelStandardCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLevelSplitsAtOffLevelSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelTypeTrivialSplitPlaceSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdentityIntegralUnitaryFrameCoordinatesOfUnitGra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointFinitePartEqRealOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjUniformizerIsUniformizerConjPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitIdempotentAtConjugatePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrimeIdempotentMulEqZeroOfVanishingAtPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaSupportedAtPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementInvLatticeClausesOfFrameConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertNeighboursLiftsDoubleCosetTranslates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftFormsAdelicDecoratedLattices
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.PrIsoScale

section Alg

variable {T : Type} [Fintype T] [DecidableEq T] {E : T → Type}
  [∀ τ, NormedAddCommGroup (E τ)] [∀ τ, InnerProductSpace ℂ (E τ)]

def pSum (ι : T → Type) [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ))
    (φ ψ : (⨂[ℂ] τ, E τ) →ₗ[ℂ] ℂ) : ℂ :=
  ∑ f : (∀ τ, ι τ), starRingEnd ℂ (φ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) *
    ψ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))

theorem tprod_expand {ι κ : T → Type} [∀ τ, Fintype (ι τ)] [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ)) (b' : ∀ τ, OrthonormalBasis (κ τ) ℂ (E τ)) (f : ∀ τ, ι τ) :
    (PiTensorProduct.tprod ℂ fun τ => b τ (f τ)) =
      ∑ g : (∀ τ, κ τ), (∏ τ, ⟪b' τ (g τ), b τ (f τ)⟫_ℂ) • PiTensorProduct.tprod ℂ fun τ => b' τ (g τ) := by
  have h : (fun τ => b τ (f τ)) = fun τ => ∑ j, ⟪b' τ j, b τ (f τ)⟫_ℂ • b' τ j :=
    funext fun τ => ((b' τ).sum_repr' _).symm
  rw [h, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact MultilinearMap.map_smul_univ _ _ _

theorem pSum_indep {ι κ : T → Type} [∀ τ, Fintype (ι τ)] [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ)) (b' : ∀ τ, OrthonormalBasis (κ τ) ℂ (E τ))
    (φ ψ : (⨂[ℂ] τ, E τ) →ₗ[ℂ] ℂ) : pSum ι b φ ψ = pSum κ b' φ ψ := by
  classical
  unfold pSum
  set U : (∀ τ, ι τ) → (∀ τ, κ τ) → ℂ := fun f g => ∏ τ, ⟪b' τ (g τ), b τ (f τ)⟫_ℂ with hU
  set t' : (∀ τ, κ τ) → ⨂[ℂ] τ, E τ := fun g => PiTensorProduct.tprod ℂ fun τ => b' τ (g τ) with ht'
  have hχ : ∀ (χ : (⨂[ℂ] τ, E τ) →ₗ[ℂ] ℂ) (f : ∀ τ, ι τ),
      χ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ)) = ∑ g, U f g * χ (t' g) := by
    intro χ f
    rw [tprod_expand b b' f, map_sum]
    simp only [map_smul, smul_eq_mul, U, t']
  have horth : ∀ g g' : (∀ τ, κ τ), ∑ f, starRingEnd ℂ (U f g) * U f g' = if g = g' then 1 else 0 := by
    intro g g'
    calc ∑ f, starRingEnd ℂ (U f g) * U f g'
        = ∑ f : (∀ τ, ι τ), ∏ τ, (⟪b τ (f τ), b' τ (g τ)⟫_ℂ * ⟪b' τ (g' τ), b τ (f τ)⟫_ℂ) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          simp only [U, map_prod, inner_conj_symm, Finset.prod_mul_distrib]
      _ = ∏ τ, ∑ i, ⟪b τ i, b' τ (g τ)⟫_ℂ * ⟪b' τ (g' τ), b τ i⟫_ℂ := by
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      _ = ∏ τ, ⟪b' τ (g' τ), b' τ (g τ)⟫_ℂ := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          rw [← (b τ).sum_inner_mul_inner]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = ∏ τ, if g' τ = g τ then (1 : ℂ) else 0 := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          exact (b' τ).inner_eq_ite _ _
      _ = if g = g' then 1 else 0 := by
          rw [Finset.prod_boole]
          simp only [Finset.mem_univ, true_implies]
          by_cases h : g = g'
          · subst h; simp
          · rw [if_neg h, if_neg]
            intro h'
            exact h (funext fun τ => (h' τ).symm)
  simp_rw [hχ φ, hχ ψ]
  calc ∑ f, starRingEnd ℂ (∑ g, U f g * φ (t' g)) * ∑ g', U f g' * ψ (t' g')
      = ∑ g, ∑ g', starRingEnd ℂ (φ (t' g)) * ψ (t' g') * ∑ f, starRingEnd ℂ (U f g) * U f g' := by
        simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g' _ => ?_
        refine Finset.sum_congr rfl fun f _ => ?_
        ring
    _ = ∑ g, starRingEnd ℂ (φ (t' g)) * ψ (t' g) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Alg

section Alg2

variable {T : Type} [Fintype T] [DecidableEq T] {E : T → Type}
  [∀ τ, NormedAddCommGroup (E τ)] [∀ τ, InnerProductSpace ℂ (E τ)]

theorem pSum_of_iso {ι : T → Type} [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ)) (τ : T)
    (A : E τ ≃ₗᵢ[ℂ] E τ) (φ ψ φ' ψ' : (⨂[ℂ] ρ, E ρ) →ₗ[ℂ] ℂ)
    (hφ : ∀ v : ∀ ρ, E ρ, φ' (PiTensorProduct.tprod ℂ (Function.update v τ (A (v τ)))) = φ (PiTensorProduct.tprod ℂ v))
    (hψ : ∀ v : ∀ ρ, E ρ, ψ' (PiTensorProduct.tprod ℂ (Function.update v τ (A (v τ)))) = ψ (PiTensorProduct.tprod ℂ v)) :
    pSum ι b φ' ψ' = pSum ι b φ ψ := by
  let b1 : ∀ ρ, OrthonormalBasis (ι ρ) ℂ (E ρ) := Function.update b τ ((b τ).map A)
  have hv : ∀ f : (∀ ρ, ι ρ), (fun ρ => b1 ρ (f ρ)) = Function.update (fun ρ => b ρ (f ρ)) τ (A (b τ (f τ))) := by
    intro f
    funext ρ
    by_cases h : ρ = τ
    · subst h
      simp [b1, OrthonormalBasis.map_apply]
    · simp [b1, Function.update_of_ne h]
  rw [← pSum_indep b1 b]
  unfold pSum
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hv f, hφ, hψ]

end Alg2

section Model

variable {D : D7}

def smIso {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.sm τ →ₗᵢ[ℂ] M.sm τ where
  toLinearMap := (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ).restrict
    (fun w hw => GlobalTheory.SmoothStable.rep_mem_sm D V S M τ g hg w hw)
  norm_map' x := (M.ds τ).2.2.1.2.1 _ (Formalism.IndefR.SchurOrthogonalityAlt.conj_mem M τ hg) x

end Model

set_option maxHeartbeats 1000000 in

theorem exists_smul_prIso (D : D7) (θ : InfFam D) (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m))
    (cX : CoefA D.sp.X') (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ) (hθ : IsInfFam θ) (hc : cX.Is)
    (hpr : IsDualPair θ MX cX prX) : ∃ c : ℂ, c ≠ 0 ∧ Seed.PrIso MX cX (c • prX) := by
  classical
  by_cases hfin : ∀ τ, FiniteDimensional ℂ (MX.sm τ)
  swap
  · refine ⟨1, one_ne_zero, ?_⟩
    intro ι _ b
    exact absurd (fun τ => Module.Finite.of_basis (b τ).toBasis) hfin
  obtain ⟨b0⟩ : Nonempty (∀ τ, OrthonormalBasis (Fin (Module.finrank ℂ (MX.sm τ))) ℂ (MX.sm τ)) :=
    ⟨fun τ => stdOrthonormalBasis ℂ (MX.sm τ)⟩
  obtain ⟨u, hu'⟩ : ∃ u : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))) → cX.W, ∀ f x,
      ⟪u f, x⟫_ℂ = prX x (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)) :=
    ⟨fun f => (InnerProductSpace.toDual ℂ cX.W).symm
      (LinearMap.toContinuousLinearMap (prX.flip (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)))),
      fun f x => by rw [InnerProductSpace.toDual_symm_apply]; rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Module.End ℂ cX.W,
      T = ∑ f, (prX.flip (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))).smulRight (u f) := ⟨_, rfl⟩
  have hT : ∀ w w', ⟪w, T w'⟫_ℂ = pSum _ b0 (prX w) (prX w') := by
    intro w w'
    rw [hTdef, LinearMap.sum_apply, inner_sum]
    unfold pSum
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [LinearMap.smulRight_apply]
    simp only [inner_smul_right, LinearMap.flip_apply]
    have e2 : ⟪w, u f⟫_ℂ = starRingEnd ℂ (prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))) := by
      rw [← hu' f w, inner_conj_symm]
    simp only [e2]
    ring

  have hinv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ w w',
      pSum _ b0 (prX (cX.ρ (atTau θ D.sp.X' τ g) w)) (prX (cX.ρ (atTau θ D.sp.X' τ g) w')) =
        pSum _ b0 (prX w) (prX w') := by
    intro τ g hg w w'
    obtain ⟨A, hA⟩ : ∃ A : MX.sm τ ≃ₗᵢ[ℂ] MX.sm τ, ∀ x, ((A x : MX.sm τ) : MX.H τ) = MX.rep τ g x :=
      ⟨(smIso MX τ hg).toLinearIsometryEquiv rfl, fun x => rfl⟩
    exact pSum_of_iso b0 τ A _ _ _ _ (fun v => hpr.2 τ g hg w v (A (v τ)) (hA _))
      (fun v => hpr.2 τ g hg w' v (A (v τ)) (hA _))

  have hρinv : ∀ (h : GA D D.sp.X') (z : cX.W), cX.ρ h (cX.ρ h⁻¹ z) = z := by
    intro h z
    have e : cX.ρ h * cX.ρ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun F : Module.End ℂ cX.W => F z) e
  have hcommAt : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ),
      T * cX.ρ (atTau θ D.sp.X' τ g) = cX.ρ (atTau θ D.sp.X' τ g) * T := by
    intro τ g hg
    apply LinearMap.ext
    intro w'
    apply ext_inner_left ℂ
    intro z
    obtain ⟨w, rfl⟩ : ∃ w, cX.ρ (atTau θ D.sp.X' τ g) w = z :=
      ⟨cX.ρ (atTau θ D.sp.X' τ g)⁻¹ z, hρinv _ z⟩
    have e1 := hT (cX.ρ (atTau θ D.sp.X' τ g) w) (cX.ρ (atTau θ D.sp.X' τ g) w')
    have e2 := hinv τ g hg w w'
    have e3 := hT w w'
    have e4 := hc.2.1 (atTau θ D.sp.X' τ g) w (T w')
    simp only [Module.End.mul_apply]
    rw [e1, e2, ← e3, e4]
  let U : Submonoid (GA D D.sp.X') := (Submonoid.centralizer ({T} : Set (Module.End ℂ cX.W))).comap cX.ρ
  have hU : ∀ h, h ∈ U ↔ T * cX.ρ h = cX.ρ h * T := by
    intro h
    simp [U, Submonoid.mem_centralizer_iff]
  have hall : ∀ h, T * cX.ρ h = cX.ρ h * T := by
    intro h
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D D.sp.X').1 h
    have h1 : a ∈ U := GlobalTheory.DefiniteMult.real_le hθ U (fun τ g hg => (hU _).2 (hcommAt τ g hg)) ha
    have h2 : k ∈ U := (hU k).2 (by rw [hc.1 k hk, mul_one, one_mul])
    exact (hU _).1 (U.mul_mem h1 h2)

  haveI : Nontrivial cX.W := hc.2.2.2.1
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  have hstab : ∀ h, (T.eigenspace μ).map (cX.ρ h) ≤ T.eigenspace μ := by
    intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx
    rw [Module.End.mem_eigenspace_iff]
    have e := congrArg (fun F : Module.End ℂ cX.W => F x) (hall h)
    simp only [Module.End.mul_apply] at e
    rw [e, hx, map_smul]
  have hE : T.eigenspace μ = ⊤ := by
    rcases hc.2.2.2.2 (T.eigenspace μ) hstab with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hμ)
    · exact h
  have hTμ : ∀ x, T x = μ • x := fun x =>
    Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top)

  obtain ⟨w, hw⟩ : ∃ w, prX w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hpr.1 (LinearMap.ext h)
  obtain ⟨f0, hf0⟩ : ∃ f : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))),
      prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw
    refine (Basis.piTensorProduct fun τ => (b0 τ).toBasis).ext fun f => ?_
    rw [Basis.piTensorProduct_apply]
    simpa using h f
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (map_zero prX)
  have hsq : ∀ z : ℂ, starRingEnd ℂ z * z = (‖z‖ : ℂ) ^ 2 := fun z => Complex.conj_mul' z
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ pSum _ b0 (prX w) (prX w) = (s : ℂ) := by
    refine ⟨∑ f : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))),
      ‖prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))‖ ^ 2, ?_, ?_⟩
    · exact Finset.sum_pos' (fun f _ => sq_nonneg _) ⟨f0, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hf0) 2⟩
    · unfold pSum
      push_cast
      exact Finset.sum_congr rfl fun f _ => hsq _
  have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw0) 2
  set r : ℝ := s / ‖w‖ ^ 2 with hr
  have hr0 : 0 < r := div_pos hs0 hwpos
  have hμr : μ = (r : ℂ) := by
    have e1 := hT w w
    have e2 : ⟪w, T w⟫_ℂ = μ * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      have hww : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
        first
          | (rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl)
          | exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w
          | simp [inner_self_eq_norm_sq_to_K]
      rw [hTμ, inner_smul_right, hww]
    rw [e2, hs] at e1
    have hn : ((‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hwpos.ne'
    rw [hr, Complex.ofReal_div, eq_div_iff hn]
    exact e1

  refine ⟨((Real.sqrt r)⁻¹ : ℝ), Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_ne_zero'.2 hr0)), ?_⟩
  have hcc : starRingEnd ℂ (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (((Real.sqrt r)⁻¹ : ℝ) : ℂ) = ((r⁻¹ : ℝ) : ℂ) := by
    rw [hsq, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs, inv_pow, Real.sq_sqrt hr0.le]
  intro ι _ b w₁ w₂
  have e : (starRingEnd ℂ (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (((Real.sqrt r)⁻¹ : ℝ) : ℂ)) * pSum ι b (prX w₁) (prX w₂) =
      ∑ f : (∀ τ, ι τ), starRingEnd ℂ (((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • prX) w₁ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) *
        ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • prX) w₂ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ)) := by
    unfold pSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring
  refine Eq.trans ?_ e
  have e3 : pSum ι b (prX w₁) (prX w₂) = μ * ⟪w₁, w₂⟫_ℂ := by
    rw [pSum_indep b b0, ← hT, hTμ, inner_smul_right]
  rw [e3, hcc, hμr, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hr0.ne', Complex.ofReal_one, one_mul]

end GlobalTheory.PrIsoScale
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.FlagOnto

theorem exists_flag_rTup : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (t : TupU I U) (y : G0 L.Pg X.toD7.R.r), ∃ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
      rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) = y := by
  intro X px I hX U L hI hV hL t y
  obtain ⟨c, hc⟩ := hL.is.βX
  have hsep := GlobalTheory.ChainEquiv.places_sep L (mu0F (tuOf I U)) hL.is t
  obtain ⟨κ, -, hκP, hκr⟩ := GlobalTheory.ParahoricLift.liftsExist X.toD7.sp.X' L.βX (L.datXt t) L.ΛX _ hc hsep.1 hsep.2 y
  exact ⟨⟨(finHom X.toD7.sp.X').rangeRestrict κ, hκP, Subgroup.mem_top _⟩, hκr⟩

end GlobalTheory.Mem.R3.FlagOnto

end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco

theorem deco_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q),
    ∃ u : ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (∀ h : Bridge.Gf X.toD7.sp.X', RowAd.decoAd X I t (h * (q : Bridge.Gf X.toD7.sp.X')) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
          (u : Formalism.L2.Col.GLG X.B.fields.E (X.B.R.N X.B.R.m - 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
            (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
              (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)))))⁻¹) •
          RowAd.decoAd X I t h) ∧
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr u : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  intro X px I hX U L eG hI hV hL hG t q
  have hz := unitaryFiniteAdelicPointAsMatrix_mem_flagIwahori X I hI L hL t q
  have hu := GlobalTheory.T.inv_reduction_mul_flagTranslation_mem_rowLevelGroup X px I U L eG hI hL hG t q hz
  refine ⟨⟨_, hu⟩, fun h => ?_, GlobalTheory.T.rowLevelCharacter_translation_eq_flagCharacter X px I U L eG hI hV hL hG t q hz hu⟩
  refine (decoAd_mul X I hI t h _ hz).trans ?_
  refine congrArg (fun a : Formalism.L2.Col.GLG X.B.fields.E (X.B.R.N X.B.R.m - 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) =>
    ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)), a) • RowAd.decoAd X I t h) ?_
  exact (mul_inv_cancel_right _ _).symm

end GlobalTheory.Mem.R3.RowDeco
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q),
    ∃ u : ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (∀ h : Bridge.Gf X.toD7.sp.X', RowAd.decoAd X I t (h * (q : Bridge.Gf X.toD7.sp.X')) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
          (u : Formalism.L2.Col.GLG X.B.fields.E (X.B.R.N X.B.R.m - 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
            (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
              (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)))))⁻¹) •
          RowAd.decoAd X I t h) ∧
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr u : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  atlas_forward_decl GlobalTheory.Mem.R3.RowDeco.deco_tie
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Forms

variable {Xf : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 Xf.E))}
  (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet Xf.E n ST SG)) (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)

theorem eqFun_smul_grp (φ : (Formalism.L2.Col.formGSD C Λ).EqFun) (u : Λ.grp) (a : Formalism.L2.Col.GLG Xf.E n SG)
    (d : Formalism.L2.Col.DecoSet Xf.E n ST SG) :
    (φ : Formalism.L2.Col.DecoSet Xf.E n ST SG → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG Xf.E n SG) * a) • d) =
      ((Λ.chr u : Xf.Kˣ) : Xf.K) • (φ : Formalism.L2.Col.DecoSet Xf.E n ST SG → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) := by
  have e := φ.2 ((1, u) : Formalism.L2.Col.FormG Λ) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d)
  have e' : ((1, u) : Formalism.L2.Col.FormG Λ) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) =
      ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG Xf.E n SG) * a) • d := by
    show ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG Xf.E n SG)) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) = _
    rw [smul_smul, Prod.mk_mul_mk, one_mul]
  rw [e'] at e
  rw [e]
  show ((Λ.chr u : Xf.Kˣ) : Xf.K) • C.rho 1 _ = _
  rw [map_one]
  rfl

end Forms

theorem semilin_inv_smul {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    {σ : K →+* ℂ} (m : V →ₛₗ[σ] W) (k : K) (c : ℂˣ) (hk : σ k = c) (x : V) :
    m x = ((c⁻¹ : ℂˣ) : ℂ) • m (k • x) := by
  rw [LinearMap.map_smulₛₗ, hk, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory.Mem.R3.RowAct

namespace GlobalTheory.Mem.R3.RowAct

theorem act_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      ∃ a : Bridge.ActTie (Bridge.ratF X.toD7.sp.X') P (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q (levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch ((famR X I hX U Xg tr).A.leftGroupActionRight t),
        ∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
          eG (a.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hTie hinner t P hRD
  refine ⟨{
      red := eG.symm.toMonoidHom.comp (rTupQ X.toD7.sp.X' L.βX (L.datXt t))
      red_surj := ?_
      red_ker := ?_
      act_eq := ?_ }, ?_⟩
  · intro g
    have key := GlobalTheory.Mem.R3.FlagOnto.exists_flag_rTup X px I hX U L hI hV hL t (eG g)
    obtain ⟨q, hq⟩ := key
    refine ⟨q, ?_⟩
    have e : rTupQ X.toD7.sp.X' L.βX (L.datXt t) q = eG g := hq
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = g
    rw [e, MulEquiv.symm_apply_apply]
  · intro q
    have e := rTupQ_eq_one_iff X.toD7.sp.X' L.βX (L.datXt t) q
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = 1 ↔ _
    exact (MulEquiv.map_eq_one_iff eG.symm).trans e
  · intro g κ hκ f
    obtain ⟨m, hm⟩ := hRD
    obtain ⟨u, hdeco, hch⟩ := GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation X px I hX U L eG hI hV hL hG t κ
    have hg : eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf X.toD7.sp.X') : GL _ _))) = g := hκ
    rw [hg] at hdeco
    funext h
    have e1 := hm ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) h
    have e2 := hm f (h * (κ : Bridge.Gf X.toD7.sp.X'))
    refine e1.trans ?_
    refine Eq.trans ?_ (congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • v) e2).symm
    have e3 : ((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm
        ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) = Formalism.L2.Col.g0HatRepEqFunX X.B.wts I.Ch I.sel t.1 g
          (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f) :=
      LinearEquiv.symm_apply_apply _ _
    have e4 := eqFun_smul_grp _ _ (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f)
      u (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g)⁻¹ (RowAd.decoAd X I t h)
    refine (congrArg (fun ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).EqFun =>
      m ((ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).D → (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).V)
        (RowAd.decoAd X I t h))) e3).trans ?_
    refine (semilin_inv_smul m _ _ hch _).trans ?_
    refine congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • m v) ?_
    exact e4.symm.trans (congrArg _ (hdeco h).symm)
  · intro q
    have e : eG (eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q)) = rTupQ X.toD7.sp.X' L.βX (L.datXt t) q :=
      MulEquiv.apply_symm_apply _ _
    exact e

end GlobalTheory.Mem.R3.RowAct
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormsFiniteGroupAction_eq_flagLevelRightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      ∃ a : Bridge.ActTie (Bridge.ratF X.toD7.sp.X') P (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q (levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch ((famR X I hX U Xg tr).A.leftGroupActionRight t),
        ∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
          eG (a.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) := by
  atlas_forward_decl GlobalTheory.Mem.R3.RowAct.act_tie
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg GlobalTheory.Mem.R3.LiftBrg.SplitLoc
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.Mem.R3.RowHk

theorem isDC_map {G H : Type} [Group G] [Group H] (Φ : G ≃* H) (K : Subgroup G) (K' : Subgroup H)
    (hK : ∀ u, Φ u ∈ K' ↔ u ∈ K) {x : G} {R : Finset G} (h : Bridge.IsDC K x R) :
    Bridge.IsDC K' (Φ x) (R.map Φ.toEquiv.toEmbedding) := by
  have hK' : ∀ y : H, y ∈ K' ↔ Φ.symm y ∈ K := fun y => by rw [← hK, MulEquiv.apply_symm_apply]
  have hmem : ∀ b, b ∈ R.map Φ.toEquiv.toEmbedding ↔ Φ.symm b ∈ R := by
    intro b
    rw [Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hb
      exact ⟨Φ.symm b, hb, by simp⟩
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · have hu := (hmem a).1 ha
    obtain ⟨k₁, k₂, e⟩ := h.1 _ hu
    refine ⟨⟨Φ k₁, (hK _).2 k₁.2⟩, ⟨Φ k₂, (hK _).2 k₂.2⟩, ?_⟩
    show a = Φ k₁ * Φ x * Φ k₂
    rw [← map_mul, ← map_mul, ← e, MulEquiv.apply_symm_apply]
  · obtain ⟨k₁, k₂, e⟩ := hg
    have hg' : Φ.symm g = Φ.symm k₁ * x * Φ.symm k₂ := by
      rw [e, map_mul, map_mul, MulEquiv.symm_apply_apply]
    obtain ⟨a, ⟨ha, haK⟩, hu⟩ := h.2 (Φ.symm g) ⟨⟨_, (hK' _).1 k₁.2⟩, ⟨_, (hK' _).1 k₂.2⟩, hg'⟩
    refine ⟨Φ a, ⟨(hmem _).2 (by simpa using ha), ?_⟩, ?_⟩
    · rw [hK', map_mul, map_inv, MulEquiv.symm_apply_apply]
      exact haK
    · rintro b ⟨hb, hbK⟩
      have hb' := (hmem b).1 hb
      rw [hK', map_mul, map_inv] at hbK
      have := hu (Φ.symm b) ⟨hb', hbK⟩
      rw [← this, MulEquiv.apply_symm_apply]

section Std

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Formalism.L2.DIV.Pl E}
  (U : Formalism.L2.Col.MhlUnif Pb) (k : ℕ)

theorem rep_mem_dc {a : Formalism.L2.Col.UAd hc n}
    (ha : (QuotientGroup.mk a : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) ∈ Formalism.L2.Col.mhlCosets hc v U k) :
    ∃ κ₁ ∈ Formalism.L2.Col.mhlKv hc n v, ∃ κ₂ ∈ Formalism.L2.Col.mhlKv hc n v, a = κ₁ * Formalism.L2.Col.mhlEta hc n v U.hπ0 k * κ₂ := by
  obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := Formalism.L2.Col.mhl_cosets_out hc U k ha
  obtain ⟨h, eh⟩ := QuotientGroup.mk_out_eq_mul (Formalism.L2.Col.mhlKv hc n v) a
  refine ⟨κ₁, h₁, κ₂ * (h : Formalism.L2.Col.UAd hc n)⁻¹, Subgroup.mul_mem _ h₂ (Subgroup.inv_mem _ h.2), ?_⟩
  rw [← mul_assoc, ← e, eh, mul_inv_cancel_right]

theorem isDC_of_reps (R : Finset (Formalism.L2.Col.UAd hc n))
    (hR : Set.BijOn (fun η : Formalism.L2.Col.UAd hc n => (QuotientGroup.mk η : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v)) R
      (Formalism.L2.Col.mhlCosets hc v U k)) :
    Bridge.IsDC (Formalism.L2.Col.mhlKv hc n v) (Formalism.L2.Col.mhlEta hc n v U.hπ0 k) R := by
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := rep_mem_dc hc U k (hR.mapsTo ha)
    exact ⟨⟨κ₁, h₁⟩, ⟨κ₂, h₂⟩, e⟩
  · obtain ⟨k₁, k₂, e⟩ := hg
    have hc' : (QuotientGroup.mk g : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) ∈ Formalism.L2.Col.mhlCosets hc v U k :=
      ⟨k₁, k₁.2, k₂, k₂.2, by rw [e]⟩
    obtain ⟨a, ha, hag⟩ := hR.surjOn hc'
    refine ⟨a, ⟨ha, QuotientGroup.eq.1 hag⟩, fun b hb => ?_⟩
    apply hR.injOn hb.1 ha
    have hag' : (QuotientGroup.mk a : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) = QuotientGroup.mk g := hag
    show (QuotientGroup.mk b : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) = QuotientGroup.mk a
    rw [hag']
    exact QuotientGroup.eq.2 hb.2

theorem reps_off (R : Finset (Formalism.L2.Col.UAd hc n))
    (hR : Set.BijOn (fun η : Formalism.L2.Col.UAd hc n => (QuotientGroup.mk η : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v)) R
      (Formalism.L2.Col.mhlCosets hc v U k)) (u : Formalism.L2.Col.UAd hc n) (hu : u ∈ R)
    (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) :
    Formalism.UG.bc (Formalism.UG.prV (E := E) w) (u : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 := by
  obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := rep_mem_dc hc U k (hR.mapsTo hu)
  rw [e]
  exact Formalism.L2.Col.mhl_off_mul hc (Formalism.L2.Col.mhl_off_mul hc h₁.1 (Formalism.L2.Col.mhlEta_off hc U k)) h₂.1 w hw

theorem reps_bij (ST SG : Finset (Formalism.L2.DIV.Pl E)) (hov : Formalism.L2.Col.IsOver v Pb)
    (hST : ∀ Q ∈ ST, ¬ Formalism.L2.Col.IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ Formalism.L2.Col.IsOver v Q)
    (hsp : Formalism.L2.Col.conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) (R : Finset (Formalism.L2.Col.UAd hc n))
    (hR : Set.BijOn (fun η : Formalism.L2.Col.UAd hc n => (QuotientGroup.mk η : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v)) R
      (Formalism.L2.Col.mhlCosets hc v U k)) (Q : Formalism.L2.DIV.Pl E) (hQ : Formalism.L2.Col.conjPrime₂ Pb = Q) (y : Formalism.L2.Col.UAd hc n) (d : Formalism.L2.Col.DecoSet E n ST SG)
    (hd : Formalism.L2.Col.decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d) :
    Set.BijOn (fun u : Formalism.L2.Col.UAd hc n => Formalism.L2.Col.decoOf ST SG ((y * u : Formalism.L2.Col.UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
      (R : Set (Formalism.L2.Col.UAd hc n)) (d.heckeSet Q.asIdeal k) := by
  subst hQ hd
  have hB := Formalism.L2.Col.mhl_split_bij' hc U k ST SG hov hST hSG hsp hk y
  have hout := Formalism.L2.Col.mhs_decoOf_out hc (v := v) ST SG hST hSG y
  refine ⟨fun u hu => ?_, fun u hu u' hu' h => ?_, fun d hd => ?_⟩
  · have := hB.mapsTo (hR.mapsTo hu)
    simp only [hout] at this
    exact this
  · have h' : Formalism.L2.Col.decoOf ST SG ((y * (QuotientGroup.mk u : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v).out : Formalism.L2.Col.UAd hc n) :
        GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        Formalism.L2.Col.decoOf ST SG ((y * (QuotientGroup.mk u' : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v).out : Formalism.L2.Col.UAd hc n) :
        GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      rw [hout, hout]; exact h
    exact hR.injOn hu hu' (hB.injOn (hR.mapsTo hu) (hR.mapsTo hu') h')
  · obtain ⟨c, hc', rfl⟩ := hB.surjOn hd
    obtain ⟨u, hu, rfl⟩ := hR.surjOn hc'
    exact ⟨u, hu, (hout u).symm⟩

end Std

theorem bijOn_map_equiv {G H T : Type} [Group G] [Group H] (Φ : G ≃* H) (R : Finset G) (S : Set T) (f : G → T) (f' : H → T)
    (hf : Set.BijOn f (R : Set G) S) (he : ∀ u, f' (Φ u) = f u) :
    Set.BijOn f' ((R.map Φ.toEquiv.toEmbedding : Finset H) : Set H) S := by
  have hmem : ∀ b, b ∈ R.map Φ.toEquiv.toEmbedding ↔ Φ.symm b ∈ R := by
    intro b
    rw [Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hb
      exact ⟨Φ.symm b, hb, by simp⟩
  refine ⟨fun b hb => ?_, fun b hb b' hb' h => ?_, fun d hd => ?_⟩
  · have := hf.mapsTo ((hmem b).1 hb)
    rwa [← he, MulEquiv.apply_symm_apply] at this
  · have h' : f (Φ.symm b) = f (Φ.symm b') := by rw [← he, ← he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h
    have := hf.injOn ((hmem b).1 hb) ((hmem b').1 hb') h'
    simpa using congrArg Φ this
  · obtain ⟨u, hu, rfl⟩ := hf.surjOn hd
    exact ⟨Φ u, (hmem _).2 (by simpa using hu), he u⟩

theorem heckeCSD_symm_apply {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} {ST SG' : Finset (HeightOneSpectrum (𝓞 E))} (S : Formalism.L2.Col.GSD K) (h : S.Ok) (c : Formalism.L2.Col.DecoPts S E n ST SG')
    (SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) (x : Formalism.L2.DIV.offSub ST SG SG' S0 × ℕ)
    (f : (S.toCSD h).Forms) :
    (S.res h).symm (Formalism.L2.DIV.heckeCSD S h c SG S0 x f) = Formalism.L2.Col.heckeFam c S0 (⟨x.1.1.1, x.1.2⟩, x.2) ((S.res h).symm f) :=
  (S.res h).symm_apply_apply _

section Gen

variable {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank)

theorem std_equiv (hG : V.gram = 1) :
    ∃ Φ : Formalism.L2.Col.UAd D.sp.cm n ≃* Bridge.Gf V, ∀ u,
      castGL h.symm (Formalism.UG.bc (swapAE D) ((Φ u : Bridge.Gf V) : GL (Fin V.rank) _)) = (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) := by
  let c : Bridge.Gf V →* GL (Fin n) (Formalism.IndefR.Lev.EAf D) :=
    (castGL h.symm).toMonoidHom.comp ((Formalism.UG.bc (swapAE D)).comp (Bridge.Gf V).subtype)
  have hc : ∀ g, c g = castGL h.symm (Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _)) := fun _ => rfl
  have hmem : ∀ g : Bridge.Gf V, c g ∈ Formalism.L2.Col.UAd D.sp.cm n := by
    intro g
    have hUA : Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _) ∈ UA D.sp.cm V.gram := by
      obtain ⟨κ, hκ⟩ := g.2
      rw [← hκ]
      exact GlobalTheory.LevFinCong.finE_mem_UA V κ
    rw [hG] at hUA
    exact (castGL_mem_UA_one D.sp.cm h.symm _).2 hUA
  let ψ : Bridge.Gf V →* Formalism.L2.Col.UAd D.sp.cm n := c.codRestrict _ hmem
  have hinj : Function.Injective ψ := by
    intro a b hab
    have e : c a = c b := congrArg Subtype.val hab
    rw [hc, hc] at e
    exact Subtype.ext (FrameEquiv.bc_swapAE_injective D V.rank ((castGL h.symm).injective e))
  have hsurj : Function.Surjective ψ := by
    intro u
    have hw : castGL h (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) ∈ UA D.sp.cm V.gram := by
      rw [hG]
      exact (castGL_mem_UA_one D.sp.cm h _).2 u.2
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.AdIsomCorrection.exists_finE V _ hw
    refine ⟨⟨finHom V κ, κ, rfl⟩, Subtype.ext ?_⟩
    change castGL h.symm (finE V κ) = _
    rw [hκ, FrameEquiv.castGL_castGL_symm h.symm]
  let Ψ := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  exact ⟨Ψ.symm, fun u => congrArg Subtype.val (Ψ.apply_symm_apply u)⟩

variable (L' : LevDat D.host.E ℂ V.rank) (SG : Finset (Pl D.host.E)) (hsub : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP ∈ SG)
  {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (x : ok × ℕ) (hoffP : pl x.1 ∈ Formalism.L2.DIV.offSet ∅ SG ∅)

include hsub hoffP

theorem under_ne : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP.under (𝓞 D.host.F) ≠ (pl x.1).under (𝓞 D.host.F) := by
  intro PP hPP hu
  have hm := hsub PP hPP
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with e | e
  · exact hoffP.2.1 (Or.inr (e ▸ hm))
  · apply hoffP.2.2 PP (Or.inr hm)
    rw [Formalism.L2.Col.conjIdeal_asIdeal, GlobalTheory.PlaceDict.conjP_eq_conjPl D, e]

theorem chi_loc (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (j : (levEnv V β L').J) (hj : isLocEnv V pl ok x j) :
    (levEnv V β L').χ j = 1 := by
  have e : (levEnv V β L').χ j = Formalism.L2.DIV.levFn β (flag1L L') (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) := rfl
  have hm : Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L') := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hloc := (isLocEnv_iff V pl ok x j hoffP.1).1 hj
  rw [e]
  exact GlobalTheory.LevSplit.levFn_eq_one _ _ _ fun PP hPP =>
    GlobalTheory.Mem.R3.LiftInertChi.redFn_eq_one_of_locAt _ _ hSt _ hloc PP (under_ne V L' SG hsub pl ok x hoffP PP hPP)

theorem lev_split (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hβ' : IsSDFrame V β Λ 1) (j : Bridge.Gf V) (hj : j ∈ (levEnv V β L').J) :
    ∃ j₁ ∈ (levEnv V β L').J, ∃ j₂ ∈ (levEnv V β L').J,
      isLocEnv V pl ok x j₁ ∧ j = j₁ * j₂ ∧ ∀ l, isLocEnv V pl ok x l → Commute j₂ l := by
  classical
  obtain ⟨hPc, hPn, hPq⟩ := hoffP
  obtain ⟨c, hβ⟩ := hβ'
  rw [one_pow] at hβ
  have hoff : ∀ PP, PP ∈ (flag1L L').Pg ∨ PP ∈ (flag1L L').Q → PP ≠ pl x.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl x.1) := by
    intro PP hPP
    have hm : PP ∈ SG := hsub PP hPP
    refine ⟨fun e => hPn (Or.inr (e ▸ hm)), fun hc => hPq PP (Or.inr hm) ?_⟩
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt (pl x.1) hPc
  have hpi : IsPrimeIdem (pl x.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 (pl x.1) e _ hpi
  have hff := h01.1
  have hcf := h01.2.1
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl x.1).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl x.1).isPrime.ne_top
  obtain ⟨-, -, hsp⟩ := (GlobalTheory.LevSplit.lev_split V β Λ 1 (flag1L L') hβ).2 (pl x.1) e _ hpi h1 hoff
  obtain ⟨g, hg, hgj⟩ := GlobalTheory.SplitHeckeAdj.fin_lift V j
  have hj' : GlobalTheory.SplitHeckeAdj.fin V g ∈ (levEnv V β L').J := by rw [hgj]; exact hj
  obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, hk⟩ := hsp g ((GlobalTheory.SplitHeckeAdj.mem_J V β L' hg).1 hj')
  refine ⟨GlobalTheory.SplitHeckeAdj.fin V k₁, (GlobalTheory.SplitHeckeAdj.mem_J V β L' h₁.1).2 h₁,
    GlobalTheory.SplitHeckeAdj.fin V k₂, (GlobalTheory.SplitHeckeAdj.mem_J V β L' h₂.1).2 h₂, ⟨e, k₁, he, h₁.1, s₁, rfl⟩,
    by rw [← hgj, hk, map_mul], ?_⟩
  intro l hl
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp V hl he
  exact (GlobalTheory.SplitHeckeAdj.commute_compl V _ hff hcf ha s₂).symm.map (GlobalTheory.SplitHeckeAdj.fin V)

theorem loc_iff_std (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : Formalism.L2.Col.IsOver v (pl x.1)) (g : Bridge.Gf V)
    (u : Formalism.L2.Col.UAd D.sp.cm n)
    (hg : castGL h.symm (Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _)) = (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D))) :
    (isLocEnv V pl ok x g ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v →
        Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1) ∧
    (isLocEnv V pl ok x g → (g ∈ (levEnv V 1 L').J ↔ u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v)) := by
  have hunder : (pl x.1).under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hv.symm
  have hA1 : isLocEnv V pl ok x g ↔ GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v g := by
    rw [← hunder]
    exact isLocEnv_iff V pl ok x g hoffP.1
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 D.host.F),
      (Units.val (g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))).map
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w) (AlgHom.id D.host.F D.host.E)) = 1 ↔
      Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1 := by
    intro w
    rw [← bc_prV_swap_eq_one_iff, ← castGL_eq_one_iff h.symm, ← bc_castGL, hg]
  have hA2 : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v g ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v →
      Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1 :=
    forall₂_congr fun w _ => hcomp w
  refine ⟨hA1.trans hA2, fun hloc => ?_⟩
  have hL1 := hA1.1 hloc
  have hu1 := hA2.1 hL1
  have hU : Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _) ∈ UA D.sp.cm V.gram := by
    obtain ⟨κ, hκ⟩ := g.2
    rw [← hκ]
    exact GlobalTheory.LevFinCong.finE_mem_UA V κ
  have hoff : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP.under (𝓞 D.host.F) ≠ v := by
    rw [← hunder]
    exact under_ne V L' SG hsub pl ok x hoffP
  rw [mem_levJ_iff V 1 L' g v hL1 hU hoff, mem_mhlKv_iff_St u hu1, ← castGL_mem_St h.symm, hg]

omit hsub hoffP in

theorem eta_isT_std (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hβ : IsSDFrame V 1 Λ 1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Pl D.host.E) (hPb : Formalism.L2.Col.conjPrime₂ Pb = pl x.1) (hv : Formalism.L2.Col.IsOver v Pb)
    (Ut : Formalism.L2.Col.MhlUnif Pb) (g : Bridge.Gf V)
    (hg : castGL h.symm (Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _)) =
      ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2 : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D))) :
    isTEnv V pl ok x g := by
  intro hx2
  obtain ⟨α₀, hα₀, hfin⟩ := GlobalTheory.T.exists_adelicPoint_finitePart_eq_realOne V g
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_splitIdempotent_at_conjugatePrime Pb Ut
  obtain ⟨h1, h2⟩ := GlobalTheory.T.conj_uniformizer_isUniformizer_conjPrime Pb Ut
  have hdict := GlobalTheory.T.mem_completedSelfDualLattice_iff_integral_stdFrame V Λ hβ
  have heps := GlobalTheory.T.conjPrimeIdempotent_mul_eq_zero_of_vanishing_at_place v Pb e hv he
  have hg' : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α₀)) =
      1 * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2 : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * 1⁻¹ := by
    rw [hfin, inv_one, mul_one, one_mul]; exact hg
  have hs := GlobalTheory.T.frameTransport_eta_supported_at_placeIdempotent V n h v Pb Ut x.2 e 1 α₀ hv he hα₀ hg'
  have hl := GlobalTheory.T.heckeElementInv_latticeClauses_of_frameConj V n h v Pb Ut x.2 e 1 α₀ he heps hdict (one_mem _) hα₀ hg'
  have hd := GlobalTheory.T.heckeElement_uniformizerRatio_determinant V n h v Pb Ut x.2 e 1 α₀ (h ▸ hx2) he heps hα₀ hg'
  rw [← hPb]
  refine ⟨α₀⁻¹, ⟨e, Formalism.L2.Col.cO D.host.E Ut.π, he, h1, h2, (GfC _).inv_mem hα₀, GlobalTheory.SplitPlace.suppAt_inv hs, hl.1, hl.2, hd⟩, ?_⟩
  rw [inv_inv, hfin]

theorem loc_data (hG : V.gram = 1) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hβ : IsSDFrame V 1 Λ 1)
    (hx2 : x.2 ≤ V.rank) :
    ∃ (hx : Bridge.Gf V) (hA : Finset (Bridge.Gf V)),
      isTEnv V pl ok x hx ∧ (∀ a ∈ hA, isLocEnv V pl ok x a) ∧ Bridge.IsDC (levEnv V 1 L').J hx hA ∧
      ∀ g : Bridge.Gf V, Set.BijOn (fun a : Bridge.Gf V => Formalism.L2.Col.decoOf ∅ SG
          (castGL h.symm (Formalism.UG.bc (swapAE D) ((g * a : Bridge.Gf V) : GL (Fin V.rank) _)))) (hA : Set (Bridge.Gf V))
        ((Formalism.L2.Col.decoOf ∅ SG (castGL h.symm (Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _)))).heckeSet (pl x.1).asIdeal x.2) := by
  obtain ⟨Φ, hΦ⟩ := std_equiv V n h hG
  obtain ⟨hc1, hc2, hc3⟩ := id hoffP
  let P : Pl D.host.E := pl x.1
  let Pb : Pl D.host.E := Formalism.L2.Col.conjPrime₂ P
  have hcc : Formalism.L2.Col.conjPrime₂ Pb = P := Formalism.L2.Col.conjPrime_conjPrime P
  obtain ⟨v, hov⟩ : ∃ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Col.IsOver v Pb :=
    ⟨HeightOneSpectrum.under (𝓞 D.host.F) Pb, rfl⟩
  have hovP : Formalism.L2.Col.IsOver v P := hcc ▸ Formalism.L2.Col.tud_isOver_conj D.sp.cm hov
  have hsp : Formalism.L2.Col.conjPrime₂ Pb ≠ Pb := by
    intro e
    apply hc1
    exact (Formalism.L2.Col.conjIdeal_asIdeal P).trans (congrArg HeightOneSpectrum.asIdeal (hcc.symm.trans e).symm)
  have hST : ∀ Q ∈ (∅ : Finset (Pl D.host.E)), ¬ Formalism.L2.Col.IsOver v Q := by simp
  have hSG : ∀ Q ∈ SG, ¬ Formalism.L2.Col.IsOver v Q := by
    intro Q hQ hQv
    rcases Formalism.L2.Col.mhl_over_eq D.sp.cm hov Q hQv with e | e
    · exact hc3 Q (Or.inr hQ) ((congrArg HeightOneSpectrum.asIdeal e).trans (Formalism.L2.Col.conjIdeal_asIdeal P).symm)
    · have e' : Q = P := e.trans hcc
      exact hc2 (Set.mem_union_right _ (Finset.mem_coe.2 (show P ∈ SG from e' ▸ hQ)))
  obtain ⟨Ut⟩ := Formalism.L2.Col.MhlUnif.nonempty hsp
  have hxn : x.2 ≤ n := h ▸ hx2
  obtain ⟨R, hR⟩ := Formalism.L2.Col.mhs_exists_reps D.sp.cm Ut x.2 ∅ SG hov hST hSG hsp hxn
  let Off : Subgroup (Formalism.L2.Col.UAd D.sp.cm n) :=
    { carrier := {u | ∀ w, w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1}
      one_mem' := fun w _ => by rw [OneMemClass.coe_one, map_one]
      mul_mem' := fun {a b} ha hb w hw => by rw [Subgroup.coe_mul, map_mul, ha w hw, hb w hw, mul_one]
      inv_mem' := fun {a} ha w hw => by rw [InvMemClass.coe_inv, map_inv, ha w hw, inv_one] }
  have hKvOff : ∀ u, u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v → u ∈ Off := fun u hu => hu.1
  have hEtaOff : (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2) ∈ Off := fun w hw => Formalism.L2.Col.mhlEta_off D.sp.cm Ut x.2 w hw
  have hoffR : ∀ u ∈ R, u ∈ Off := fun u hu w hw => reps_off D.sp.cm Ut x.2 R hR u hu w hw
  let Lc : Subgroup (Bridge.Gf V) := Off.map Φ.toMonoidHom
  have hLc : ∀ u, Φ u ∈ Lc ↔ u ∈ Off := by
    intro u
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hisLoc : ∀ u, isLocEnv V pl ok x (Φ u) ↔ u ∈ Off := fun u =>
    (loc_iff_std V n h L' SG hsub pl ok x hoffP v hovP (Φ u) u (hΦ u)).1
  have hJ : ∀ u, u ∈ Off → (Φ u ∈ (levEnv V 1 L').J ↔ u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v) := fun u hu =>
    (loc_iff_std V n h L' SG hsub pl ok x hoffP v hovP (Φ u) u (hΦ u)).2 ((hisLoc u).2 hu)
  have hLoc' : ∀ l, isLocEnv V pl ok x l ↔ l ∈ Lc := by
    intro l
    have := hisLoc (Φ.symm l)
    rw [MulEquiv.apply_symm_apply] at this
    rw [this, ← hLc, MulEquiv.apply_symm_apply]
  have hKiff : ∀ u, Φ u ∈ (levEnv V 1 L').J ⊓ Lc ↔ u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v := by
    intro u
    constructor
    · rintro ⟨h1, h2⟩
      exact (hJ u ((hLc u).1 h2)).1 h1
    · intro hu
      exact ⟨(hJ u (hKvOff u hu)).2 hu, (hLc u).2 (hKvOff u hu)⟩
  have hmemR : ∀ a, a ∈ R.map Φ.toEquiv.toEmbedding → ∃ u ∈ R, a = Φ u := by
    intro a ha
    obtain ⟨u, hu, e⟩ := Finset.mem_map.1 ha
    exact ⟨u, hu, e.symm⟩
  have hDCl : Bridge.IsDC ((levEnv V 1 L').J ⊓ Lc) (Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2)) (R.map Φ.toEquiv.toEmbedding) :=
    isDC_map Φ _ _ hKiff (isDC_of_reps D.sp.cm Ut x.2 R hR)
  have hDC : Bridge.IsDC (levEnv V 1 L').J (Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2)) (R.map Φ.toEquiv.toEmbedding) := by
    refine GlobalTheory.RowPartsOrth.isDC_of_local (levEnv V 1 L').J Lc (Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2))
      (R.map Φ.toEquiv.toEmbedding) ((hLc _).2 hEtaOff) ?_ ?_ hDCl
    · intro j hj
      obtain ⟨j₁, hj₁, j₂, hj₂, hl₁, e, hc⟩ := lev_split V L' SG hsub pl ok x hoffP 1 Λ hβ j hj
      exact ⟨j₁, hj₁, j₂, hj₂, (hLoc' j₁).1 hl₁, e, fun l hl => hc l ((hLoc' l).2 hl)⟩
    · intro a ha
      obtain ⟨u, hu, rfl⟩ := hmemR a ha
      exact (hLc u).2 (hoffR u hu)
  refine ⟨Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2), R.map Φ.toEquiv.toEmbedding,
    eta_isT_std V n h pl ok x Λ hβ v Pb hcc hov Ut _ (hΦ _), ?_, hDC, ?_⟩
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := hmemR a ha
    exact (hisLoc u).2 (hoffR u hu)
  · intro g
    obtain ⟨w, rfl⟩ := Φ.surjective g
    exact bijOn_map_equiv Φ R _ _ _
      (reps_bij D.sp.cm Ut x.2 ∅ SG hov hST hSG hsp hxn R hR P hcc w _ (by rw [hΦ]))
      (fun u => by
        show Formalism.L2.Col.decoOf ∅ SG (castGL h.symm (Formalism.UG.bc (swapAE D) ((Φ w * Φ u : Bridge.Gf V) : GL (Fin V.rank) _))) = _
        rw [← map_mul Φ, hΦ])

end Gen

theorem gramX'_one (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem datX_sub (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) :
    ∀ PP, PP ∈ (L.datXt t).Pg ∨ PP ∈ (L.datXt t).Q → PP ∈ sgL X I U t := by
  intro PP hPP
  rcases hPP with hPP | hPP
  · rw [show (L.datXt t).Pg = L.Pg from rfl, hL.Pg] at hPP
    classical
    exact Finset.mem_union.2 (Or.inl hPP)
  · rw [show (L.datXt t).Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    classical
    exact Finset.mem_union.2 (Or.inr hPP)

theorem op_eq_of_bij (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (cX : CoefA X.toD7.sp.X') (t : TupU I U)
    {J : Subgroup (Bridge.Gf X.toD7.sp.X')} {χ : J →* ℂˣ}
    (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hA : Finset (Bridge.Gf X.toD7.sp.X'))
    (hB : ∀ g, Set.BijOn (fun a => RowAd.decoAd X I t (g * a)) (hA : Set (Bridge.Gf X.toD7.sp.X'))
      (Formalism.L2.Col.DecoSet.heckeSet x.1.1.1.asIdeal x.2 (RowAd.decoAd X I t g)))
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ)
    (hR : RowAd.ReadsDeco X I hX Xg tr cX t P)
    (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
    P.ext (((famR X I hX U Xg tr).A.heckeR t x f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
      ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V) =
      Bridge.dcOp hA (P.ext (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) := by
  classical
  obtain ⟨m, hm⟩ := hR
  funext g
  rw [hm, Bridge.dcOp]
  erw [heckeCSD_symm_apply]
  rw [Formalism.L2.Col.heckeFam]
  erw [Formalism.L2.Col.heckeD_op_apply]
  erw [map_sum]
  unfold Formalism.L2.Col.DecoPts.nb
  rw [Finset.sum_map]
  have hP0 := (x.1.1.1).ne_bot
  have hP1 := Formalism.L2.Col.conjIdeal_ne_bot hP0
  symm
  refine Finset.sum_nbij (fun a => RowAd.decoAd X I t (g * a)) ?_ ?_ ?_ ?_
  · intro a ha
    exact (Formalism.L2.Col.DecoSet.mem_heckeNb hP0 hP1 _ _ _).2 ((hB g).mapsTo ha)
  · intro a ha b hb hab
    exact (hB g).injOn ha hb hab
  · intro d hd
    have hd' := (Formalism.L2.Col.DecoSet.mem_heckeNb hP0 hP1 _ _ _).1 hd
    obtain ⟨a, ha, rfl⟩ := (hB g).surjOn hd'
    exact ⟨a, ha, rfl⟩
  · intro a _
    rw [hm]
    rfl

theorem hecke_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') P ((famR X I hX U Xg tr).A.heckeR t) (fun i => 1 ≤ i.2 ∧ i.2 ≤ X.toD7.sp.X'.rank)
        (isTEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t))
        (isLocEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t))) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hTie hinner t P hR
  have hβ := hL.is.βX
  rw [hL.beta.2] at hβ
  have key : ∀ x : (famR X I hX U Xg tr).A.ok t × ℕ, 1 ≤ x.2 ∧ x.2 ≤ X.toD7.sp.X'.rank →
      ∃ (hx : Bridge.Gf X.toD7.sp.X') (hA : Finset (Bridge.Gf X.toD7.sp.X')),
        isTEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x hx ∧
        (∀ a ∈ hA, isLocEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x a) ∧
        Bridge.IsDC (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J hx hA ∧
        ∀ f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms,
          P.ext (((famR X I hX U Xg tr).A.heckeR t x f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
            ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V) =
          Bridge.dcOp hA (P.ext (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) := by
    intro x hx
    obtain ⟨hx', hA, h1, h2, h3, h4⟩ := loc_data X.toD7.sp.X' (X.B.R.N X.B.R.m - 1) (RowAd.rank_X' X).symm (L.datXt t) (sgL X I U t)
      (datX_sub X I U L hL t) (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x x.1.2
      (gramX'_one X I hI) L.ΛX hβ hx.2
    refine ⟨hx', hA, h1, h2, ?_, fun f => op_eq_of_bij X I hX U Xg tr cX t x hA h4 P hR f⟩
    rw [hL.beta.2]
    exact h3
  choose! hxf hAf hxok hAloc hDC hop using key
  exact ⟨⟨hxf, hAf, hxok, hAloc, fun x _ j hj => chi_loc X.toD7.sp.X' (L.datXt t) (sgL X I U t) (datX_sub X I U L hL t)
    (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x x.1.2 L.βX j hj, hDC, hop⟩⟩

end GlobalTheory.Mem.R3.RowHk
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitHecke_rows_eq_doubleCoset_operators : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') P ((famR X I hX U Xg tr).A.heckeR t) (fun i => 1 ≤ i.2 ∧ i.2 ≤ X.toD7.sp.X'.rank)
        (isTEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t))
        (isLocEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t))) := by
  atlas_forward_decl GlobalTheory.Mem.R3.RowHk.hecke_tie
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.RowAd.Inert

theorem conj_heckeFamI_apply {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (C : Formalism.L2.Col.CoefPk X n (Formalism.L2.Col.DecoSet X.E n ST SG)) (Λ : Formalism.L2.Col.LevFam X.E X.K n SG)
    (hS : (Formalism.L2.Col.formGSD C Λ).Ok) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Formalism.L2.Col.LevOffI ST SG S0 × List ℕ)
    (f : ((Formalism.L2.Col.formGSD C Λ).toCSD hS).Forms) (d : Formalism.L2.Col.DecoSet X.E n ST SG) :
    ((((Formalism.L2.Col.formGSD C Λ).res hS).symm ((((Formalism.L2.Col.formGSD C Λ).res hS).conj
      (Formalism.L2.Col.heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y)) f) : (Formalism.L2.Col.formGSD C Λ).EqFun) :
        Formalism.L2.Col.DecoSet X.E n ST SG → C.V) d =
      ∑ e ∈ d.inertNb y.1.1.asIdeal y.2, ((((Formalism.L2.Col.formGSD C Λ).res hS).symm f : (Formalism.L2.Col.formGSD C Λ).EqFun) :
        Formalism.L2.Col.DecoSet X.E n ST SG → C.V) e := by
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [Formalism.L2.Col.heckeFamI_formPts_apply]
  rfl

theorem colIn3_heckeRI_apply {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R)
    (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Formalism.L2.Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
    (τ : TupF TU) (q : ↑((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).okI τ) × List ℕ)
    (f : ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.MtildeCSD τ).Forms) (d : (Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).D) :
    (((Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).res (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX)).symm
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).heckeRI τ q f)).1 d =
      ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb q.1.1.1.asIdeal q.2 d,
        (((Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).res (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX)).symm f).1 e :=
  conj_heckeFamI_apply _ _ (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX) S0 (offSubI.lev q.1, q.2) f d

theorem opEq (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U) (cX : CoefA X.toD7.sp.X') {J : Subgroup (Bridge.Gf X.toD7.sp.X')} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ)
    (hP : ReadsDeco X I hX Xg tr cX t P)
    (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (R : Finset (Bridge.Gf X.toD7.sp.X'))
    (hN : ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → M) (g : Bridge.Gf X.toD7.sp.X'),
        ∑ a ∈ R, ψ (decoAd X I t (g * a)) =
          ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb (q.1.1 : PlI X.B px).1.asIdeal q.2 (decoAd X I t g : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)), ψ e)
    (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
    P.ext ((((famR X I hX U Xg tr).heckeRI t q f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
        ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) =
      Bridge.dcOp R (P.ext (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) := by
  obtain ⟨m, hm⟩ := hP
  funext g
  have e1 := hm ((famR X I hX U Xg tr).heckeRI t q f) g
  have e2 := colIn3_heckeRI_apply (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I U)
    Xg ∅ (xiValOf I) tr t q f (decoAd X I t g)
  have e3 := hN _ (fun e => m ((((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 e)) g
  refine e1.trans ?_
  refine (congrArg m e2).trans ?_
  refine (map_sum m _ _).trans ?_
  refine e3.symm.trans ?_
  exact (Finset.sum_congr rfl (fun a _ => hm f (g * a))).symm

theorem chi_eq_one {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (Q : Pl D.host.E)
    (hQc : Formalism.L2.Col.conjPrime₂ Q = Q) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q) (j : (levEnv V β L).J)
    (hj : IsLocElt V Q (j : Bridge.Gf V)) : (levEnv V β L).χ j = 1 := by
  have e : (levEnv V β L).χ j = Formalism.L2.DIV.levFn β (flag1L L) (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) := rfl
  have hm : Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L) := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hloc := LiftInertChi.locAt_of_isLocElt V _ _ hj
  have hconj : Formalism.DivisionValues.conjPl Q = Q := GlobalTheory.InertNbr.conjPl_eq_of_conjP hQc
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q →
      Formalism.L2.DIV.redFn β PP (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) = 1 := fun PP hPP =>
    LiftInertChi.redFn_eq_one_of_locAt _ _ hSt _ hloc PP (fun hu => by
      rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h | h
      · exact hoff PP hPP h
      · exact hoff PP hPP (h.trans hconj))
  have hr1 : Formalism.L2.DIV.rTup β (flag1L L) (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1
    rw [hred PP.1 (Or.inl PP.2)]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  rw [e]
  unfold Formalism.L2.DIV.levFn
  rw [hr1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hPP
    rw [hred PP (Or.inr hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hPP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hred PP (Or.inl hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

theorem gram_eq_one (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem off_level (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) {U : Set I.ι}
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hL : LevOf X I U L) (t : TupU I U) (Q : PlI X.B px) :
    ∀ PP, PP ∈ (L.datXt t).Pg ∨ PP ∈ (L.datXt t).Q → PP ≠ Q.1 := by
  rintro PP (h | h) rfl
  · have h' : Q.1 ∈ L.Pg := h
    rw [hL.Pg] at h'
    exact Q.2.2.2 (Or.inr h')
  · refine (hL.is.Q_pl t _ h).2 _ h ?_
    exact GlobalTheory.InertNbr.isConjPl_self (D := X.toD7) Q.2.1

theorem inert_neighbours (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) {U : Set I.ι}
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hI : I.Ok) (hL : LevOf X I U L) (t : TupU I U) (Q : PlI X.B px)
    (hQ : Q.1 ∉ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (s : List ℕ) (hs : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank s) :
    ∃ (x : Bridge.Gf X.toD7.sp.X') (A : Finset (Bridge.Gf X.toD7.sp.X')), IsLabElt X.toD7.sp.X' Q.1 (labIn X.toD7.sp.X'.rank s) x ∧
      (∀ a ∈ A, IsLocElt X.toD7.sp.X' Q.1 a) ∧ Bridge.IsDC (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J x A ∧
      ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → M) (g : Bridge.Gf X.toD7.sp.X'),
        ∑ a ∈ A, ψ (decoAd X I t (g * a)) =
          ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb Q.1.asIdeal s (decoAd X I t g : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)), ψ e := by
  obtain ⟨m, hm⟩ := hL.is.βX
  rw [one_pow] at hm
  have hβ := hL.beta.2
  rw [hβ] at hm
  have key := GlobalTheory.InertNbr.exists_hecke X.toD7.sp.X' (n := X.B.R.N X.B.R.m - 1) (rank_X' X).symm L.ΛX (L.datXt t) hm Q.1 Q.2.1
    (off_level X I hL t Q) hQ 1 1 (one_mem _)
    (fun x => by
      rw [gram_eq_one X I hI, one_mul, inv_one, mul_one]
      exact (LiftBrg.castGL_mem_UA_one X.toD7.sp.cm (rank_X' X).symm x).symm)
    (one_mem _) (one_mem _) s hs
  simp only [inv_one, one_mul, mul_one] at key
  rw [hβ]
  exact key

theorem exists_inertTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') P ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1) := by
  intro X px I hX U Xg tr L eG hI _ hL _ cX gramR c0R _ _ _ _ t P hP
  classical
  have hN := fun (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2) =>
    inert_neighbours X I hI hL t (q.1.1 : PlI X.B px) (fun h => q.1.2 (Or.inr h)) q.2 hq
  exact ⟨{
    hx := fun q => if hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2 then (hN q hq).choose else 1
    hA := fun q => if hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2 then (hN q hq).choose_spec.choose else ∅
    hx_ok := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.1
    hA_loc := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.1
    chi_loc := fun q _ j hj => chi_eq_one X.toD7.sp.X' L.βX (L.datXt t) (q.1.1 : PlI X.B px).1 (q.1.1 : PlI X.B px).2.1
      (off_level X I hL t (q.1.1 : PlI X.B px)) j hj
    hDC := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.2.1
    op_eq := fun q hq f => by
      simp only [dif_pos hq]
      exact opEq X I hX U Xg tr t cX P hP q _ (hN q hq).choose_spec.choose_spec.2.2.2 f }⟩

end GlobalTheory.Mem.R3.RowAd.Inert
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowsRead

theorem decoPt_eq_decoAd (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) {U : Set I.ι} (t : TupU I U)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hβ : L.βX = 1) (hc : CMData X.B.fields.F X.B.fields.E)
    (h : Bridge.Gf X.toD7.sp.X') (x : Formalism.L2.Col.UAd hc (X.B.R.N X.B.R.m - 1))
    (hM : MatEq (matIn X.toD7.sp.X' L.βX h) (show GL (Fin (X.B.R.N X.B.R.m - 1)) (Lev.EAf X.toD7) from x.1)) :
    Formalism.L2.Col.decoPt hc (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (QuotientGroup.mk x) =
      GlobalTheory.Mem.R3.RowAd.decoAd X I t h := by
  have hx : x.1 = GlobalTheory.Mem.R3.RowAd.ptE X h := by
    ext i j
    have := hM.2 (Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm i) (Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm j) i j rfl rfl
    rw [hβ, matIn, mul_one] at this
    exact this.symm
  rw [Formalism.L2.Col.decoPt_mk, hx]
  rfl

theorem exists_matEq_ptE (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) {U : Set I.ι}
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hβ : L.βX = 1) :
    ∃ hc : CMData X.B.fields.F X.B.fields.E, ∀ h : Bridge.Gf X.toD7.sp.X', ∃ x : Formalism.L2.Col.UAd hc (X.B.R.N X.B.R.m - 1),
      MatEq (matIn X.toD7.sp.X' L.βX h) (show GL (Fin (X.B.R.N X.B.R.m - 1)) (Lev.EAf X.toD7) from x.1) := by
  refine ⟨X.toD7.sp.cm, fun h => ⟨⟨GlobalTheory.Mem.R3.RowAd.ptE X h, GlobalTheory.Mem.R3.RowDeco.ptE_mem_UAd X I hI h⟩, GlobalTheory.Mem.R3.RowAd.rank_X' X, ?_⟩⟩
  intro i j i' j' hi hj
  obtain rfl : i = Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm i' := Fin.ext hi
  obtain rfl : j = Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm j' := Fin.ext hj
  rw [hβ, matIn, mul_one]
  rfl

set_option maxHeartbeats 4000000 in

theorem exists_rowSide : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ s : ∀ t, Seed.RowSideT (famR X I hX U Xg tr) L cX (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) t, (∀ t,       (∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
        eG ((s t).act_tie.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∧
      Bridge.CoefTie X.toD7.sp.X' cX.coef (s t).pres (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
        (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') (s t).pres ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1)) ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => (s t).pres.extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin hβ _
  obtain ⟨c, -, hli, -, -, hcI, hP⟩ := GlobalTheory.Mem.R3.RowStd.exists_std_wtCast X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin hβ
  choose P hPr hCo using hP
  have hRd : ∀ t, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t (P t) := fun t => ⟨c, hPr t⟩
  choose a ha using fun t => GlobalTheory.T.rowFormsFiniteGroupAction_eq_flagLevelRightTranslation X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)
  refine ⟨fun t => { pres := P t, act_tie := a t, hecke := (GlobalTheory.T.splitHecke_rows_eq_doubleCoset_operators X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)).some },
    fun t => ⟨ha t, hCo t, GlobalTheory.Mem.R3.RowAd.Inert.exists_inertTie X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)⟩, c, hcI, ?_, hli, exists_matEq_ptE X I hI L hβ⟩
  intro hc t φ h x hM
  refine (hPr t _ h).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (fun d => c (φ.2.1 d)) (decoPt_eq_decoAd X I t L hβ hc h x hM).symm

end GlobalTheory.Mem.R3.RowsRead
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowForms_adelic_decoratedLattices : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ s : ∀ t, Seed.RowSideT (famR X I hX U Xg tr) L cX (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) t, (∀ t,       (∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
        eG ((s t).act_tie.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∧
      Bridge.CoefTie X.toD7.sp.X' cX.coef (s t).pres (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
        (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') (s t).pres ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1)) ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => (s t).pres.extL φ)  := by
  atlas_forward_decl GlobalTheory.Mem.R3.RowsRead.exists_rowSide
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem famR_places : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    (∀ t P, P ∈ (famR X I hX U Xg tr).A.ok t ↔
      Bridge.SplitOff (P.1 : Pl X.toD7.host.E) ((L.Pg : Set (Pl X.toD7.host.E)) ∪ (L.Q t : Set (Pl X.toD7.host.E)))) ∧
    (∀ PP, Bridge.SplitOff PP (L.Pg : Set (Pl X.toD7.host.E)) → ∃ P : PlS X.B px, (P.1 : Pl X.toD7.host.E) = PP) ∧
    Bridge.InertTie (famR X I hX U Xg tr) (fun Q : PlI X.B px => (Q.1 : Pl X.toD7.host.E)) (L.Pg : Set (Pl X.toD7.host.E)) L.Q ∧
    (∀ PP, Bridge.InertOff PP (L.Pg : Set (Pl X.toD7.host.E)) → ∃ Q : PlI X.B px, (Q.1 : Pl X.toD7.host.E) = PP) := by
  intro X px I hX U Xg tr L eG _ _ hL _
  have hS : ∀ t : TupU I U, ((∅ : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((∅ : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) :
        Set (HeightOneSpectrum (𝓞 X.B.fields.E)))) =
      (L.Pg : Set (Pl X.toD7.host.E)) ∪ (L.Q t : Set (Pl X.toD7.host.E)) := by
    intro t
    rw [hL.Pg, hL.Q t]
    have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
      show Formalism.L2.Col.QE I.sel (I.tup (ixOf I U t) : Chr X.B.fields.F X.B.fields.E X.B.fields.K) = _
      rw [tup_ixOf I t]
    rw [e]
    simp [Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG]
    rfl
  have hS0 : ((∅ : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((∅ : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      (((X.B.primes px).vGs : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E)))) =
      (L.Pg : Set (Pl X.toD7.host.E)) := by
    rw [hL.Pg]
    simp
    rfl
  refine ⟨fun t P => ?_, fun PP hPP => ?_, ⟨Subtype.val_injective, fun t Q => ?_⟩, fun PP hPP => ?_⟩
  · show P.1 ∈ Formalism.L2.DIV.offSet ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ ↔ _
    unfold Formalism.L2.DIV.offSet Formalism.IndefR.Bridge.SplitOff
    rw [Set.mem_setOf_eq, hS t]
    exact Iff.rfl
  · obtain ⟨h1, h2, h3⟩ := hPP
    refine ⟨⟨PP, h1, ?_, fun Q hQ => h3 Q ?_⟩, rfl⟩
    · rw [hS0]; exact h2
    · rw [← hS0]; exact hQ
  · show Q.1 ∉ _ ↔ _
    unfold Formalism.IndefR.Bridge.InertOff
    rw [hS t]
    have hc : ∀ P : Pl X.toD7.host.E, Formalism.L2.Col.conjPrime₂ P = P →
        Formalism.HermitianLatticesTheory.conjIdeal (K := X.toD7.host.E) P.asIdeal = P.asIdeal := fun P hP => by
      rw [Formalism.L2.Col.conjIdeal_asIdeal, hP]
    exact ⟨fun h => ⟨hc Q.1 Q.2.1, h⟩, fun h => h.2⟩
  · obtain ⟨h1, h2⟩ := hPP
    have hc : Formalism.L2.Col.conjPrime₂ PP = PP := HeightOneSpectrum.ext (by rw [← Formalism.L2.Col.conjIdeal_asIdeal]; exact h1)
    have hin : ∃ x : 𝓞 X.toD7.host.E, Formalism.L2.Col.cO X.toD7.host.E x - x ∉ PP.asIdeal := by
      obtain ⟨θ, t, ht, hθ⟩ := X.toD7.sp.cm.cmUnram.2.2 PP.asIdeal PP.isMaximal
      have e : Formalism.L2.Col.cO X.toD7.host.E θ = t := RingOfIntegers.ext ht.symm
      refine ⟨θ, fun h => hθ ?_⟩
      rw [e] at h
      rw [← neg_sub]
      exact PP.asIdeal.neg_mem h
    refine ⟨⟨PP, hc, hin, ?_⟩, rfl⟩
    rw [hS0]; exact h2

end GlobalTheory.Mem.R3

end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Cls

theorem coeffField_rootsOfUnity_typePrimes_hermitianStages : ∀ X : Stages, GlobalTheory.Core.Cls.RootsG X.toD7 := by
  intro X i
  have hp : Nat.Prime (X.B.host.g i) := X.B.host.g_prime i
  obtain ⟨z, -, hz⟩ := X.B.roots_Ks (X.B.host.g i * (X.B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : X.B.host.g i * (X.B.host.g i - 1) ≠ 0 :=
    mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot z (X.B.host.g i * (X.B.host.g i - 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := X.B.embLL) ?_ X.B.embLL.injective
    rw [hz]
    exact_mod_cast Complex.isPrimitiveRoot_exp _ hne
  have hpos : 0 < X.B.host.g i * (X.B.host.g i - 1) := Nat.pos_of_ne_zero hne
  exact ⟨⟨z ^ (X.B.host.g i - 1), hprim.pow hpos (mul_comm _ _)⟩, ⟨z ^ X.B.host.g i, hprim.pow hpos rfl⟩⟩

end GlobalTheory.Core.Cls
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.Brg

open Formalism.L2.Col in

theorem conjIdeal_eq_conjP {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = (conjPrime₂ P).asIdeal := by
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro r ⟨s, hs, e⟩
    show r ∈ (conjPrime₂ P).asIdeal
    rw [mem_conjP]
    have : cO E r = s := RingOfIntegers.ext (by
      show star (r : E) = (s : E)
      have e' : (r : E) = star (s : E) := e
      rw [e', star_star])
    rw [this]; exact hs
  · intro r hr
    rw [mem_conjP] at hr
    refine Ideal.subset_span ⟨cO E r, hr, ?_⟩
    show (r : E) = star (star (r : E))
    rw [star_star]

open Formalism.L2.Col in

theorem g_notMem_of_levOff {X : Fields} {Pr : Primes X} (hPr : Pr.Ok)
    (P : letI := X.starE; LevOff (E := X.E) ∅ Pr.vGs ∅) (k : Fin 2) :
    ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := by
  classical
  letI := X.starE
  intro hk
  have h0 : X.conjO (Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  have hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ Pr.vGs := fun Q hQ => by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ]
  rw [← hPr.piG_norm k] at hk
  rcases P.1.isPrime.mem_or_mem hk with h | h
  · have hc : conjPrime₂ P.1 ∈ Pr.vG k := by
      refine (mem_divs h0 _).2 ?_
      rw [mem_conjP]
      show cO X.E (X.conjO (Pr.piG k)) ∈ P.1.asIdeal
      exact (cO_cO (Pr.piG k)).symm ▸ h
    exact P.2.2.2 (conjPrime₂ P.1) (Or.inr (hsub _ hc)) (conjIdeal_eq_conjP P.1).symm
  · exact P.2.2.1 (Or.inr (hsub _ ((mem_divs h0 _).2 h)))

end GlobalTheory.Mem.R3.Brg

namespace GlobalTheory.Mem.R3.Brg

theorem muVal_eq {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hI : I.Ok) (hV : ValsIn I) (i : Fin B.R.m) {a : I.ι}
    {τ : Tup B.fields.F B.fields.E B.fields.K I.S} (hτ : I.tup a = τ) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (hg : ∀ k, ((B.host.g k : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal) (hu : (I.xi a).UnrAt P) :
    B.embLL ((I.Ch.muVal i P * xiValOf I τ P : B.LLˣ) : B.LL) = (((I.C.mu0 i * I.xi a).val P : ℂˣ) : ℂ) := by
  subst hτ
  rw [Formalism.L2.Host.HChar.val_mul, Units.val_mul, Units.val_mul, map_mul, hV.embLL_xiValOf a P hu]
  congr 1
  exact hI.ch_tied.muVal i P hg

theorem values : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    (∀ (i : Fin X.toD7.R.m) t, ∀ P ∈ (famR X I hX U Xg tr).A.ok t,
      X.toD7.what₂.embLL ((famR X I hX U Xg tr).A.muVal i t P : X.toD7.what₂.LL) =
        (((L.C.mu0 i * L.xiH t).val (P.1 : Pl X.toD7.host.E) : ℂˣ) : ℂ)) ∧
    (∀ P ∈ (famR X I hX U Xg tr).A.ok (famR X I hX U Xg tr).A.μ0,
      X.toD7.what₂.embLL ((famR X I hX U Xg tr).A.etaVal P : X.toD7.what₂.LL) =
        Formalism.L2.Host.etaAlg X.toD7.host L.C.eta (P.1 : Pl X.toD7.host.E)) ∧
    ∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → ∃ z : X.toD7.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP)) := by
  intro X px I hX U Xg tr L eG hI hV hL _
  classical
  letI := X.B.fields.starE
  have hPr : (X.B.primes px).Ok := (GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).2.1
  refine ⟨fun i t P hP => ?_, fun P _ => ?_, fun t PP hPP => ?_⟩
  · have hP' : P.1 ∈ Formalism.L2.DIV.offSet (E := X.B.fields.E) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ := hP
    have hQ : ∀ PP, PP ∈ I.Q (ixOf I U t) → PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := fun PP h =>
      Finset.mem_union_right _ (by rw [← tup_ixOf I t]; exact h)
    have hg : ∀ k, ((X.B.host.g k : ℕ) : 𝓞 X.B.fields.E) ∉ P.1.asIdeal := g_notMem_of_levOff hPr P
    have hunr : (I.xi (ixOf I U t)).UnrAt P.1 := by
      by_contra hn
      rw [← hL.xiH t] at hn
      rcases (hL.is.Q_ram t P.1).1 hn with h | ⟨PP', h, hc⟩
      · rw [hL.Q t] at h
        exact hP'.2.1 (Or.inr (Finset.mem_coe.2 (hQ _ h)))
      · rw [hL.Q t] at h
        have hle : PP'.asIdeal ≤ (Formalism.L2.Col.conjPrime₂ P.1).asIdeal := fun c hcm => by
          obtain ⟨c', hc', e⟩ := hc c hcm
          refine (Formalism.L2.Col.mem_conjP (E := X.B.fields.E) P.1 c).2 ?_
          have : Formalism.L2.Col.cO X.B.fields.E c = c' := RingOfIntegers.ext e.symm
          rw [this]; exact hc'
        have heq : PP'.asIdeal = (Formalism.L2.Col.conjPrime₂ P.1).asIdeal :=
          PP'.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P.1).isPrime.ne_top hle
        exact hP'.2.2 PP' (Or.inr (Finset.mem_coe.2 (hQ _ h))) (heq.trans (conjIdeal_eq_conjP P.1).symm)
    rw [hL.C, hL.xiH t]
    exact muVal_eq I hI hV i (tup_ixOf I t) P.1 hg hunr
  · show X.B.embLL (I.Ch.etaVal P.1 : X.B.LL) = _
    rw [hL.C]
    exact hI.ch_tied.etaVal P.1
  · rcases hPP with h | h
    · rw [hL.Pg] at h
      obtain ⟨k, hk⟩ : ∃ k, PP ∈ (X.B.primes px).vG k := by
        rcases Finset.mem_union.1 h with h | h
        exacts [⟨0, h⟩, ⟨1, h⟩]
      have hn : Ideal.absNorm PP.asIdeal = X.B.host.g k := hPr.vG_norm k PP hk
      have hcard : Nat.card (kP PP) = X.B.host.g k := by
        rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hcard]
      exact (GlobalTheory.Core.Cls.coeffField_rootsOfUnity_typePrimes_hermitianStages X k).1
    · rw [hL.Q t] at h
      exact hV.2 _ PP h

end GlobalTheory.Mem.R3.Brg
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.BrgRead

set_option maxHeartbeats 1000000

theorem embLL_labLL_eq {D : D7} (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem gram_V (X : Stages) (h : DiagSpaces X.toD7.sp) (i : Fin X.toD7.R.m) : (Vc X.toD7 i).gram = 1 := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  have h1 := hV ((i : ℕ) + 1)
  have hn : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  rw [hn] at h1
  change (X.toD7.sp.V ((i : ℕ) + 1)).gram = 1
  rw [h1]
  refine Matrix.ext fun a b => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ a b).trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem isDualPair_smul {D : D7} {θ : InfFam D} {MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)} {cX : CoefA D.sp.X'}
    {prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ} (h : IsDualPair θ MX cX prX) {c : ℂ} (hc : c ≠ 0) :
    IsDualPair θ MX cX (c • prX) := by
  refine ⟨smul_ne_zero hc h.1, fun τ g hg w v u hu => ?_⟩
  simp only [LinearMap.smul_apply]
  rw [h.2 τ g hg w v u hu]

theorem exists_coefData : ∀ (D : D7), Seed.VPos D → ∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
  ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ)
    (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] cX.W)
    (c0L : ∀ i : Fin D.R.m, VV D.what₂.LL (fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) →ₛₗ[D.what₂.embLL] (cV i).W),
    cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧
    (gramR = D.sp.X'.gram ∨ gramR = -D.sp.X'.gram) ∧
    Bridge.CoefMapTie D.sp.X' cX.coef c0R (rhoV (labLL D) _) ∧
    (∀ i, Bridge.CoefMapTie (Vc D i) (cV i).coef (c0L i) (rhoVr (labLL D) _)) ∧
    (∀ x y, inner ℂ (c0R x) (c0R y) = D.what₂.embLL (pairV (labLL D) _ gramR x y)) ∧
    ∀ i x y, inner ℂ (c0L i x) (c0L i y) = D.what₂.embLL (pairVr (labLL D) _
      (if D.sp.Vneg ((i : ℕ) + 1) then -(Vc D i).gram else (Vc D i).gram) x y) := by
  intro D hV θ hθ MX
  obtain ⟨cX, prX, c0R, gramR, hcX, hdual, hg, hmap, hin⟩ := GlobalTheory.CoefSpace.exists_coef_dualPair D θ MX hθ
  have hL := fun i => GlobalTheory.CoefModel.exists_coef_lift D i (hV i)
  choose cV c0L hcV hmapL hinL using hL
  obtain ⟨c, hc, hiso⟩ := GlobalTheory.PrIsoScale.exists_smul_prIso D θ MX cX prX hθ hcX hdual
  exact ⟨cX, cV, c • prX, gramR, c0R, c0L, hcX, hcV, isDualPair_smul hdual hc, hiso, hg, hmap, hmapL, hin, hinL⟩
theorem hecke_degrees : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px),
    (∀ t P, (famR X I hX U Xg tr).A.heckeR t (P, 0) = 1 ∧
      ∀ k, X.toD7.sp.X'.rank < k → (famR X I hX U Xg tr).A.heckeR t (P, k) = 0) ∧
    (∀ i t P, (famR X I hX U Xg tr).A.heckeL i t (P, 0) = 1 ∧
      ∀ k, (Vc X.toD7 i).rank < k → (famR X I hX U Xg tr).A.heckeL i t (P, k) = 0) := by
  intro X px I hX U Xg tr
  have hk3 := X.B.R.m_add_three_le_k
  refine ⟨fun t P => ⟨heckeCSD_zero _ _ _ _ _ _, fun k hk => ?_⟩, fun i t P => ⟨heckeCSD_zero _ _ _ _ _ _, fun k hk => ?_⟩⟩
  · refine (congrArg _ (Formalism.L2.Col.heckeFam_eq_zero_of_lt _ _ _ ?_)).trans (LinearEquiv.map_zero _)
    have e := X.toD7.sp.X'_rank
    change X.toD7.sp.X'.rank < k at hk
    rw [e] at hk
    change _ < k
    unfold Ranks.rankX' at hk
    unfold Ranks.N
    simp only [Ranks.r] at hk ⊢
    change X.B.R.k + X.B.R.m - 1 + X.B.R.m * X.B.R.t < k at hk
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · refine (congrArg _ (Formalism.L2.Col.heckeFam_eq_zero_of_lt _ _ _ ?_)).trans (LinearEquiv.map_zero _)
    have e := X.toD7.sp.V_rank _ (by omega) i.2
    change (X.toD7.sp.V ((i : ℕ) + 1)).rank < k at hk
    rw [e] at hk
    exact hk

theorem exists_brgL : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∃ (cX : CoefA X.toD7.sp.X') (cV : ∀ i, CoefA (Vc X.toD7 i)) (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ ∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ := by
  intro X px I hX U Xg tr L eG hI hV hL hG hβX hβV hsX hsV θ hθ MX
  have hVP : Seed.VPos X.toD7 := fun i => X.B.V_posDef _ (by omega) i.2
  obtain ⟨cX, cV, prX, gramR, c0R, c0L, hcX, hcV, hdual, hiso, hgram, hmapR, hmapL, hinR, hinL⟩ :=
    exists_coefData X.toD7 hVP θ hθ MX
  have hR := GlobalTheory.T.exists_rowForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hmapR hinR hβX hsX
  have hLf := fun i => GlobalTheory.T.exists_liftForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cV i (c0L i) (hcV i) (hmapL i) (hinL i) (hβV i)
    (gram_V X hI.spaces i) (hsV i)
  obtain ⟨sR, hsR, hstR⟩ := hR
  choose sL hsL hstL using hLf
  obtain ⟨hok, hon, hit, hion⟩ := GlobalTheory.Mem.R3.famR_places X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hmu, heta, hroots⟩ := GlobalTheory.Mem.R3.Brg.values X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hdR, hdL⟩ := hecke_degrees X px I hX U Xg tr
  have hrk : X.toD7.sp.X'.rank = (famR X I hX U Xg tr).A.r + X.toD7.R.m * (famR X I hX U Xg tr).A.t := X.toD7.sp.X'_rank
  have hrkL : ∀ i : Fin X.toD7.R.m, (Vc X.toD7 i).rank = (famR X I hX U Xg tr).A.r + (famR X I hX U Xg tr).A.t :=
    fun i => X.toD7.sp.V_rank _ (by omega) i.2
  let B : Seed.BType (famR X I hX U Xg tr) L cX cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) :=
    { R := sR, L := fun i t => sL i t, rankR := hrk, rankL := hrkL }
  classical
  refine ⟨cX, cV, fun P => P.1, L.Pg, B, fun Q => Q.1, L.Pg.image (fun PP => PP.under (𝓞 X.toD7.host.F)), prX,
    hcX, hcV, hdual, hiso, ?_, hstR, hstL⟩
  exact
    { red_R := fun t q => (hsR t).1 q
      red_L := fun i t q => (hsL i t).1 q
      tie := ⟨gramR, c0R, c0L,
        { ranks := ⟨rfl, rfl, rfl⟩
          v0 := rfl
          tauL_ok := fun τ => RingHom.ext fun x => embLL_labLL_eq τ x
          pl_inj := fun a b h => Subtype.ext h
          q := fun P => rfl
          S_fin := Set.toFinite _
          ok := hok
          gramR_eq := hgram
          mapR := hmapR
          mapL := hmapL
          coefR := fun t => (hsR t).2.1
          coefL := fun i t => (hsL i t).2.1 }⟩
      sb := rfl
      roots := hroots
      pl_onto := hon
      degR := hdR
      degL := hdL
      muVal := hmu
      etaVal := heta
      in_tie := hit
      in_onto := hion
      in_R := fun t => (hsR t).2.2
      in_L := fun i t => (hsL i t).2.2
      in_SF := fun v => by
        simp only [Finset.mem_image]
        refine exists_congr fun PP => and_congr_right fun _ => ?_
        rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.under_asIdeal, Ideal.under_def] }

end GlobalTheory.Mem.R3.BrgRead

end
end
