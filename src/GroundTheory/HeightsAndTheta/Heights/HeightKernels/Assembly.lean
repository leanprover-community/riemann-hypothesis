import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Imports
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.RestAssembly
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeightNE
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsConjInvariant
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLeRoot
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootDivSuppEmpty
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootAnchorNonzero
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootPointConj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootPointsFinite
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPtsIntegralZeroLowerNE
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootHeightNE
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeBasisExists
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEmbBijective
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineSemipositive
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.IsArithVarBotDualBlocksUnit
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCurvePoint
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointArInt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsPointVertRSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPointLineDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PTelescope
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSubLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopBasisChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualGeomDegCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassGeomDegChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopMetricChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopLatticeChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStdBaseChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassLinesProj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOnPlane
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOfPlane
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdMassAt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegPos

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootArithmeticVariety

theorem isIntegral_of_pow_eq_one {x : ℂ} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by
    simp [Polynomial.eval₂_sub, h]⟩

theorem isIntegral_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ a b, IsIntegral ℤ (M a b)) :
    IsIntegral ℤ M.det := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem (integralClosure ℤ ℂ) fun σ _ => ?_
  rw [Units.smul_def]
  refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun i _ => hM (σ i) i) _

theorem isIntegral_onePipe {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, IsIntegral ℤ (Z a b))
    (a : Fin j) (b : Fin (j + m)) : IsIntegral ℤ (onePipe Z a b) := by
  simp only [onePipe, Matrix.of_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) b
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    exact hZ a i

theorem isIntegral_rootCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine isIntegral_det _ fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id]
  refine isIntegral_onePipe _ (fun a b => ?_) _ _
  obtain ⟨k, hk, h⟩ := hζ p.1 a b
  exact isIntegral_of_pow_eq_one hk h

end RootArithmeticVariety

open RootArithmeticVariety in

theorem RootArithVar.proof (h : CoordConeArithVar.Statement) : RootArithVar.Statement := by
  intro f j m ζ hf hζ
  have hK : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have := h (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) (fun _ => plAnchor j m) 0 Fin.elim0 hK
    (fun k => by simp [rootCoord, anchor_minor]) (algebraicIndependent_empty_type)
    (fun i => Fin.elim0 i) ?_
  · simpa [rootPointIdeal] using this
  · rintro r ⟨p, rfl⟩
    have h1 : IsIntegral ℚ (rootCoord ζ p / rootCoord ζ ⟨p.1, plAnchor j m⟩) := by
      simp only [rootCoord, anchor_minor, div_one]
      exact (isIntegral_rootCoord ζ hζ p).tower_top
    exact (h1.tower_top (A := IntermediateField.adjoin ℚ (Set.range (Fin.elim0 : Fin 0 → ℂ)))).isAlgebraic

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem FsLineSemipositive.proof (h₁ : FsLineSmooth.Statement) (h₂ : FsLineLevi.Statement) :
    FsLineSemipositive.Statement := by
  intro K _ ι _ P
  exact ⟨h₁ K ι, fun z hz w _ => h₂ K ι z w hz.1⟩

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace NefOfNonnegAlt

theorem geoNum_zero_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 V a := by
  unfold geoNum
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem geoNum_one_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : 0 ≤ geoNum 1 V (fun _ => a) := by
  unfold geoNum
  split_ifs
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (ha k) ?_
    refine finsum_nonneg fun W => finsum_nonneg fun _ => ?_
    exact mul_nonneg (Int.natCast_nonneg _) (geoNum_zero_nonneg _ _)
  · exact le_rfl

end NefOfNonnegAlt

theorem NefOfNonneg.proof : NefOfNonneg.Statement := by
  intro K _ ι _ P a ha W _ _ _ _
  exact NefOfNonnegAlt.geoNum_one_nonneg W a ha

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootLogNormBoundAlt

theorem norm_block_le (h₃ : PlueckerKernel.Statement) (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) :
    ‖WithLp.toLp 2 v‖ ≤ ‖a‖ * Real.sqrt ((1 + m : ℝ) ^ j) := by
  rw [EuclideanSpace.norm_eq]
  have hs : ∑ I, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (PlIdx j m)) I‖ ^ 2
      = ‖a‖ ^ 2 * ∑ I : PlIdx j m, ‖(colsOf (onePipe Z) I).det‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [hv, mul_pow]
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (h₃ j m Z hZ)) (norm_nonneg _)

theorem log_block (h₃ : PlueckerKernel.Statement) (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (ha : a ≠ 0) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) (hv0 : 0 < ‖WithLp.toLp 2 v‖) :
    -((j : ℝ) / 2 * Real.log (1 + m)) ≤ Real.log (‖a‖ / ‖WithLp.toLp 2 v‖) := by
  have hb := norm_block_le h₃ j m Z hZ a v hv
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hm : (0 : ℝ) < (1 + m : ℝ) ^ j := by positivity
  have hl := Real.log_le_log hv0 hb
  rw [Real.log_mul ha'.ne' (Real.sqrt_pos.mpr hm).ne', Real.log_sqrt hm.le, Real.log_pow] at hl
  rw [Real.log_div ha'.ne' hv0.ne']
  linarith

end RootLogNormBoundAlt

open RootLogNormBoundAlt in

theorem RootLogNormBound.proof (h₁ : RootAnchorNonzero.Statement) (h₂ : RootPointConj.Statement)
    (h₃ : PlueckerKernel.Statement) : RootLogNormBound.Statement := by
  intro f j m ζ hζ z hz
  have hpos : ∀ τ : Fin f, 0 < ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ := fun τ =>
    (fsMetric (PlIdx j m)).pos _ fun h0 => by
      obtain ⟨i, hi⟩ := hz.1 τ
      exact hi (congrFun h0 i)
  have key : ∀ τ : Fin f, -((j : ℝ) / 2 * Real.log (1 + m)) ≤
      Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    intro τ
    obtain ⟨ζ', hζ', hz'⟩ := h₂ f j m ζ hζ z hz τ
    exact log_block h₃ j m ζ' (fun a b => by
        obtain ⟨k, hk, h⟩ := hζ' a b
        exact Complex.norm_eq_one_of_pow_eq_one h hk.ne')
      _ (h₁ f j m ζ hζ z hz τ) _ hz' (hpos τ)
  have hne : ∀ τ ∈ (Finset.univ : Finset (Fin f)),
      ‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ ≠ 0 := fun τ _ =>
    div_ne_zero (norm_ne_zero_iff.mpr (h₁ f j m ζ hζ z hz τ)) (hpos τ).ne'
  have e : logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z =
      ∑ τ, Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    rw [← Real.log_prod hne]
    simp [logNorm, fsMulti, HermLine.ofMetrics, fsMetric, rootAnchorSection, Finset.prod_div_distrib]
  rw [e]
  calc -grassConst f j m = ∑ _τ : Fin f, -((j : ℝ) / 2 * Real.log (1 + m)) := by
        simp [grassConst]; ring
    _ ≤ _ := Finset.sum_le_sum fun τ _ => key τ

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

namespace MultiHomogMemCoordinate

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem mapDomain_fst_eq (m : (Σ k, ι k) →₀ ℕ) (a : K → ℕ) (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    Finsupp.mapDomain Sigma.fst m = Finsupp.equivFunOnFinite.symm a := by
  ext k
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [hm]
  · intro b _ hb
    simp [hb]
  · simp

theorem cone_monomial (y : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (a : K → ℕ)
    (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    mConeMap y (monomial m c) =
      C (aeval y (monomial m c)) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  have hX : (monomial (Finsupp.mapDomain Sigma.fst m) (1 : Ω) : MvPolynomial K Ω) =
      m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e := by
    rw [← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]
    simp only [map_pow, rename_X]
  rw [← mapDomain_fst_eq m a hm, hX]
  simp only [mConeMap, aeval_monomial, mul_pow, Finsupp.prod_mul, MvPolynomial.algebraMap_apply, map_finsuppProd,
    map_pow, map_mul]
  ring

theorem cone_eq (y : (Σ k, ι k) → Ω) (g : MRing ι) (a : K → ℕ) (hg : IsMultiHomog g a) :
    mConeMap y g = C (aeval y g) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m hm => cone_monomial y m _ a (hg m hm)

end MultiHomogMemCoordinate

open MultiHomogMemCoordinate in

theorem MultiHomogMemCoord.proof : MultiHomogMemCoord.Statement := by
  intro K _ ι _ Ω _ y g a hg
  rw [mCoordIdeal, RingHom.mem_ker, cone_eq y g a hg, C_mul_monomial, mul_one,
    monomial_eq_zero]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootDenseAlt

theorem aeval_grassPolyCoord {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval x (grassPolyCoord f j m p) = rootCoord (fun τ a b => x (τ, a, b)) p := by
  simp only [grassPolyCoord, rootCoord]
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp only [colsOf, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
    onePipe, Matrix.of_apply]
  generalize (p.2.1.orderEmbOfFin p.2.2) b = c
  induction c using Fin.addCases with
  | left c => simp [Fin.append_left, Matrix.one_apply, apply_ite]
  | right c => simp [Fin.append_right]

theorem aeval_rootCoord {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ) (g : MRing (plBlocks f j m)) :
    aeval (rootCoord (fun τ a b => x (τ, a, b))) g = aeval x (aeval (grassPolyCoord f j m) g) := by
  rw [show aeval x (aeval (grassPolyCoord f j m) g) =
      ((aeval x).restrictScalars ℤ).comp (aeval (grassPolyCoord f j m)) g from rfl, comp_aeval]
  exact congrArg (fun y => aeval y g) (funext fun p => (aeval_grassPolyCoord x p).symm)

theorem aeval_comp_ringHom {σ τ Ω : Type*} [Field Ω] (φ : MvPolynomial σ ℚ →+* Ω)
    (P : τ → MvPolynomial σ ℚ) (g : MvPolynomial τ ℤ) :
    aeval (fun i => φ (P i)) g = φ (aeval P g) := by
  have : (aeval (fun i => φ (P i)) : MvPolynomial τ ℤ →ₐ[ℤ] Ω).toRingHom =
      φ.comp (aeval P).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  exact congrArg (fun ψ : MvPolynomial τ ℤ →+* Ω => ψ g) this

end RootDenseAlt

theorem RootDense.proof (h₁ : MultiHomogMemCoord.Statement) (h₂ : RootsOfUnityDense.Statement) :
    RootDense.Statement := by
  intro f j m g ⟨a, ha⟩ hg
  have hQ0 : aeval (grassPolyCoord f j m) g ≠ 0 := by
    intro h0
    apply hg
    rw [grassIdeal, h₁ (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) g a ha]
    exact (RootDenseAlt.aeval_comp_ringHom
      (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)) _ g).trans
      (by rw [h0, map_zero])
  let e := Fintype.equivFin (Fin f × Fin j × Fin m)
  have hP : rename e (map (algebraMap ℚ ℂ) (aeval (grassPolyCoord f j m) g)) ≠ 0 := by
    intro h
    apply hQ0
    apply map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    apply rename_injective e e.injective
    simpa using h
  obtain ⟨z, hz, hzQ⟩ : ∃ z : Fin (Fintype.card (Fin f × Fin j × Fin m)) → ℂ,
      (∀ i, ∃ k : ℕ, 0 < k ∧ z i ^ k = 1) ∧
        eval z (rename e (map (algebraMap ℚ ℂ) (aeval (grassPolyCoord f j m) g))) ≠ 0 := by
    by_contra! H
    exact hP (h₂ _ _ H)
  refine ⟨rootPointIdeal (fun τ a b => (z ∘ e) (τ, a, b)), ⟨_, fun τ a b => hz _, rfl⟩, ?_⟩
  show g ∉ mCoordIdeal _
  rw [h₁ (Fin f) (plBlocks f j m) ℂ _ g a ha]
  refine fun h => hzQ ?_
  rw [eval_rename, eval_map, ← aeval_def, ← RootDenseAlt.aeval_rootCoord]
  exact h

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem GrassHeightBound.proof (hArith : GrassArithVar.Statement) (hRoot : RootArithVar.Statement)
    (hSemi : FsLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : FsConjInvariant.Statement) (hLe : GrassLeRoot.Statement) (hHt : RootHeight.Statement)
    (hDense : RootDense.Statement) : GrassHeightBound.Statement := by
  intro hZ2 f j m hf II hII
  refine hZ2 (Fin f) (plBlocks f j m) (grassIdeal f j m) ⊥ (f * j * m) (fsMulti (plBlocks f j m))
    (grassConst f j m) (rootFamily f j m) II hII (hArith f j m hf) bot_le (hSemi _ _ _)
    (hNef _ _ _ _ fun _ => ?_) (hConj _ _) ?_ (hDense f j m)
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · rintro W ⟨ζ, hζ, rfl⟩
    exact ⟨hRoot f j m ζ hf hζ, hLe f j m ζ, hHt f j m ζ hf hζ II hII⟩

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField NumberField.ComplexEmbedding

noncomputable section

namespace DualLineConjugation

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def conjPerm (K : Type) [Field K] : Equiv.Perm (K →+* ℂ) :=
  Function.Involutive.toPerm _ (involutive_conjugate K)

omit [Fintype T] [DecidableEq T] in

theorem conj_mulVec (b : Module.Basis T ℤ (dualLattice F)) (w : (K →+* ℂ) × Fin i → ℂ) :
    (fun t => starRingEnd ℂ ((dualEmbMatrix b *ᵥ w) t)) =
      dualEmbMatrix b *ᵥ fun p => starRingEnd ℂ (w (conjugate p.1, p.2)) := by
  funext t
  simp only [mulVec, dotProduct, map_sum, map_mul]
  refine Fintype.sum_equiv ((conjPerm K).prodCongr (Equiv.refl _)) _ _ fun p => ?_
  simp [conjPerm, dualEmbMatrix]

theorem recover_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualRecover b hb (fun t => starRingEnd ℂ (z t)) =
      fun p => starRingEnd ℂ (dualRecover b hb z (conjugate p.1, p.2)) := by
  have h1 : ∀ w, (dualRecover b hb).symm w = dualEmbMatrix b *ᵥ w := fun w => by
    simp [dualRecover]
  apply (dualRecover b hb).symm.injective
  rw [LinearEquiv.symm_apply_apply, h1, ← conj_mulVec b (dualRecover b hb z), ← h1,
    LinearEquiv.symm_apply_apply]

theorem re_conj_form {n : Type} [Fintype n] (H : Matrix n n ℂ) (v : n → ℂ) :
    (star (fun j => starRingEnd ℂ (v j)) ⬝ᵥ (H *ᵥ fun j => starRingEnd ℂ (v j))).re =
      (star v ⬝ᵥ (H.map (starRingEnd ℂ) *ᵥ v)).re := by
  rw [← Complex.conj_re (star v ⬝ᵥ _)]
  congr 1
  simp [dotProduct, mulVec, map_sum, map_mul]

theorem normSq_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualNormSq b hb (fun t => starRingEnd ℂ (z t)) = dualNormSq b hb z := by
  unfold dualNormSq
  rw [recover_conj]
  refine Fintype.sum_equiv (conjPerm K) _ _ fun σ => ?_
  have hσ : conjPerm K σ = conjugate σ := rfl
  rw [hσ, F.conj σ]
  exact re_conj_form (F.metric σ) fun j => dualRecover b hb z (conjugate σ, j)

end DualLineConjugation

theorem DualLineConj.proof : DualLineConj.Statement := by
  intro K _ _ i F T _ _ b hb z
  show Real.sqrt (dualNormSq b hb fun t => starRingEnd ℂ (z ⟨(), t⟩)) =
    Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  rw [DualLineConjugation.normSq_conj b hb fun t => z ⟨(), t⟩]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField

noncomputable section

namespace PointDegreeComplexPositive

theorem card_algHom_pos {K' : Type} [Field K'] [NumberField K'] (E : IntermediateField ℚ K') :
    0 < Nat.card (E →ₐ[ℚ] ℂ) := by
  have : FiniteDimensional ℚ E := inferInstance
  have : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  have : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  exact Nat.card_pos

end PointDegreeComplexPositive

theorem PointDegCPos.proof : PointDegCPos.Statement := by
  intro T _ K' _ _ y hP
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP]
  exact PointDegreeComplexPositive.card_algHom_pos _

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace PointVertRAux

theorem degC_eq_finrank {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K']
    {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) :
    degC (mCoordIdeal y) = Module.finrank ℚ (blockFnField y) := by
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP, Nat.card_eq_fintype_card,
    AlgHom.card]

end PointVertRAux

theorem PointVertR.proof (hI : VertRIndex.Statement) (hN : SectionIndexNorm.Statement) :
    PointVertR.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  rw [hI T K' y s hP hs hsP, PointVertRAux.degC_eq_finrank hP,
    ← Module.finrank_mul_finrank ℚ (blockFnField y) K', Nat.cast_mul, mul_assoc,
    hN T K' y s hP hs hsP]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem DualTopSubLattice.proof (hBasis : DualTopBasisChange.Statement)
    (hStacked : DualTopStacked.Statement) (hDeg : DualStackedDegree.Statement) :
    DualTopSubLattice.Statement := by
  intro K _ _ i F F' T T' _ _ _ _ b hb b' hb' II hi hII hle
  have hcard : Fintype.card T = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective b hb, DualTopStackedExistence.card_eq_of_bijective b' hb']
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked hle b b' hcard
  have hb₁ := DualEmbBijective.proof K i F T' b₁
  have hb₁' := DualEmbBijective.proof K i F' T' b₁'

  have h1 : II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T') (dualIdeal b₁') i (fun _ => dualLine F'.withStdMetric b₁' hb₁') :=
    hBasis K i F'.withStdMetric T' T' b₁' hb₁' b' hb' II hi hII
  have h2 : II Unit (dualBlocks T') (dualIdeal b₁) i (fun _ => dualLine F.withStdMetric b₁ hb₁) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) :=
    hBasis K i F.withStdMetric T T' b hb b₁ hb₁ II hi hII

  have h3 := hStacked K i F F' T' b₁ hb₁ b₁' hb₁' a II hi hII hle hab
  have h4 := hDeg K i F F' T' b₁ b₁' a hle hab
  rw [h1, h3, h2, h4]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

theorem DualGeomDegStandard.proof (hD : DualGeomDegCharts.Statement)
    (hG : GrassGeomDegChart.Statement) (hM : ChartMassInvariant.Statement) :
    DualGeomDegStandard.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨A, hA, hE⟩ := hD K i F T b hb hi
  obtain ⟨B, hB, hG'⟩ := hG (i - 1)
  have e1 : 1 * 1 * (i - 1) = i - 1 := by simp
  have hterm : ∀ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ) =
      chartMass (1 : Matrix (Fin (i - 1 + 1)) (Fin (i - 1 + 1)) ℂ) := fun σ =>
    hM _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hA σ).1)
  rw [e1, hE, hG', hM _ _ (Matrix.PosDef.conjTranspose_mul_self B hB.1),
    Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, Finset.card_univ,
    Embeddings.card K ℂ, nsmul_eq_mul]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem DualTopStandard.proof (hBC : DualStdBaseChange.Statement) (hGL : GrassLinesProj.Statement) :
    DualTopStandard.Statement := by
  intro K _ _ i T _ _ b hb II hi hII
  rw [hBC K i T b hb II hi hII]
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, hGL m II hII]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace TopDualBound

theorem grassConst_lines {i : ℕ} (hi : 1 ≤ i) : grassConst 1 1 (i - 1) = 1 / 2 * Real.log i := by
  have h : (1 : ℝ) + ((i - 1 : ℕ) : ℝ) = i := by
    rw [Nat.cast_sub hi]; push_cast; ring
  simp only [grassConst, h]
  norm_num

theorem dim_lines {i : ℕ} (hi : 1 ≤ i) : ((1 * 1 * (i - 1) + 1 : ℕ) : ℝ) = i := by
  congr 1; omega

end TopDualBound

theorem DualTopBound.proof (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hMetric : DualTopMetricChange.Statement)
    (hLattice : DualTopLatticeChange.Statement) (hStd : DualTopStandard.Statement)
    (hDeg : DualGeomDegStandard.Statement) (hGrass : GrassHeightBound.Statement) :
    DualTopBound.Statement := by
  intro hZ2 K _ _ i F T _ _ b hb II hi hII
  obtain ⟨T', _, _, ⟨b'⟩⟩ := hBasis K i (HermLattice.standard K i)
  have hb' := hBij K i (HermLattice.standard K i) T' b'
  set g := geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd
  have hA := hMetric K i F T b hb II hi hII
  have hB := hLattice K i F T T' b hb b' hb' II hi hII
  have hC := hStd K i T' b' hb' II hi hII
  have hG := hDeg K i F T b hb hi
  have hH := hGrass hZ2 1 1 (i - 1) le_rfl II hII
  rw [TopDualBound.dim_lines hi, TopDualBound.grassConst_lines hi] at hH
  rw [hA, hB, hC, hG]
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hslope : (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * (d * g) =
      -F.degree * g + d * ((i : ℝ) * (1 / 2 * Real.log i) * g) := by
    simp only [HermLattice.slope, normalise]
    rw [← hd]
    field_simp
  rw [hslope]
  have := mul_le_mul_of_nonneg_left hH hd0.le
  linarith

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem LineOfLargeDegreeFromZ.proofDual (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hArith : DualArithVar.Statement)
    (hSemi : DualLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : DualLineConj.Statement) (hPt : DualPointLineDegree.Statement)
    (hTop : DualTopBound.Statement) (hPos : DualGeomDegPos.Statement) :
    LineOfLargeDegreeFromZ.Statement := by
  intro hZ1 hZ2 hEx K _ _ i hi F ε hε
  obtain ⟨II, hII⟩ := hEx
  obtain ⟨T, _, _, ⟨b⟩⟩ := hBasis K i F
  have hb := hBij K i F T b
  set A := dualLine F b hb with hA
  set e : ℝ := -F.slope + 1 / 2 * Real.log i + ε with he
  by_contra hne
  push Not at hne
  have hW : ∀ W : Ideal (MRing (dualBlocks T)), IsArithVar W 1 → dualIdeal b ≤ W →
      e * degC W ≤ II Unit (dualBlocks T) W 1 ![A] := by
    intro W hW1 hPW
    obtain ⟨hdeg, K', iF, iN, iA, v, hv, hline⟩ := hPt K i F T b hb II hII W hW1 hPW
    have hlt := hne K' iF iN iA v hv
    rw [hline] at hlt
    have hd : (0 : ℝ) < degC W := by exact_mod_cast hdeg
    have h1 : e < II Unit (dualBlocks T) W 1 ![A] / degC W := by
      rw [neg_div] at hlt
      linarith
    exact ((lt_div_iff₀ hd).mp h1).le
  have hV : IsArithVar (dualIdeal b) (i - 1 + 1) := by
    rw [Nat.sub_add_cancel hi]; exact hArith K i F T b hi
  have hZ := hZ1 Unit (dualBlocks T) (dualIdeal b) ⊥ (i - 1) A e II hII hV
    bot_le (hSemi K i F T b hb) (hNef _ _ _ _ fun _ => zero_le_one) (hConj K i F T b hb) hW
  rw [Nat.sub_add_cancel hi] at hZ
  have hT := hTop hZ2 K i F T b hb II hi hII
  have hG := hPos K i F T b hb hi
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have key : (i : ℝ) * e * geomDeg (dualIdeal b) A (i - 1) ≤
      (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * geomDeg (dualIdeal b) A (i - 1) := hZ.trans hT
  have : (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) ≤ 0 := by
    rw [he] at key
    nlinarith
  have : 0 < (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) :=
    mul_pos (mul_pos hi' hε) hG
  linarith

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem CoordConeArithVar.full : CoordConeArithVar.Statement :=
  CoordConeArithVar.proof IntDomainDim.full

theorem GrassArithVar.full : GrassArithVar.Statement := GrassArithVar.proof CoordConeArithVar.full

theorem RootArithVar.full : RootArithVar.Statement := RootArithVar.proof CoordConeArithVar.full

theorem DualArithVar.full : DualArithVar.Statement := DualArithVar.proof CoordConeArithVar.full

theorem FsLineSemipositive.full : FsLineSemipositive.Statement :=
  FsLineSemipositive.proof FsLineSmooth.proof FsLineLevi.proof

theorem RootPointConj.full : RootPointConj.Statement := RootPointConj.proof RootAnchorNonzero.proof

theorem RootPointsFinite.full : RootPointsFinite.Statement :=
  RootPointsFinite.proof RootAnchorNonzero.proof

theorem RootLogNormBound.full : RootLogNormBound.Statement :=
  RootLogNormBound.proof RootAnchorNonzero.proof RootPointConj.full PlueckerKernel.full

theorem RootHeight.full : RootHeight.Statement :=
  RootHeight.proofNE RootArithVar.full RootDivSuppEmpty.proof RootLogNormBound.full
    RootPointsFinite.full PtsIntegralZeroLowerNE.proof MultiHomogMemCoord.proof FsLineSmooth.proof

theorem RootDense.full : RootDense.Statement :=
  RootDense.proof MultiHomogMemCoord.proof RootsOfUnityDense.full

theorem GrassHeightBound.full : GrassHeightBound.Statement :=
  GrassHeightBound.proof GrassArithVar.full RootArithVar.full FsLineSemipositive.full
    NefOfNonneg.proof FsConjInvariant.proof GrassLeRoot.proof RootHeight.full RootDense.full

theorem DualStdMassAt.full : DualStdMassAt.Statement :=
  DualStdMassAt.proof DualPtsOnPlane.proof DualPtsOfPlane.proof

theorem DualPointLineDegree.ofOpen (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement) :
    DualPointLineDegree.Statement :=
  DualPointLineDegree.proof DualCurvePoint.proof PointDegCPos.proof PointArInt.proof
    (PointVertR.proof hVI hSN) DualLineIndex.proof DualLineSemipositive.proof

theorem DualTopBound.ofOpen (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement) :
    DualTopBound.Statement :=
  DualTopBound.proof DualLatticeBasisExists.proof DualEmbBijective.proof
    (DualTopMetricChange.proof Telescope.proof hEnergy)
    (DualTopLatticeChange.proof (DualTopSubLattice.proof hBasis hStacked hSDeg))
    (DualTopStandard.proof hBC hGL) (DualGeomDegStandard.proof hCharts hGChart hMass)
    GrassHeightBound.full

theorem DualGeomDegPos.ofOpen (hDeg : DegreeStatement) (hInd : PtsIndepStatement) :
    DualGeomDegPos.Statement :=
  DualGeomDegPos.proof hDeg hInd DualArithVar.full DualLineSemipositive.proof DualPtsOnPlane.proof
    DualStdMassAt.full

theorem LineOfLargeDegreeFromZ.ofOpen (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement)
    (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement)
    (hDeg : DegreeStatement) (hInd : PtsIndepStatement) :
    LineOfLargeDegreeFromZ.Statement :=
  LineOfLargeDegreeFromZ.proofDual DualLatticeBasisExists.proof DualEmbBijective.proof
    DualArithVar.full DualLineSemipositive.proof NefOfNonneg.proof DualLineConj.proof
    (DualPointLineDegree.ofOpen hVI hSN)
    (DualTopBound.ofOpen hEnergy hBasis hStacked hSDeg hBC hGL hCharts hGChart hMass)
    (DualGeomDegPos.ofOpen hDeg hInd)

theorem KernelsCut.ofOpen (hZ1 : SuccessiveMinimaLowerBound) (hZ2 : SuccessiveMinimaUpperBound)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement)
    (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement)
    (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement)
    (hDeg : DegreeStatement) (hInd : PtsIndepStatement)
    (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestTerms.FlagIntegralKillsPowerSums.Statement)
    (h₃ : RestTerms.RestTermWellDefined.Statement) (h₄ : RestTerms.SameFactorBound.Statement)
    (h₅ : RestTerms.RestBound.Statement) : KernelsCut.Statement :=
  KernelsCut.proof
    (LineOfLargeDegreeFromZ.ofOpen hVI hSN hEnergy hBasis hStacked hSDeg hBC hGL hCharts hGChart
      hMass hDeg hInd hZ1 hZ2 hI)
    (RestTermSharp.ofRestTerms h₁ h₂ h₃ h₄ h₅)

end GroundTheory.Heights₂.Heights
end
