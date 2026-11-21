import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFormulaPolynomialGen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedLocalFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetIntegralUnramifiedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumExhaustionUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityBoundUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianVolumeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelJointReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterLevelFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetMeasureFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicCharacterLocalComponentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorConditionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMatrixIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedFieldStructure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExistence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionThree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFour
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDualAtPlace
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual

section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

namespace GoodLoc

variable (hG : GoodLoc σ J T bs v ψv S σS ϖ ε)
include hG

theorem coe_pS : ((hG.pS : S) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ := rfl

theorem cT_smul_pS (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) :
    PositivityTheory.PfSWUS.Loc.cT σS (hG.pS • X) = hG.pS • X := by
  ext a b
  have h1 := congrFun (congrFun hX a) b
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul] at h1 ⊢
  have h2 : σS hG.pS = hG.pS := hG.quad.fix_ϖ
  rw [h2, h1]

theorem hermLev_succ (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) :
    hG.hermLev (k + 1) (hG.pS • X) (hG.cT_smul_pS k X hX) = hG.hermLev k X hX := by
  apply Subtype.ext
  funext a b
  show (ϖ ^ (k + 1))⁻¹ • (((hG.pS • X) a b : S) : Fv F v ⊗[F] E) = (ϖ ^ k)⁻¹ • ((X a b : S) : Fv F v ⊗[F] E)
  rw [Matrix.smul_apply, smul_eq_mul, Subring.coe_mul, coe_pS, ← Algebra.smul_def, smul_smul, pow_succ, mul_inv,
    mul_assoc, inv_mul_cancel₀ hG.unif_ne, mul_one]

def liftH {k : ℕ} (B : hermMod σS hG.pS n k) : Matrix (Fin n) (Fin n) S := Classical.choose B.2

theorem liftH_herm {k : ℕ} (B : hermMod σS hG.pS n k) : PositivityTheory.PfSWUS.Loc.cT σS (hG.liftH B) = hG.liftH B :=
  (Classical.choose_spec B.2).1

theorem red_liftH {k : ℕ} (B : hermMod σS hG.pS n k) : red hG.pS k (hG.liftH B) = B.1 :=
  (Classical.choose_spec B.2).2

def iota (k : ℕ) (B : hermMod σS hG.pS n k) : HermR (Fv F v) σ n ⧸ H0 S σ n :=
  QuotientAddGroup.mk (hG.hermLev k (hG.liftH B) (hG.liftH_herm B))

theorem iota_eq (hCL : ClassLev) (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X)
    (B : hermMod σS hG.pS n k) (hB : red hG.pS k X = B.1) :
    hG.iota k B = QuotientAddGroup.mk (hG.hermLev k X hX) := by
  unfold iota
  rw [QuotientAddGroup.eq, neg_add_eq_sub]
  exact (hCL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG k X (hG.liftH B) hX (hG.liftH_herm B)).2 (by rw [hB, hG.red_liftH])

theorem iota_inj (hCL : ClassLev) (k : ℕ) : Function.Injective (hG.iota k) := by
  intro B B' h
  unfold iota at h
  rw [QuotientAddGroup.eq, neg_add_eq_sub] at h
  have := (hCL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG k (hG.liftH B') (hG.liftH B) (hG.liftH_herm B') (hG.liftH_herm B)).1 h
  rw [hG.red_liftH, hG.red_liftH] at this
  exact Subtype.ext this.symm

theorem iota_succ (hCL : ClassLev) (k : ℕ) (B : hermMod σS hG.pS n k) :
    ∃ B' : hermMod σS hG.pS n (k + 1), hG.iota (k + 1) B' = hG.iota k B := by
  refine ⟨⟨red hG.pS (k + 1) (hG.pS • hG.liftH B), hG.pS • hG.liftH B, hG.cT_smul_pS k _ (hG.liftH_herm B), rfl⟩, ?_⟩
  rw [hG.iota_eq hCL (k + 1) (hG.pS • hG.liftH B) (hG.cT_smul_pS k _ (hG.liftH_herm B)) _ rfl, hG.hermLev_succ]
  rfl

theorem iota_surj (hCL : ClassLev) (hEx : Exhaust) (c : HermR (Fv F v) σ n ⧸ H0 S σ n) :
    ∃ k B, hG.iota k B = c := by
  induction c using QuotientAddGroup.induction_on with
  | H b =>
    obtain ⟨k, X, hX, rfl⟩ := hEx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG b
    exact ⟨k, ⟨red hG.pS k X, X, hX, rfl⟩, hG.iota_eq hCL k X hX _ rfl⟩

theorem f_lev (hNP : NuPow) (hJ : JtLev) (hNL : NuLev) (hPL : PsiLev) (hT : ∀ a b, σ (T b a) = T a b)
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (hμ : SdW F E σ M J (Fv F v) ψv n μv)
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)) (hlam : lam.IsAddHaarMeasure)
    (hL : (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (z : ℂ) (k : ℕ) (B : hermMod σS hG.pS n k) :
    whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z
      (hG.hermLev k (hG.liftH B) (hG.liftH_herm B)) =
    ((ε : ℂ) ^ M * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * z + n))) ^
        Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1) *
      hG.psiLev (c := -1) (neg_mem (one_mem _)) k (Matrix.trace (red hG.pS k (matS S T hG.T_int) * B.1)) := by
  have e1 := hNL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG lam L hlam hL k (hG.liftH B) (hG.liftH_herm B)
  have e2 := hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG μv hμ k (hG.liftH B) (hG.liftH_herm B)
  have e3 := hPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG hT k (hG.liftH B) (hG.liftH_herm B)
  rw [hG.red_liftH] at e1 e2 e3
  have e4 : nuAt hG.pS B.1 = (Ideal.absNorm v.asIdeal ^ 2) ^ Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1) :=
    hNP S σS hG.pS _ ε hG.quad n k B.1 B.2
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have := hG.quad.one_lt
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  simp only [whI]
  rw [e1, e2, e3]
  congr 1
  set D := Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1)
  set q := Ideal.absNorm v.asIdeal
  rw [e4]
  have h5 : ((((q ^ 2) ^ D : ℕ) : ℝ) : ℂ) = ((q : ℂ) ^ (2 * D : ℕ)) := by push_cast; ring
  rw [h5, ← Complex.natCast_cpow_natCast_mul]
  have h6 : ((2 * D : ℕ) : ℂ) * -(z - ((M : ℂ) - n) / 2) = (D : ℂ) * (2 * -(z - ((M : ℂ) - n) / 2)) := by push_cast; ring
  rw [h6, Complex.cpow_nat_mul, ← mul_pow]
  congr 1
  rw [← Complex.cpow_intCast, mul_left_comm, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

end GoodLoc

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct

theorem locC_of_steps (hP : UnrPoly) (hCI : CosetInt) (hTE : TsumExhaust) (hNP : NuPow) (hNB : NuBound)
    (hLC : LevChars) (hVH : HermitianLatticeVolumeOne) (hJ : JtLev) (hNL : NuLev) (hPL : PsiLev) (hEx : Exhaust) (hCL : ClassLev)
    (hInv : HermitianLatticeInvariance) (hCM : CosetMeas) : LocC := by
  classical
  intro F E _ _ _ _ _ σ M n d J T hT bs v ψv S σS ϖ ε hG μv νv lam L hμ hν hlam hL z hz
  set q : ℕ := Ideal.absNorm v.asIdeal with hq
  have hR : IsUnrQuad S σS hG.pS q ε := hG.quad
  have hq1 : 1 < q := hR.one_lt
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hfin : ∀ k, Finite (S ⧸ lev hG.pS k) := fun k => Nat.finite_of_card_ne_zero (by
    rw [GlobalTheory.T.unramified_quotient_card S σS hG.pS q ε hR k]; exact pow_ne_zero _ (by omega))
  letI : ∀ k, Fintype (S ⧸ lev hG.pS k) := fun k => Fintype.ofFinite _
  letI : ∀ k, Fintype (hermMod σS hG.pS n k) := fun k => Fintype.ofFinite _
  have hε1 : ‖(ε : ℂ)‖ = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

  set f := whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z with hf
  have hinv : ∀ b h, h ∈ H0 S σ n → f (b + h) = f b := fun b h hh =>
    hInv F E σ M n d J T bs v ψv S σS ϖ ε hG hT μv lam L hL z b h hh
  let fbar : HermR (Fv F v) σ n ⧸ H0 S σ n → ℂ := fun c => f (Quotient.out c)
  have hfbar : ∀ g, f g = fbar (QuotientAddGroup.mk g) := by
    intro g
    have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk g : HermR (Fv F v) σ n ⧸ H0 S σ n)) :
        HermR (Fv F v) σ n ⧸ H0 S σ n) = QuotientAddGroup.mk g := Quotient.out_eq' _
    rw [QuotientAddGroup.eq] at h1
    have := hinv (Quotient.out (QuotientAddGroup.mk g : HermR (Fv F v) σ n ⧸ H0 S σ n)) _ h1
    rw [add_neg_cancel_left] at this
    exact this

  set t : ℂ := (ε : ℂ) ^ M * (q : ℂ) ^ (-(2 * z + n)) with ht
  have hval : ∀ k (B : hermMod σS hG.pS n k), fbar (hG.iota k B) =
      t ^ Nat.log (q ^ 2) (nuAt hG.pS B.1) *
        hG.psiLev (c := -1) (neg_mem (one_mem _)) k (Matrix.trace (red hG.pS k (matS S T hG.T_int) * B.1)) := by
    intro k B
    rw [GoodLoc.iota, ← hfbar]
    exact hG.f_lev hNP hJ hNL hPL hT μv hμ lam L hlam hL z k B

  let C : ℕ → Finset (HermR (Fv F v) σ n ⧸ H0 S σ n) := fun k => Finset.univ.image (hG.iota k)
  have hCmono : Monotone C := by
    refine monotone_nat_of_le_succ fun k => ?_
    intro c hc
    obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨B', hB'⟩ := hG.iota_succ hCL k B
    exact Finset.mem_image.2 ⟨B', Finset.mem_univ _, hB'⟩
  have hCcov : ∀ c, ∃ k, c ∈ C k := by
    intro c
    obtain ⟨k, B, rfl⟩ := hG.iota_surj hCL hEx c
    exact ⟨k, Finset.mem_image.2 ⟨B, Finset.mem_univ _, rfl⟩⟩
  have hsumC : ∀ k, ∑ c ∈ C k, fbar c = ∑ B : hermMod σS hG.pS n k, fbar (hG.iota k B) := fun k =>
    Finset.sum_image fun B _ B' _ h => hG.iota_inj hCL k h
  have hnormC : ∀ k, ∑ c ∈ C k, ‖fbar c‖ = ∑ B : hermMod σS hG.pS n k, ‖t‖ ^ Nat.log (q ^ 2) (nuAt hG.pS B.1) := by
    intro k
    rw [Finset.sum_image fun B _ B' _ h => hG.iota_inj hCL k h]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [hval, norm_mul, norm_pow, AddChar.norm_apply, mul_one]

  have htn : ‖t‖ = (q : ℝ) ^ (-(2 * z.re + n)) := by
    rw [ht, norm_mul, norm_pow, hε1, one_pow, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    simp
  have hlt : (q : ℝ) ^ (n ^ 2) * ‖t‖ < 1 := by
    rw [htn, ← Real.rpow_natCast, ← Real.rpow_add (by exact_mod_cast (by omega : 0 < q))]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq1)
    push_cast
    nlinarith [sq_nonneg (n : ℝ), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hbound : ∀ k, ∑ c ∈ C k, ‖fbar c‖ ≤ 1 / (1 - (q : ℝ) ^ (n ^ 2) * ‖t‖) := by
    intro k
    rw [hnormC]
    have := hNB S σS hG.pS q ε hR n k ‖t‖ (norm_nonneg _) hlt
    rwa [tsum_fintype] at this

  have hlc : IsLevelChars σS hG.pS (hG.psiLev (c := -1) (neg_mem (one_mem _))) :=
    hLC F E σ M n d J T bs v ψv S σS ϖ ε hG (-1) (neg_mem (one_mem _)) (by simp)
  have hpoly : ∀ k, 1 ≤ k → ∑ c ∈ C k, fbar c = ∏ i : Fin n, (1 - t * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    intro k hk
    rw [hsumC, ← hP S σS hG.pS q ε hR _ hlc n (matS S T hG.T_int) hG.T_unimod k hk t, tsum_fintype]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [hval, mul_comm]

  obtain ⟨hsum, htend⟩ := hTE _ fbar C hCmono hCcov ⟨_, hbound⟩
  have htsum : ∑' c, fbar c = ∏ i : Fin n, (1 - t * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    refine tendsto_nhds_unique htend ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact (hpoly k hk).symm

  haveI := hν.1
  haveI := hCM F E σ M n d J T bs v ψv S σS ϖ ε hG |>.1
  have hcount : Countable (HermR (Fv F v) σ n ⧸ H0 S σ n) := by
    have : (Set.univ : Set (HermR (Fv F v) σ n ⧸ H0 S σ n)) ⊆ ⋃ k, Set.range (hG.iota k) := fun c _ => by
      obtain ⟨k, B, rfl⟩ := hG.iota_surj hCL hEx c
      exact Set.mem_iUnion.2 ⟨k, B, rfl⟩
    exact Set.countable_univ_iff.1 ((Set.countable_iUnion fun k => (Set.finite_range _).countable).mono this)
  obtain ⟨hI1, hI2⟩ := hCI _ νv (H0 S σ n) (hCM F E σ M n d J T bs v ψv S σS ϖ ε hG).2
    (hVH F E σ M n d J T bs v ψv S σS ϖ ε hG νv hν) hcount f fbar hfbar
  refine ⟨hI1.2 hsum, ?_⟩
  rw [hI2 hsum, htsum]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  rw [ht, mul_pow, mul_mul_mul_comm, ← pow_add, ← Complex.cpow_natCast (q : ℂ) (i : ℕ), ← Complex.cpow_add _ _ hq0]
  congr 2
  ring

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

section
namespace PositivityTheory.SiegelWeilFormula.Gunr

theorem unrPoly : PositivityTheory.SiegelWeilFormula.Gen.UnrPoly := GlobalTheory.T.unramified_formula_polynomial_gen GlobalTheory.T.unramified_local_formula

theorem locC : LocC :=
  locC_of_steps unrPoly GlobalTheory.T.coset_integral_unramified GlobalTheory.T.tsum_exhaustion_unramified GlobalTheory.T.multiplicity_power_formula GlobalTheory.T.multiplicity_bound_unramified GlobalTheory.T.level_characters_unramified GlobalTheory.T.integral_hermitian_volume_one GlobalTheory.T.level_joint_reduction GlobalTheory.T.multiplicity_level_formula GlobalTheory.T.character_level_formula GlobalTheory.T.level_exhaustion GlobalTheory.T.class_level_formula GlobalTheory.T.integral_hermitian_invariance GlobalTheory.T.coset_measure_formula

end PositivityTheory.SiegelWeilFormula.Gunr
end

section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_le_one_iff_mem' (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    ‖y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

omit [NumberField F] [NumberField E] in
theorem mem_basisSet_two (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) : (2 : F)⁻¹ ∈ basisSet σ bs := by
  classical
  simp [basisSet]

omit [NumberField F] [NumberField E] in
theorem mem_basisSet_one (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (k : Fin d) :
    bs.repr 1 k ∈ basisSet σ bs := by
  unfold basisSet
  simp

theorem two_of {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (hB : IntAt v (basisSet σ bs)) : ‖(2 : Fv F v)‖ = 1 := by
  have h1 := hB _ (mem_basisSet_two σ bs)
  rw [map_inv₀, map_ofNat, ← norm_le_one_iff_mem', norm_inv] at h1
  have h2 : ‖(2 : Fv F v)‖ ≤ 1 := by
    rw [norm_le_one_iff_mem', show (2 : Fv F v) = 1 + 1 by norm_num]
    exact add_mem (one_mem _) (one_mem _)
  have h0 : (2 : Fv F v) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    exact (map_ne_zero_iff _ (algebraMap F (Fv F v)).injective).mpr two_ne_zero
  have hpos : 0 < ‖(2 : Fv F v)‖ := norm_pos_iff.mpr h0
  have h3 := (inv_le_one₀ hpos).mp h1
  linarith

theorem unif_mem_Rv {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (hB : IntAt v (basisSet σ bs)) {ϖ : Fv F v} (hϖ : ϖ ∈ v.adicCompletionIntegers F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ Rv bs v := by
  intro k
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.basis_repr_tmul]
  simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact mul_mem hϖ (hB _ (mem_basisSet_one σ bs k))

theorem locRingE_of (h1 : RvRing) (h2 : FixedK) (h3 : UnifEx) (h4 : QuadAt) (h6 : TraceDualAt) : LocRingE := by
  intro F E i1 i2 i3 i4 i5 σ hCM d bs v hB
  obtain ⟨S, σS, hS, hσS⟩ := h1 F E σ d bs v hB
  obtain ⟨ϖ, hϖ0, hϖ1, hϖd, hϖc⟩ := h3 F v
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε : ℂ) = eSp E v := by
    unfold eSp
    split_ifs
    · exact ⟨-1, by simp⟩
    · exact ⟨1, by simp⟩
  have hϖS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v) ∈ S := by
    have := unif_mem_Rv hB ϖ.2
    rw [← hS] at this
    exact this
  have htr := h6 F E σ hCM d bs v hB
  rw [← hS] at htr
  exact ⟨S, σS, ϖ, ε, hϖS, hε, hS, hσS, h2 F E σ hCM v, ϖ.2, hϖ0, hϖ1,
    h4 F E σ hCM d bs v hB S σS hS hσS ϖ hϖ0 hϖ1 hϖd hϖc hϖS ε hε, two_of hB, htr⟩

theorem almostGood_ofE (h1 : FinInt) (h2 : PsiBasic) (h3 : PsiCond) (h4 : LocRingE) (h5 : LocMat) : AlmostGood := by
  classical
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  filter_upwards [h1 F (basisSet σ bs ∪ matSet bs J ∪ matSet bs T), h3 F ψ hψ] with v hv hc
  have hB : IntAt v (basisSet σ bs) := fun x hx => hv x (by simp [hx])
  have hMJ : IntAt v (matSet bs J) := fun x hx => hv x (by simp [hx])
  have hMT : IntAt v (matSet bs T) := fun x hx => hv x (by simp [hx])
  obtain ⟨S, σS, ϖ, ε, hϖ, hε, hcar, hsig, hfix, hϖO, hϖ0, hϖ1, hquad, htwo, htr⟩ := h4 F E σ hσ d bs v hB
  obtain ⟨hJi, hJu⟩ := h5 F E σ d bs v S σS hcar hsig M J hJ.1 hJ.2 hMJ
  obtain ⟨hTi, hTu⟩ := h5 F E σ d bs v S σS hcar hsig n T hT hdet hMT
  obtain ⟨pa, p0, pc⟩ := h2 F ψ hψ v
  exact ⟨S, σS, ϖ, ε, hε,
    { carrier := hcar, sig := hsig, fixed := hfix, unif_mem := hϖO, unif_ne := hϖ0, unif_lt := hϖ1, unif_S := hϖ,
      quad := hquad, two := htwo, trace_dual := htr, J_int := hJi, J_unimod := hJu, T_int := hTi, T_unimod := hTu,
      psi_add := pa, psi_zero := p0, psi_cont := pc, psi_cond := hc }⟩

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

section
namespace PositivityTheory.SiegelWeilFormula.Gunr

theorem almostGood : AlmostGood :=
  almostGood_ofE GlobalTheory.T.unramified_finite_integral GlobalTheory.T.basic_character_unramified GlobalTheory.T.character_conductor_condition
    (locRingE_of GlobalTheory.T.residue_ring_structure GlobalTheory.T.fixed_field_structure GlobalTheory.T.uniformizer_existence
      (quadAt_of GlobalTheory.T.unramified_quadratic_condition_one GlobalTheory.T.unramified_quadratic_condition_two GlobalTheory.T.unramified_quadratic_condition_three GlobalTheory.T.unramified_quadratic_condition_four GlobalTheory.T.unramified_quadratic_condition_five) GlobalTheory.T.trace_dual_at_place) GlobalTheory.T.local_matrix_integral

end PositivityTheory.SiegelWeilFormula.Gunr
end

section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

variable {F : Type} [Field F] [NumberField F]

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

theorem unrWhitX_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhitX := by
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  refine ⟨(n : ℝ) ^ 2, ?_⟩
  filter_upwards [hA F E σ hσ M J hJ n T hT hdet d bs ψ hψ] with v hv
  obtain ⟨S, σS, ϖ, ε, hε, hG⟩ := hv
  intro μv νv lam L hμ hν hlam hL z hz
  rw [← hε]
  exact hC F E σ M n d J T hT bs v (psiV F ψ v) S σS ϖ ε hG μv νv lam L hμ hν hlam hL z hz

theorem eSp_eq (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : ℤˣ, ((e : ℤ) : ℂ) = eSp E v := by
  unfold eSp
  split_ifs
  · exact ⟨-1, by simp⟩
  · exact ⟨1, by simp⟩

theorem unrWhitAll_of_X (h : UnrWhitX) : UnrWhitAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  obtain ⟨t, ht⟩ := h F E σ hσ M J hJ n T hT hdet d bs ψ hψ
  refine ⟨t, ?_⟩
  filter_upwards [ht] with v hv
  obtain ⟨e, he⟩ := eSp_eq E v
  exact ⟨e, fun μv νv lam L hμ hν hlam hL z hz => by rw [he]; exact hv μv νv lam L hμ hν hlam hL z hz⟩

theorem unrWhitAll_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhitAll := unrWhitAll_of_X (unrWhitX_of_parts hC hA)

theorem unrWhit_of_all (h : UnrWhitAll) : UnrWhit :=
  fun F E _ _ _ _ _ σ hσ M J hJ n _ T hT hdet d bs ψ hψ => h F E σ hσ M J hJ n T hT hdet d bs ψ hψ

theorem unrWhit_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhit := unrWhit_of_all (unrWhitAll_of_parts hC hA)

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

section
namespace PositivityTheory.SiegelWeilFormula.Gunr

theorem unrWhitX : PositivityTheory.SiegelWeilFormula.Gen.UnrWhitX := unrWhitX_of_parts locC almostGood

theorem unrWhit : PositivityTheory.SiegelWeilFormula.Gen.UnrWhit := unrWhit_of_parts locC almostGood

end PositivityTheory.SiegelWeilFormula.Gunr
end
