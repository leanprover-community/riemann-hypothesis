import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDrop
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestHeightBound
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsWord
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.DegreeTautologicalLineProjectiveLine
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.GramSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPowerSumOneZero
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.WeilBound.CoreStatements.FlagImmersions.MeanSlopeOfProportionalVolume
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT2
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AntisymmetricPerturbationBound
import Development.WeilBound.CoreStatements.FlagImmersions.AntisymmetryTowerTheorem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.DegFlSymmetryInvariance
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilTheorem
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CurveDegreeLinearNefCone
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPolynomialEval
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DivSuppArithHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatement

section
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (FlBlock FlIdx PFl xLine xDeg yFl fsHerm ΩFl refNorm)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Top.HhLabel

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def blockMap (σ : Equiv.Perm Ψ) : FlBlock Ψ N → FlBlock Ψ N := fun q => (σ q.1, q.2)

def coordMap (σ : Equiv.Perm Ψ) : (Σ q : FlBlock Ψ N, FlIdx Ψ N q) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨(σ p.1.1, p.1.2), p.2⟩

theorem blockMap_bijective (σ : Equiv.Perm Ψ) : Function.Bijective (blockMap (N := N) σ) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    simp only [blockMap, Prod.mk.injEq] at h
    rw [σ.injective h.1, h.2]
  · rintro ⟨τ, i⟩
    exact ⟨(σ.symm τ, i), by simp [blockMap]⟩

theorem coordMap_injective (σ : Equiv.Perm Ψ) : Function.Injective (coordMap (N := N) σ) := by
  rintro ⟨⟨τ, i⟩, A⟩ ⟨⟨τ', i'⟩, A'⟩ h
  simp only [coordMap, Sigma.mk.inj_iff, Prod.mk.injEq] at h
  obtain ⟨⟨h1, rfl⟩, h2⟩ := h
  obtain rfl := σ.injective h1
  cases eq_of_heq h2
  rfl

theorem coordMap_surjective (σ : Equiv.Perm Ψ) : Function.Surjective (coordMap (N := N) σ) := by
  rintro ⟨⟨τ, i⟩, A⟩
  refine ⟨⟨(σ.symm τ, i), A⟩, Sigma.ext (by simp [coordMap]) HEq.rfl⟩

theorem isBlockMap (σ : Equiv.Perm Ψ) : IsBlockMap (blockMap (N := N) σ) (coordMap σ) :=
  ⟨(blockMap_bijective σ).1, coordMap_injective σ, fun _ => rfl, fun q _ => coordMap_surjective σ q⟩

def matEquiv (N : ℕ) (σ : Equiv.Perm Ψ) : (Ψ × Fin N × Fin N) ≃ (Ψ × Fin N × Fin N) :=
  Equiv.prodCongr σ (Equiv.refl _)

def fieldAut (σ : Equiv.Perm Ψ) : ΩFl Ψ N ≃+* ΩFl Ψ N :=
  IsFractionRing.ringEquivOfRingEquiv (renameEquiv ℚ (matEquiv N σ)).toRingEquiv

theorem yFl_coordMap (σ : Equiv.Perm Ψ) (p : Σ q : FlBlock Ψ N, FlIdx Ψ N q) :
    yFl Ψ N (coordMap σ p) = fieldAut σ (yFl Ψ N p) := by
  unfold yFl fieldAut
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  show _ = (renameEquiv ℚ (matEquiv N σ)).toRingEquiv.toRingHom _
  rw [RingHom.map_det]
  congr 1
  refine Matrix.ext fun a b => ?_
  exact (rename_X (R := ℚ) (matEquiv N σ) (p.1.1, Fin.castLE (GroundTheory.Heights₂.Heights.LowerBoundFree.step_le p.1.2) a, p.2.1 b)).symm

theorem mCoordIdeal_ringHom {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    (i : Ω₀ →+* Ω) (y₀ : (Σ k, J k) → Ω₀) : mCoordIdeal (fun p => i (y₀ p)) = mCoordIdeal y₀ := by
  have key : ∀ f : MRing J, mConeMap (fun p => i (y₀ p)) f = MvPolynomial.map i (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp => simp only [map_mul, hp]; simp [mConeMap]
  ext f
  show mConeMap _ f = 0 ↔ mConeMap _ f = 0
  rw [key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective i i.injective)

theorem imageZ_PFl (σ : Equiv.Perm Ψ) : imageZ (coordMap σ) (PFl Ψ N) = PFl Ψ N := by
  unfold PFl
  rw [← GroundTheory.Heights₂.Heights.Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v (isBlockMap σ),
    ← mCoordIdeal_ringHom (fieldAut (N := N) σ : ΩFl Ψ N →+* ΩFl Ψ N) (yFl Ψ N)]
  congr 1
  funext p
  exact yFl_coordMap σ p

theorem blockFnField_coordMap (σ : Equiv.Perm Ψ) :
    blockFnField (yFl Ψ N ∘ coordMap σ) = blockFnField (yFl Ψ N) := by
  unfold blockFnField
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨coordMap σ p, coordMap σ q, by simp [coordMap, hpq], rfl⟩
  · rintro ⟨p, q, hpq, rfl⟩
    obtain ⟨p', rfl⟩ := coordMap_surjective σ p
    obtain ⟨q', rfl⟩ := coordMap_surjective σ q
    exact ⟨p', q', (blockMap_bijective σ).1 hpq, rfl⟩

theorem xDeg_blockMap (σ : Equiv.Perm Ψ) (p : Ψ × Fin N) (q : FlBlock Ψ N) :
    xDeg Ψ N (σ p.1, p.2) (blockMap σ q) = xDeg Ψ N p q := by
  by_cases h : q.1 = p.1 <;> simp [xDeg, blockMap, h]

theorem isPullHerm_xLine (σ : Equiv.Perm Ψ) (p : Ψ × Fin N) :
    IsPullHerm (blockMap σ) (coordMap σ) (xLine Ψ N p) (xLine Ψ N (σ p.1, p.2)) := by
  refine ⟨?_, fun z' => ?_⟩
  · show xDeg Ψ N (σ p.1, p.2) = pullDeg (blockMap σ) (xDeg Ψ N p)
    funext q
    obtain ⟨q', rfl⟩ := (blockMap_bijective σ).2 q
    unfold pullDeg
    rw [(blockMap_bijective σ).1.extend_apply, xDeg_blockMap]
  · show refNorm (xDeg Ψ N (σ p.1, p.2)) z' = refNorm (xDeg Ψ N p) fun r => z' (coordMap σ r)
    unfold refNorm
    refine (Fintype.prod_bijective (blockMap σ) (blockMap_bijective σ) _ _ fun k => ?_).symm
    rw [xDeg_blockMap]
    rfl

theorem degree_mapDomain {J J' : Type} (f : J → J') (m : J →₀ ℕ) : (m.mapDomain f).degree = m.degree := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb]
  | single a n => simp [Finsupp.mapDomain_single, Finsupp.degree_single]

end GlobalTheory.CompanionTheory.Ar.Top.HhLabel

namespace GlobalTheory.CompanionTheory.Ar.Top

open HhLabel in

theorem hhFl_labelInv : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ]
    (N : ℕ) [Nonempty Ψ], 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) →
    LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  intro II hII Ψ _ _ N _ _ hP σ F
  have key : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N,
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (σ (w k).1, (w k).2)) =
        II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (w k)) := by
    intro w
    have himg := imageZ_PFl (N := N) σ
    have hPF := hII.2.2.1 (FlBlock Ψ N) (FlIdx Ψ N) (FlBlock Ψ N) (FlIdx Ψ N) (blockMap σ) (coordMap σ) (ΩFl Ψ N)
      (yFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (w k)) (fun k => xLine Ψ N (σ (w k).1, (w k).2))
      (isBlockMap σ) hP (by show IsArithVar (imageZ (coordMap σ) (PFl Ψ N)) _; rw [himg]; exact hP)
      (fun _ => GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)
      (fun j => isPullHerm_xLine σ (w j))
    rw [blockFnField_coordMap, IntermediateField.relfinrank_self, Nat.cast_one, one_mul] at hPF
    exact hPF.trans (congrArg (fun P => II (FlBlock Ψ N) (FlIdx Ψ N) P (dimFl Ψ N + 1) fun k => xLine Ψ N (w k)) himg)
  induction F using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial m c =>
    rw [rename_monomial]
    by_cases hm : m.degree = dimFl Ψ N + 1
    · obtain ⟨w, rfl⟩ := RootFieldNumerics.HH.exists_word _ m hm
      have hmap : (∑ k, Finsupp.single (w k) (1 : ℕ)).mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) =
          ∑ k, Finsupp.single (σ (w k).1, (w k).2) 1 := by
        rw [Finsupp.mapDomain_finset_sum]
        simp only [Finsupp.mapDomain_single]
      have hwd := RootFieldNumerics.HH.hhFl_word II hII.1 hP (fun k => (σ (w k).1, (w k).2)) c
      rw [hmap, hwd, RootFieldNumerics.HH.hhFl_word II hII.1 hP w c, key w]
    · rw [HhModel.hhFl_monomial_of_ne II _ _ (by rwa [degree_mapDomain]), HhModel.hhFl_monomial_of_ne II _ _ hm]

end GlobalTheory.CompanionTheory.Ar.Top
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_label_invariant : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.hhFl_labelInv
end

section
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top.HhTestProof

open scoped ComplexOrder MatrixOrder in

theorem det_one_add_bound {a b : ℕ} (Z : Matrix (Fin a) (Fin b) ℂ) (hZ : ∀ i k, ‖Z i k‖ = 1) :
    0 < (1 + Z * Z.conjTranspose).det.re ∧ (1 + Z * Z.conjTranspose).det.re ≤ (1 + (b : ℝ)) ^ a := by
  have hA : (1 + Z * Z.conjTranspose).PosDef :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_self_mul_conjTranspose Z)
  refine ⟨(Complex.pos_iff.mp hA.det_pos).1, ?_⟩
  refine (ReciprocityTheory.GeometryOfNumbersTheory.gramSt_hadamard hA).trans (le_of_eq ?_)
  have hd : ∀ i : Fin a, (((1 : Matrix (Fin a) (Fin a) ℂ) + Z * Z.conjTranspose) i i).re = 1 + (b : ℝ) := by
    intro i
    have h1 : (Z * Z.conjTranspose) i i = ∑ k, Z i k * star (Z i k) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    have h2 : ∀ k, (Z i k * star (Z i k)).re = 1 := by
      intro k
      have := Complex.mul_conj (Z i k)
      rw [Complex.star_def, this, Complex.normSq_eq_norm_sq, hZ]
      simp
    rw [Matrix.add_apply, Matrix.one_apply_eq, Complex.add_re, Complex.one_re, h1, Complex.re_sum,
      Finset.sum_congr rfl fun k _ => h2 k]
    simp
  rw [Finset.prod_congr rfl fun i _ => hd i]
  simp

theorem half_log_det_le {j m N : ℕ} (hN : j + m = N) (Z : Matrix (Fin m) (Fin j) ℂ) (hZ : ∀ i k, ‖Z i k‖ = 1) :
    1 / 2 * Real.log (1 + Z * Z.conjTranspose).det.re ≤ ((min j m : ℕ) : ℝ) / 2 * Real.log ((N : ℝ) + 1) := by
  have hNr : (j : ℝ) + m = N := by exact_mod_cast hN
  have key : ∀ (c d : ℕ), c + d = N → ∀ x : ℝ, 0 < x → x ≤ (1 + (d : ℝ)) ^ c →
      1 / 2 * Real.log x ≤ (c : ℝ) / 2 * Real.log ((N : ℝ) + 1) := by
    intro c d hcd x hx hle
    have hcdr : (c : ℝ) + d = N := by exact_mod_cast hcd
    have h1 : Real.log x ≤ (c : ℝ) * Real.log (1 + (d : ℝ)) := by
      have := Real.log_le_log hx hle
      rwa [Real.log_pow] at this
    have h2 : Real.log (1 + (d : ℝ)) ≤ Real.log ((N : ℝ) + 1) := by
      apply Real.log_le_log (by positivity)
      have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
      linarith
    have h3 : (c : ℝ) * Real.log (1 + (d : ℝ)) ≤ (c : ℝ) * Real.log ((N : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg c)
    linarith
  rcases le_total m j with h | h
  · rw [min_eq_right h]
    obtain ⟨h0, h1⟩ := det_one_add_bound Z hZ
    exact key m j (by omega) _ h0 h1
  · rw [min_eq_left h]
    have hcomm : (1 + Z * Z.conjTranspose).det = (1 + Z.conjTranspose * Z).det :=
      Matrix.det_one_add_mul_comm _ _
    have hZ' : ∀ i k, ‖Z.conjTranspose i k‖ = 1 := by
      intro i k
      simp [Matrix.conjTranspose_apply, hZ]
    obtain ⟨h0, h1⟩ := det_one_add_bound Z.conjTranspose hZ'
    rw [Matrix.conjTranspose_conjTranspose] at h0 h1
    rw [hcomm]
    exact key j m (by omega) _ h0 h1

section Poly

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def negX : RP Ψ N →ₐ[ℝ] RP Ψ N := aeval fun x => -X x

theorem negX_monomial (m : Ψ × Fin N →₀ ℕ) (c : ℝ) :
    negX (monomial m c : RP Ψ N) = monomial m ((-1) ^ m.degree * c) := by
  have h1 : (m.prod fun i k => (-X i : RP Ψ N) ^ k) =
      C ((-1) ^ m.degree) * m.prod fun i k => (X i : RP Ψ N) ^ k := by
    rw [Finsupp.prod, Finsupp.prod]
    have : ∀ i ∈ m.support, (-X i : RP Ψ N) ^ m i = C ((-1) ^ m i) * X i ^ m i := by
      intro i _
      rw [neg_pow, map_pow, map_neg, map_one]
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, ← map_prod,
      Finset.prod_pow_eq_pow_sum]
    rfl
  rw [negX, aeval_monomial, h1, monomial_eq (a := (-1) ^ m.degree * c), map_mul, algebraMap_eq]
  ring

theorem coeff_negX (m : Ψ × Fin N →₀ ℕ) (F : RP Ψ N) :
    coeff m (negX F) = (-1) ^ m.degree * coeff m F := by
  induction F using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [negX_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq]; ring

end Poly

section Funs

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def hR (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (II : IntersectionSystem) : RP Ψ N →ₗ[ℝ] ℝ :=
  (basisMonomials (Ψ × Fin N) ℝ).constr ℝ fun m => GroundTheory.Heights₂.Heights.LowerBoundFree.hFlMono Ψ N II m

theorem hR_monomial (II : IntersectionSystem) (m : Ψ × Fin N →₀ ℕ) (c : ℝ) :
    hR Ψ N II (monomial m c) = c * GroundTheory.Heights₂.Heights.LowerBoundFree.hFlMono Ψ N II m := by
  have h : (monomial m c : RP Ψ N) = c • basisMonomials (Ψ × Fin N) ℝ m := by
    simp [smul_monomial]
  rw [h, map_smul, hR, Module.Basis.constr_basis, smul_eq_mul]

theorem hhFl_monomial (II : IntersectionSystem) (m : Ψ × Fin N →₀ ℕ) (c : ℝ) :
    hhFl Ψ N II (monomial m c) = c * ((-1) ^ m.degree * GroundTheory.Heights₂.Heights.LowerBoundFree.hFlMono Ψ N II m) := by
  have h : (monomial m c : RP Ψ N) = c • basisMonomials (Ψ × Fin N) ℝ m := by
    simp [smul_monomial]
  rw [h, map_smul, hhFl, Module.Basis.constr_basis, smul_eq_mul]

theorem hhFl_eq (II : IntersectionSystem) (F : RP Ψ N) : hhFl Ψ N II F = hR Ψ N II (negX F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u c => rw [negX_monomial, hhFl_monomial, hR_monomial]; ring
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

theorem hFl_eq (II : IntersectionSystem) (G : GroundTheory.Heights₂.Heights.LowerBoundFree.RootPoly Ψ N) :
    GroundTheory.Heights₂.Heights.LowerBoundFree.hFl Ψ N II G = hR Ψ N II (map (algebraMap ℚ ℝ) G) := by
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, GroundTheory.Heights₂.Heights.LowerBoundFree.hFl]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_monomial, hR_monomial]
  rfl

def flR (F : RP Ψ N) : ℝ :=
  ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * F.coeff (permExp σ)

theorem degFl_eq_flR (F : RP Ψ N) : degFl F = flR (negX F) := by
  rw [degFl, flR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hd : (permExp σ).degree = dimFl Ψ N := Formalism.DegreeFormula.PPowSum.degree_permExp σ
  rw [coeff_negX, hd]
  ring

theorem flagInt_eq (G : GroundTheory.Heights₂.Heights.LowerBoundFree.RootPoly Ψ N) :
    ((GroundTheory.Heights₂.Heights.LowerBoundFree.flagInt Ψ N G : ℚ) : ℝ) = flR (map (algebraMap ℚ ℝ) G) := by
  rw [GroundTheory.Heights₂.Heights.LowerBoundFree.flagInt, GroundTheory.Heights₂.Heights.LowerBoundFree.antisym, coeff_sum,
    flR, Rat.cast_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hinj : Function.Injective (GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct Ψ N σ) := by
    rintro ⟨a, i⟩ ⟨b, k⟩ h
    simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp [(σ a).injective h]
  have hm : GroundTheory.Heights₂.Heights.LowerBoundFree.rhoMono Ψ N =
      (permExp σ).mapDomain (GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct Ψ N σ) := by
    ext ⟨τ, i⟩
    have : (τ, i) = GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct Ψ N σ (τ, (σ τ).symm i) := by
      simp [GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct]
    rw [this, Finsupp.mapDomain_apply hinj]
    simp [GroundTheory.Heights₂.Heights.LowerBoundFree.rhoMono, permExp, GroundTheory.Heights₂.Heights.LowerBoundFree.weylAct]
  rw [coeff_smul, hm, coeff_rename_mapDomain _ hinj, smul_eq_mul, Rat.cast_mul, coeff_map]
  congr 1
  simp [GroundTheory.Heights₂.Heights.LowerBoundFree.weylSign]

end Funs

section Test

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def muR (j : ℕ) : RP Ψ N := map (algebraMap ℚ ℝ) (GroundTheory.Heights₂.Heights.LowerBoundFree.muPoly Ψ N j)

def vR (j : ℕ) : RP Ψ N := map (algebraMap ℚ ℝ) (GroundTheory.Heights₂.Heights.LowerBoundFree.vandBlocks Ψ N j)

theorem muR_eq (j : ℕ) : (muR j : RP Ψ N) = ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), X (τ, i) := by
  rw [muR, GroundTheory.Heights₂.Heights.LowerBoundFree.muPoly, map_sum, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

theorem negX_muR (j : ℕ) : negX (muR j : RP Ψ N) = -muR j := by
  rw [muR_eq, negX, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_X]

theorem negX_fibClass (j : ℕ) : negX (fibClass j : RP Ψ N) = vR j := by
  rw [fibClass, vR, GroundTheory.Heights₂.Heights.LowerBoundFree.vandBlocks, negX, map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun ab _ => ?_
  simp only [map_sub, aeval_X, map_X]
  ring

def sAll : RP Ψ N := ∑ τ, pk τ 1

theorem muSmall_of_le {j : ℕ} (h : N - j ≤ j) : (muSmall j : RP Ψ N) = muR j := by
  rw [muSmall, if_pos h, muR_eq]

theorem muR_sub_muSmall {j : ℕ} (h : ¬ N - j ≤ j) : (muR j : RP Ψ N) - muSmall j = sAll := by
  rw [muSmall, if_neg h, muR_eq, sAll, sub_neg_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [pk, pkLow, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

theorem degFl_sAll_mul (Q : RP Ψ N) : degFl ((sAll : RP Ψ N) * Q) = 0 := by
  rw [sAll, Finset.sum_mul]
  refine Finset.sum_induction _ (fun x : RP Ψ N => degFl x = 0) ?_ ?_ ?_
  · intro a b ha hb
    rw [Model.degFl_add, ha, hb, add_zero]
  · simp [degFl]
  · intro τ _
    exact Model.degFl_pk_mul τ 1 le_rfl Q

theorem muR_homog (j : ℕ) : (muR j : RP Ψ N).IsHomogeneous 1 := by
  rw [muR_eq]
  exact IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X _ _

theorem muSmall_homog (j : ℕ) : (muSmall j : RP Ψ N).IsHomogeneous 1 := by
  by_cases h : N - j ≤ j
  · rw [muSmall_of_le h]; exact muR_homog j
  · rw [muSmall, if_neg h]
    refine IsHomogeneous.neg ?_
    refine IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => ?_
    rw [pow_one]
    exact isHomogeneous_X _ _

theorem fibClass_homog (j : ℕ) : ∃ d, (fibClass j : RP Ψ N).IsHomogeneous d := by
  refine ⟨_, IsHomogeneous.prod _ _ _ fun τ _ => IsHomogeneous.prod _ _ (fun _ => 1) fun ab _ => ?_⟩
  exact (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)

end Test

section Main

open GroundTheory.Heights₂.Heights.LowerBoundFree (FA Jint fib dimN)

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem dimN_eq (j : ℕ) : dimN Ψ N j = dimX Ψ N j := by
  rw [dimN, dimX, Nat.mul_assoc]

theorem negX_pow_mul (k j : ℕ) :
    negX ((muR j : RP Ψ N) ^ k * fibClass j) = ((-1 : ℝ) ^ k) • ((muR j : RP Ψ N) ^ k * vR j) := by
  rw [map_mul, map_pow, negX_muR, negX_fibClass, neg_pow, smul_eq_C_mul, map_pow, map_neg, map_one]
  ring

theorem map_FA (j : ℕ) (cf : ℚ) :
    map (algebraMap ℚ ℝ) (FA Ψ N j cf) = (cf : ℝ) • ((muR j : RP Ψ N) ^ (dimN Ψ N j + 1) * vR j) := by
  rw [FA, fib, map_mul, map_pow, map_mul, map_C, smul_eq_C_mul]
  change _ * (C ((cf : ℝ)) * _) = _
  rw [muR, vR]
  ring

theorem map_J (j : ℕ) (cf : ℚ) :
    map (algebraMap ℚ ℝ) ((GroundTheory.Heights₂.Heights.LowerBoundFree.muPoly Ψ N j) ^ (dimN Ψ N j) *
      fib Ψ N j cf) = (cf : ℝ) • ((muR j : RP Ψ N) ^ (dimN Ψ N j) * vR j) := by
  rw [fib, map_mul, map_pow, map_mul, map_C, smul_eq_C_mul]
  change _ * (C ((cf : ℝ)) * _) = _
  rw [muR, vR]
  ring

theorem hhFl_muR (II : IntersectionSystem) (j : ℕ) :
    hhFl Ψ N II ((muR j : RP Ψ N) ^ (dimX Ψ N j + 1) * fibClass j) =
      -GroundTheory.Heights₂.Heights.LowerBoundFree.hFl Ψ N II (FA Ψ N j ((-1) ^ dimX Ψ N j)) := by
  rw [hhFl_eq, negX_pow_mul, hFl_eq, map_FA, dimN_eq, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

theorem degFl_muR (j : ℕ) :
    degFl ((muR j : RP Ψ N) ^ dimX Ψ N j * fibClass j) = ((Jint Ψ N j ((-1) ^ dimX Ψ N j) : ℚ) : ℝ) := by
  rw [degFl_eq_flR, negX_pow_mul, Jint, flagInt_eq, map_J, dimN_eq]
  push_cast
  rfl

theorem testDeg_eq (j : ℕ) :
    testDeg Ψ N j = ((Jint Ψ N j ((-1) ^ dimX Ψ N j) : ℚ) : ℝ) := by
  rw [← degFl_muR, testDeg]
  by_cases h : N - j ≤ j
  · rw [muSmall_of_le h]
  · have e := geom_sum₂_mul (muR j : RP Ψ N) (muSmall j) (dimX Ψ N j)
    rw [muR_sub_muSmall h] at e
    have e2 : (muR j : RP Ψ N) ^ dimX Ψ N j * fibClass j = muSmall j ^ dimX Ψ N j * fibClass j +
        sAll * ((∑ i ∈ Finset.range (dimX Ψ N j), (muR j : RP Ψ N) ^ i * muSmall j ^ (dimX Ψ N j - 1 - i)) *
          fibClass j) := by
      rw [← mul_assoc, mul_comm sAll, e]
      ring
    rw [e2, Model.degFl_add, degFl_sAll_mul, add_zero]

theorem degree_count {j d : ℕ} (hn : dimX Ψ N j ≠ 0)
    (hT : (testPoly j : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1)) (hdeg : 0 < testDeg Ψ N j)
    (hf : (fibClass j : RP Ψ N).IsHomogeneous d) : dimX Ψ N j + d = dimFl Ψ N := by
  have h0 : (muSmall j : RP Ψ N) ^ dimX Ψ N j * fibClass j ≠ 0 := by
    intro h
    rw [testDeg, h] at hdeg
    simp [degFl] at hdeg
  have hM : (muSmall j : RP Ψ N) ≠ 0 := by
    intro h
    rw [h, zero_pow hn, zero_mul] at h0
    exact h0 rfl
  have hT0 : (testPoly j : RP Ψ N) ≠ 0 := by
    rw [testPoly, pow_succ', mul_assoc]
    exact mul_ne_zero hM h0
  have h2 : (testPoly j : RP Ψ N).IsHomogeneous (1 * (dimX Ψ N j + 1) + d) :=
    ((muSmall_homog j).pow _).mul hf
  have := h2.inj_right hT hT0
  omega

theorem hhFl_test (II : IntersectionSystem) {j d : ℕ}
    (hkill : ∀ τ (Q : RP Ψ N), Q.IsHomogeneous (dimFl Ψ N) → hhFl Ψ N II (pk τ 1 * Q) = 0)
    (hf : (fibClass j : RP Ψ N).IsHomogeneous d) (hd : dimX Ψ N j + d = dimFl Ψ N) :
    hhFl Ψ N II (testPoly j) = hhFl Ψ N II ((muR j : RP Ψ N) ^ (dimX Ψ N j + 1) * fibClass j) := by
  rw [testPoly]
  by_cases h : N - j ≤ j
  · rw [muSmall_of_le h]
  · have e := geom_sum₂_mul (muR j : RP Ψ N) (muSmall j) (dimX Ψ N j + 1)
    rw [muR_sub_muSmall h] at e
    set Q : RP Ψ N := (∑ i ∈ Finset.range (dimX Ψ N j + 1),
      (muR j : RP Ψ N) ^ i * muSmall j ^ (dimX Ψ N j + 1 - 1 - i)) * fibClass j with hQ
    have e2 : (muR j : RP Ψ N) ^ (dimX Ψ N j + 1) * fibClass j =
        muSmall j ^ (dimX Ψ N j + 1) * fibClass j + sAll * Q := by
      rw [hQ, ← mul_assoc, mul_comm sAll, e]
      ring
    have hQh : Q.IsHomogeneous (dimFl Ψ N) := by
      rw [← hd, hQ]
      refine IsHomogeneous.mul ?_ hf
      refine IsHomogeneous.sum _ _ _ fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      have := ((muR_homog (Ψ := Ψ) (N := N) j).pow i).mul ((muSmall_homog (Ψ := Ψ) (N := N) j).pow (dimX Ψ N j + 1 - 1 - i))
      have e3 : 1 * i + 1 * (dimX Ψ N j + 1 - 1 - i) = dimX Ψ N j := by omega
      rwa [e3] at this
    rw [e2, map_add, sAll, Finset.sum_mul, map_sum, Finset.sum_eq_zero fun τ _ => hkill τ Q hQh, add_zero]

end Main

theorem hhTestBound_hhFl : GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement → PB.Inputs →
    ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
      [Nonempty Ψ] (j : ℕ), 1 ≤ j → j < N → HhTestBound j (hhFl Ψ N II) := by
  intro hZ2 _ II hII Ψ _ _ N _ j hj hjN
  have hN : 2 ≤ N := by omega
  obtain ⟨hT, hdeg, -, -⟩ := GlobalTheory.T.test_polynomial_shift_total Ψ N j hj hjN
  have hA : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) := by
    have := (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
    rwa [GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right] at this
  have hkill : ∀ τ (Q : RP Ψ N), Q.IsHomogeneous (dimFl Ψ N) → hhFl Ψ N II (pk τ 1 * Q) = 0 :=
    fun τ Q hQ => GlobalTheory.T.flag_height_power_sum_one_zero II hII Ψ N τ Q hN hA hQ
  have hn : dimX Ψ N j ≠ 0 := by
    have h1 : 0 < Fintype.card Ψ := Fintype.card_pos
    have h2 : 0 < N - j := by omega
    exact (Nat.mul_pos h1 (Nat.mul_pos (by omega) h2)).ne'
  obtain ⟨d, hf⟩ := fibClass_homog (Ψ := Ψ) (N := N) j
  have hd := degree_count hn hT hdeg hf
  have hJ := testDeg_eq (Ψ := Ψ) (N := N) j
  have hJ0 : 0 < GroundTheory.Heights₂.Heights.LowerBoundFree.Jint Ψ N j ((-1) ^ dimX Ψ N j) := by
    rw [hJ] at hdeg
    exact_mod_cast hdeg
  have hb := hZ2 II Ψ N j ((-1) ^ dimX Ψ N j) (((min j (N - j) : ℕ) : ℝ) / 2 * Real.log ((N : ℝ) + 1))
    hII.1 hN hj (by omega) hJ0
    (fun Z hZ => half_log_det_le (by omega) Z hZ)
  rw [HhTestBound, hhFl_test II hkill hf hd, hhFl_muR, hJ]
  rw [dimN_eq] at hb
  refine hb.trans (le_of_eq ?_)
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Top.HhTestProof
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_test_bound : GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (j : ℕ), 1 ≤ j → j < N → HhTestBound j (hhFl Ψ N II) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.HhTestProof.hhTestBound_hhFl
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem mean_slope_of_volume_eq : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval :=
  @RootFieldNumerics.mean_slope_of_proportional_volume

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_slope_proportional_volume : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem thmB_functional : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh :=
  @RootFieldNumerics.antisymmetry_tower_theorem

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_theorem_B : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.thmB_functional
end

section
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flag_integral_permutations : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∀ (τ : Ψ) (a b : Fin N) (F : RP Ψ N), a ≠ b → degFl (rename (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) F) = -degFl F) ∧ ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F ∧ ∀ (j : ℕ) (τ : Ψ), Sh j (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Sh j τ F ∧ Tot (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Tot τ F :=
  @RootFieldNumerics.degFl_symmetry_invariance

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_symmetries : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∀ (τ : Ψ) (a b : Fin N) (F : RP Ψ N), a ≠ b → degFl (rename (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) F) = -degFl F) ∧ ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F ∧ ∀ (j : ℕ) (τ : Ψ), Sh j (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Sh j τ F ∧ Tot (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Tot τ F := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.flag_integral_permutations
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem sum_group_apply_eq {Ψ : Type} (Γ : Subgroup (Equiv.Perm Ψ)) [Fintype Γ]
    (htr : ∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') (f : Ψ → ℝ) (τ τ' : Ψ) :
    ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ) = ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ') := by
  obtain ⟨ρ, hρ, rfl⟩ := htr τ' τ
  exact Fintype.sum_equiv (Equiv.mulRight (⟨ρ, hρ⟩ : Γ)) _ _ (fun g => by simp [Equiv.Perm.mul_apply])

theorem exists_group_mean {Ψ : Type} (Γ : Subgroup (Equiv.Perm Ψ)) [Fintype Γ]
    (htr : ∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') (f : Ψ → ℝ) :
    ∃ A : ℝ, ∀ τ, ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ) = (Fintype.card Γ : ℝ) * A := by
  rcases isEmpty_or_nonempty Ψ with h | ⟨⟨τ₀⟩⟩
  · exact ⟨0, fun τ => (h.false τ).elim⟩
  · have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    refine ⟨(∑ g : Γ, f ((g : Equiv.Perm Ψ) τ₀)) / (Fintype.card Γ : ℝ), fun τ => ?_⟩
    rw [mul_div_cancel₀ _ hc]
    exact sum_group_apply_eq Γ htr f τ τ₀

theorem mean_estimate {G Ψ : Type} [Fintype G] [Nonempty G] [Fintype Ψ] (P V H bd A Bs : ℝ) (S U : Ψ → ℝ)
    (a b : G → Ψ → ℝ) (hA : ∀ τ, ∑ g, a g τ = (Fintype.card G : ℝ) * A)
    (hB : ∀ τ, ∑ g, b g τ = (Fintype.card G : ℝ) * Bs)
    (h : ∀ g, |P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)| ≤ bd) :
    |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)| ≤ bd := by
  have hn : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card G : ℝ) with hndef
  have h1 : ∑ g, ∑ τ, (a g τ - b g τ) * S τ = n * ((A - Bs) * ∑ τ, S τ) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hA, hB]
    ring
  have h2 : ∑ g, ∑ τ, b g τ * U τ = n * (Bs * ∑ τ, U τ) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_mul, hB]
    ring
  have key : ∑ g : G, (P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)) =
      n * (P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)) := by
    have : ∀ g : G, P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ) =
        (P - V * H) + V * ∑ τ, (a g τ - b g τ) * S τ + V * ∑ τ, b g τ * U τ := fun g => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [← hndef]
    ring
  have hle : n * |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)| ≤ n * bd := by
    calc n * |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)|
        = |n * (P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ))| := by
          rw [abs_mul, abs_of_pos hn]
      _ = |∑ g : G, (P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ))| := by rw [key]
      _ ≤ ∑ g : G, |P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g : G, bd := Finset.sum_le_sum fun g _ => h g
      _ = n * bd := by simp [hndef]
  exact le_of_mul_le_mul_left hle hn

theorem thmBA_of_thmB_propA : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.ThmB II hh → T.PropA II →
    LabelInv (Ψ := Ψ) (N := N) hh → T.ThmBA II hh := by
  intro II Ψ _ _ N T hh hB hA hL
  obtain ⟨C, B₁, hC⟩ := hB
  obtain ⟨Γ, htr, hinv⟩ := hA
  have : Fintype Γ := Fintype.ofFinite _
  refine ⟨C, max B₁ 2, fun B hBge => ?_⟩
  obtain ⟨α, β, hm⟩ := hC B (le_trans (le_max_left _ _) hBge)
  obtain ⟨A, hAm⟩ := exists_group_mean Γ htr α
  obtain ⟨Bs, hBm⟩ := exists_group_mean Γ htr β
  refine ⟨A, Bs, fun m hdeg => ?_⟩
  refine mean_estimate (G := Γ) _ _ _ _ A Bs _ _ (fun g τ => α ((g : Equiv.Perm Ψ) τ))
    (fun g τ => β ((g : Equiv.Perm Ψ) τ)) hAm hBm fun g => ?_
  set F : RP Ψ N := monomial m 1 with hF
  set φ : Ψ × Fin N → Ψ × Fin N := fun x => ((g : Equiv.Perm Ψ) x.1, x.2) with hφ
  have hR : (monomial (m.mapDomain φ) 1 : RP Ψ N) = rename φ F := (rename_monomial φ m 1).symm
  have hest := hm (m.mapDomain φ) (by rw [Finsupp.degree_mapDomain]; exact hdeg)
  have anti := fun τ j => ((GlobalTheory.T.flag_degree_symmetries Ψ N).2 (g : Equiv.Perm Ψ) F).2 j τ
  have hS : ∑ τ, (α τ - β τ) * Sh T.j τ (rename φ F) =
      ∑ τ, (α ((g : Equiv.Perm Ψ) τ) - β ((g : Equiv.Perm Ψ) τ)) * Sh T.j τ F := by
    rw [← Equiv.sum_comp (g : Equiv.Perm Ψ)]
    exact Finset.sum_congr rfl fun τ _ => by rw [(anti τ T.j).1]
  have hU : ∑ τ, β τ * Tot τ (rename φ F) = ∑ τ, β ((g : Equiv.Perm Ψ) τ) * Tot τ F := by
    rw [← Equiv.sum_comp (g : Equiv.Perm Ψ)]
    exact Finset.sum_congr rfl fun τ _ => by rw [(anti τ T.j).2]
  rw [hR, hS, hU, hinv g g.2 B (le_trans (le_max_right _ _) hBge) F, hL g F] at hest
  exact hest

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_theorem_B_averaged : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.ThmB II hh → T.PropA II → LabelInv (Ψ := Ψ) (N := N) hh → T.ThmBA II hh := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA
end

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem gap_nonneg_of_dominant {Ψ : Type} [Fintype Ψ] {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N)
    {mu : Wt Ψ N} (hd : Dominant mu) (τ : Ψ) : 0 ≤ gap j mu τ := by
  have h1 : j - 1 < N := by omega
  have hle : mu τ ⟨j, hjN⟩ ≤ mu τ ⟨j - 1, h1⟩ := hd τ ⟨j - 1, h1⟩ ⟨j, hjN⟩ (by rw [Fin.mk_le_mk]; omega)
  simp only [gap, ent, dif_pos h1, dif_pos hjN]
  exact sub_nonneg.mpr hle

theorem NefThreshold.mono {Ψ : Type} [Fintype Ψ] {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N)
    {mu : Wt Ψ N} (hd : Dominant mu) {b b' : ℝ} (hb : b ≤ b') (h : NefThreshold j b mu) :
    NefThreshold j b' mu := by
  intro τ
  have hg : 0 ≤ gap j mu τ := gap_nonneg_of_dominant hj1 hjN hd τ
  calc 4 * (Fintype.card Ψ : ℝ) * ‖mu‖ ≤ (b - 2) * gap j mu τ := h τ
    _ ≤ (b' - 2) * gap j mu τ := mul_le_mul_of_nonneg_right (by linarith) hg

theorem RootTower.nefFib_of_nefThreshold :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.ModelNefStatement → T.M2 →
      ∀ (B : ℕ) (c : T.Comp) (mu : Wt Ψ N), Dominant mu → NefThreshold T.j B mu →
        (T.M B c).NefFib mu 0 := by
  intro Ψ _ _ N T h1 h2 B c mu hd hB p hp
  by_cases hS : T.InS B p
  · exact h1 B c p hS mu hd
  · have hBp : B < p := by
      by_contra hc
      exact hS (show p.Prime ∧ (p ≤ B ∨ p ∈ T.bad) from ⟨hp, Or.inl (not_lt.mp hc)⟩)
    refine h2 B c p hp hS mu hd ?_
    exact NefThreshold.mono T.j_pos T.j_lt hd (by exact_mod_cast hBp.le) hB

end GlobalTheory.CompanionTheory.Ar.Top
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem RootTower.tower_I3_of_nef_inputs :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I3 := by
  intro Ψ _ _ N T hA1 hM1 hM2 hAN abelian₂
  obtain ⟨s₀, hs₀, h⟩ := hA1 abelian₂
  refine ⟨s₀, hs₀, fun B hB c lam s hl hs hss hd ht => ⟨?_, h B hB c lam s hl hs hss hd⟩⟩
  intro p hp
  have hn := RootTower.nefFib_of_nefThreshold Ψ N T hM1 hM2 B c (T.lamS lam s) hd ht p hp
  exact (GlobalTheory.T.curve_degree_linear_nef_cone Ψ N (T.M B c) (T.lamS lam s) 0 s 0 0).2.2.1 p hs.le hn (hAN B c p hp)

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_I3_of_semipositive_nef : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I3 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flag_gap_eq_sub {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam : Wt Ψ N) (τ : Ψ) (a : Fin N)
    (h : (a : ℕ) + 1 < N) :
    PB.gap (fun x : Ψ × Fin N => lam x.1 x.2) (τ, a) = lam τ a - lam τ ⟨(a : ℕ) + 1, h⟩ := by
  simp [PB.gap, PB.gapX, h]

theorem flag_dim_eq_antisymmetric_degree (Ψ : Type) [Fintype Ψ] (N : ℕ) :
    dimFl Ψ N = GroundTheory.Heights₂.Heights.antisymDegree Ψ N := by
  simp [dimFl, GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right]

theorem flag_height_I9 : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N →
      I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  intro hFH hIn II hII Ψ _ _ N _ hN
  have hA : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) := by
    rw [flag_dim_eq_antisymmetric_degree]
    exact (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  have hev : ∀ lam : Wt Ψ N, hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) =
      eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := fun lam =>
    GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N lam hN hA
  obtain ⟨-, hgap, hdom⟩ := hFH hIn II hII Ψ N hN
  refine ⟨?_, ?_, ?_⟩
  · rintro lam - ⟨τ, a, b, hab, heq⟩
    have h : (a : ℕ) + 1 < N := hab ▸ b.2
    have hb : b = ⟨(a : ℕ) + 1, h⟩ := Fin.ext hab
    rw [hev]
    refine hgap _ (τ, a) h ?_
    rw [flag_gap_eq_sub lam τ a h, ← hb, heq, sub_self]
  · intro lam hlam
    rw [hev]
    refine hdom _ fun p hp => ?_
    obtain ⟨τ, a⟩ := p
    rw [flag_gap_eq_sub lam τ a hp, sub_nonneg]
    exact hlam τ a ⟨(a : ℕ) + 1, hp⟩ (Fin.le_def.2 (Nat.le_succ _))
  · intro τ Q hQ
    exact GlobalTheory.T.flag_height_power_sum_one_zero II hII Ψ N τ Q hN hA hQ

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_I9_properties : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N → I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace LimitVolumeRatio

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem linRoot_sub_smul (lam nu : Wt Ψ N) (s : ℝ) :
    linRoot (lam - s • nu) = linRoot lam - C s * linRoot nu := by
  simp only [linRoot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_neg, mul_assoc]
  ring

theorem linA_lamS (T : RootTower Ψ N) (u : Wt Ψ N) (s : ℝ) :
    linA (T.lamS u s) s = toA (linRoot u) + C s * (X none - toA (linRoot T.nu)) := by
  simp only [linA, RootTower.lamS, linRoot_sub_smul, toA, map_sub, map_mul, rename_C]
  ring

theorem cont_pow (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (P0 P1 : RPA Ψ N) (d : ℕ) :
    Continuous fun s : ℝ => Φ ((P0 + C s * P1) ^ d) := by
  have h : ∀ s : ℝ, Φ ((P0 + C s * P1) ^ d) =
      ∑ m ∈ Finset.range (d + 1), s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) := by
    intro s
    rw [add_pow, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) =
      Φ (s ^ (d - m) • (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N))) by rw [map_smul, smul_eq_mul]]
    congr 1
    rw [MvPolynomial.smul_eq_C_mul, mul_pow, ← map_pow]
    ring
  rw [show (fun s : ℝ => Φ ((P0 + C s * P1) ^ d)) = fun s : ℝ => ∑ m ∈ Finset.range (d + 1),
      s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) from funext h]
  exact continuous_finset_sum _ fun m _ => (continuous_pow _).mul continuous_const

theorem tendsto_lin (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (T : RootTower Ψ N) (u : Wt Ψ N) (d : ℕ) :
    Tendsto (fun s => Φ (linA (T.lamS u s) s ^ d)) (𝓝[>] 0) (𝓝 (Φ (toA (linRoot u ^ d)))) := by
  have hc := (cont_pow Φ (toA (linRoot u)) (X none - toA (linRoot T.nu)) d).tendsto 0
  simp only [map_zero, zero_mul, add_zero] at hc
  rw [show toA (linRoot u ^ d) = toA (linRoot u) ^ d by simp [toA, map_pow]]
  exact (hc.mono_left nhdsWithin_le_nhds).congr fun s => by rw [linA_lamS]

theorem gap_sub_smul (j : ℕ) (lam nu : Wt Ψ N) (s : ℝ) (τ : Ψ) :
    gap j (lam - s • nu) τ = gap j lam τ - s * gap j nu τ := by
  simp only [gap, ent]
  split_ifs <;> simp <;> ring

end LimitVolumeRatio

end GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace LimitVolumeRatio

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem eventually_dominant (T : RootTower Ψ N) (u : Wt Ψ N) (hu : RegDominant u) :
    ∀ᶠ s in 𝓝 (0 : ℝ), Dominant (T.lamS u s) := by
  have key : ∀ τ (a b : Fin N), ∀ᶠ s in 𝓝 (0 : ℝ), a ≤ b → (T.lamS u s) τ b ≤ (T.lamS u s) τ a := by
    intro τ a b
    by_cases hab : a < b
    · have h1 : Tendsto (fun s : ℝ => u τ b - s * T.nu τ b) (𝓝 0) (𝓝 (u τ b - 0 * T.nu τ b)) :=
        (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0
      have h2 : Tendsto (fun s : ℝ => u τ a - s * T.nu τ a) (𝓝 0) (𝓝 (u τ a - 0 * T.nu τ a)) :=
        (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0
      filter_upwards [h1.eventually_lt h2 (by simpa using hu τ a b hab)] with s hs _
      simpa [RootTower.lamS] using hs.le
    · exact Eventually.of_forall fun s h => by
        have : a = b := le_antisymm h (not_lt.mp hab)
        subst this
        exact le_rfl
  exact eventually_all.2 fun τ => eventually_all.2 fun a => eventually_all.2 fun b => key τ a b

theorem eventually_threshold [Nonempty Ψ] (T : RootTower Ψ N) (u : Wt Ψ N) (g : ℝ) (hw : WeightHyp T.j u g)
    (B : ℕ) (hB : bigB0 u g < B + 1) :
    ∀ᶠ s in 𝓝 (0 : ℝ), NefThreshold T.j B (T.lamS u s) := by
  have hF : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by have := T.j_pos; have := T.j_lt; omega)
  have hg : 0 < g := hw.1
  have hx : 0 ≤ ‖u‖ := norm_nonneg _
  set F : ℝ := (Fintype.card Ψ : ℝ)
  set x : ℝ := ‖u‖
  have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hB' : 4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3 < (B : ℝ) - 2 := by
    simp only [bigB0] at hB
    nlinarith
  have hxg : x / g * g = x := div_mul_cancel₀ x hg.ne'
  have hFN : (4 : ℝ) ≤ F * (N : ℝ) ^ 2 := by
    have := mul_le_mul hF hn2 (by norm_num) (by linarith)
    linarith
  have hpos : 0 < 4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3 := by
    have : 0 ≤ x / g := div_nonneg hx hg.le
    have h' : 0 ≤ 4 * F * (N : ℝ) ^ 2 * (x / g) := mul_nonneg (by positivity) this
    linarith
  have hB2 : 0 ≤ (B : ℝ) - 2 := by linarith
  have at0 : ∀ τ, 4 * F * x < ((B : ℝ) - 2) * gap T.j u τ := by
    intro τ
    have h1 : ((B : ℝ) - 2) * g ≤ ((B : ℝ) - 2) * gap T.j u τ :=
      mul_le_mul_of_nonneg_left (hw.2.2.1 τ) hB2
    have h2 := mul_lt_mul_of_pos_right hB' hg
    have h3 : (4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3) * g =
        4 * F * (N : ℝ) ^ 2 * g + 4 * F * (N : ℝ) ^ 2 * x - 3 * g := by
      rw [sub_mul, add_mul, mul_assoc (4 * F * (N : ℝ) ^ 2), hxg]
    have h4 : 4 * F * x ≤ 4 * F * (N : ℝ) ^ 2 * x := by
      have e : 4 * F * (N : ℝ) ^ 2 * x - 4 * F * x = (4 * F * x) * ((N : ℝ) ^ 2 - 1) := by ring
      have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * F) hx) (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ 2 - 1)
      linarith
    have h5 : 0 < 4 * F * (N : ℝ) ^ 2 * g - 3 * g := by
      have e : 4 * F * (N : ℝ) ^ 2 * g - 3 * g = g * (4 * (F * (N : ℝ) ^ 2) - 3) := by ring
      rw [e]
      exact mul_pos hg (by linarith)
    linarith
  have key : ∀ τ, ∀ᶠ s in 𝓝 (0 : ℝ), 4 * F * ‖T.lamS u s‖ ≤ ((B : ℝ) - 2) * gap T.j (T.lamS u s) τ := by
    intro τ
    have h1 : Tendsto (fun s : ℝ => 4 * F * ‖T.lamS u s‖) (𝓝 0) (𝓝 (4 * F * ‖T.lamS u 0‖)) :=
      ((continuous_const.mul (continuous_const.sub (continuous_id.smul continuous_const)).norm)).tendsto 0
    have h2 : Tendsto (fun s : ℝ => ((B : ℝ) - 2) * (gap T.j u τ - s * gap T.j T.nu τ)) (𝓝 0)
        (𝓝 (((B : ℝ) - 2) * (gap T.j u τ - 0 * gap T.j T.nu τ))) :=
      (continuous_const.mul (continuous_const.sub (continuous_id.mul continuous_const))).tendsto 0
    have h0 : 4 * F * ‖T.lamS u 0‖ < ((B : ℝ) - 2) * (gap T.j u τ - 0 * gap T.j T.nu τ) := by
      simpa [RootTower.lamS] using at0 τ
    filter_upwards [h1.eventually_lt h2 h0] with s hs
    rw [RootTower.lamS, gap_sub_smul]
    exact hs.le
  exact eventually_all.2 key

theorem tower_T1_limit_of_inputs : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ]
    (T : RootTower Ψ N), T.Proportional → T.I2 II → T.I3 → T.T1 II := by
  intro II Ψ _ _ N _ T hProp hI2 hI3 u g hw B hB c
  have hF : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by have := T.j_pos; have := T.j_lt; omega)
  have hB2 : 2 ≤ B := by
    have hq : 0 ≤ ‖u‖ / g := div_nonneg (norm_nonneg _) hw.1.le
    have : (16 : ℝ) ≤ bigB0 u g := by
      simp only [bigB0]
      have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      have hFN : (4 : ℝ) ≤ (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2 := by nlinarith
      have h1q : (1 : ℝ) ≤ 1 + ‖u‖ / g := by linarith
      have := mul_le_mul hFN h1q zero_le_one (by positivity)
      nlinarith
    have : (15 : ℝ) < B := by linarith
    exact_mod_cast (show (2 : ℝ) ≤ B by linarith)
  have hdom := eventually_dominant T u hw.2.1
  have hthr := eventually_threshold T u g hw B hB
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := eventually_mem_nhdsWithin

  obtain ⟨s₁, hs₁, C₂, hag⟩ := hI2 (l1 u)
  have hdiff : Tendsto (fun s => T.mbarTop II B c u s - T.PBs II B c (T.lamS u s) s) (𝓝[>] 0) (𝓝 0) := by
    have hlin : Tendsto (fun s : ℝ => C₂ * s) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlin
    filter_upwards [hpos, (eventually_le_nhds hs₁).filter_mono nhdsWithin_le_nhds,
      hdom.filter_mono nhdsWithin_le_nhds] with s h0 h1 h2
    exact hag B hB2 c u s le_rfl h0 h1 h2
  have hPB : Tendsto (fun s => T.PBs II B c (T.lamS u s) s) (𝓝[>] 0)
      (𝓝 (T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)))) :=
    LimitVolumeRatio.tendsto_lin ((T.M B c).PP II) T u (dimFl Ψ N + 1)
  have hbar : Tendsto (fun s => T.mbarTop II B c u s) (𝓝[>] 0)
      (𝓝 (T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)))) := by
    have h := hPB.add hdiff
    rw [add_zero] at h
    exact h.congr fun s => by ring
  have hdeg : Tendsto (fun s => T.mDeg B c u s) (𝓝[>] 0) (𝓝 (T.vol c * flagDeg u)) := by
    have h := LimitVolumeRatio.tendsto_lin (T.M B c).geoFun T u (dimFl Ψ N)
    rwa [hProp.2.1 B c] at h
  have hvpos : 0 < T.vol c * flagDeg u :=
    mul_pos (hProp.1 c) ((flagDeg_eq_weyl Ψ N u).2.1 hw.2.1)
  refine ⟨?_, hbar, hdeg, hvpos, ?_⟩
  · obtain ⟨s₀, hs₀, h3⟩ := hI3 (l1 u)
    filter_upwards [hpos, (eventually_le_nhds hs₀).filter_mono nhdsWithin_le_nhds,
      hdom.filter_mono nhdsWithin_le_nhds, hthr.filter_mono nhdsWithin_le_nhds] with s h0 h1 h2 h4
    exact h3 B hB2 c u s le_rfl h0 h1 h2 h4
  · have hne : ((dimFl Ψ N : ℝ) + 1) * (T.vol c * flagDeg u) ≠ 0 :=
      (mul_pos (by positivity) hvpos).ne'
    exact hbar.div (hdeg.const_mul _) hne

end LimitVolumeRatio

end GlobalTheory.CompanionTheory.Ar.Top
end
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_T1_limit : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N), T.Proportional → T.I2 II → T.I3 → T.T1 II := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.LimitVolumeRatio.tower_T1_limit_of_inputs
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem chain_tower : PB.FlagHeight → PB.Inputs → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound →
    GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement →
    ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    [Nonempty Ψ] (T : RootTower Ψ N) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C C' rd Lval : ℝ), 0 ≤ C → 0 ≤ C' → 1 ≤ rd →
    FrobShape frob → T.Proportional → T.I1 II → T.I2 II → T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I5 II → T.I6 II →
    T.I7 → T.I8 II (hhFl Ψ N II) → T.Prop6 II frob → T.PropA II → T.PropF II C' rd Lval → T.VolEq →
    T.SlopeLower II C rd Lval → T.T1 II ∧ T.ThmB II (hhFl Ψ N II) ∧ T.T2 II (2 * C + 3 * C' + 5) rd Lval ∧
      T.MeanSlope II (2 * C + 3 * C' + 5) rd Lval := by
  intro hFH hIn hZ1 hZ2 hAP hG II hII Ψ _ _ N _ T frob C C' rd Lval hC hC' hrd hfs hP hI1 hI2 hA1 hM1 hM2 hAN
    hI5 hI6 hI7 hI8 hP6 hPA hPF hVol hSL
  have hN : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  have hI3 : T.I3 := GlobalTheory.T.tower_I3_of_semipositive_nef Ψ N T hA1 hM1 hM2 hAN
  have hT1 : T.T1 II := GlobalTheory.T.tower_T1_limit II Ψ N T hP hI2 hI3
  have hW : T.ThmW II := GlobalTheory.T.tower_weil_theorem hIn.2.2.2.2.2.1 GlobalTheory.T.exists_unique_rational_statement GlobalTheory.CompanionTheory.Ar.Link.divSuppArith_holds hZ1 hZ2
    II hII Ψ N T hP hI1 hI2 hI3 hI5 hI6 hI7
  have hI9 : I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := GlobalTheory.T.flag_height_I9_properties hFH hIn II hII Ψ N hN
  have hB : T.ThmB II (hhFl Ψ N II) := GlobalTheory.T.tower_theorem_B hAP II Ψ N T (hhFl Ψ N II) hP hW hI8 hI9
  have he : GroundTheory.Heights₂.Heights.antisymDegree Ψ N = dimFl Ψ N := by
    simp [GroundTheory.Heights₂.Heights.antisymDegree, dimFl, Nat.choose_two_right]
  have hAr := (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  rw [he] at hAr
  have hLab : LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := GlobalTheory.T.flag_height_label_invariant II hII Ψ N hN hAr
  have hBA : T.ThmBA II (hhFl Ψ N II) := GlobalTheory.T.tower_theorem_B_averaged II Ψ N T (hhFl Ψ N II) hB hPA hLab
  have hTest : HhTestBound T.j (hhFl Ψ N II) := GlobalTheory.T.flag_height_test_bound hG hIn II hII Ψ N T.j T.j_pos T.j_lt
  have hA0 : T.LowerBoundAtBase II (hhFl Ψ N II) frob (2 * (C + C') + 3) rd Lval :=
    GlobalTheory.T.test_height_bound II Ψ N T (hhFl Ψ N II) frob C C' rd Lval hC hC' hrd hP hI9 hPF hSL hTest
  have hK : (0 : ℝ) ≤ 2 * (C + C') + 3 := by linarith
  have hT2' := GlobalTheory.T.tower_T2 II Ψ N T (hhFl Ψ N II) frob (2 * (C + C') + 3) C' rd Lval hK hC' hrd hP hfs hI9 hP6
    hBA hPF hA0
  have hEq : 2 * (C + C') + 3 + C' + 2 = 2 * C + 3 * C' + 5 := by ring
  rw [hEq] at hT2'
  exact ⟨hT1, hB, hT2', GlobalTheory.T.mean_slope_proportional_volume II Ψ N T _ rd Lval hP hVol hT2'⟩

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_weil_inputs_combined : PB.FlagHeight → PB.Inputs → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C C' rd Lval : ℝ), 0 ≤ C → 0 ≤ C' → 1 ≤ rd → FrobShape frob → T.Proportional → T.I1 II → T.I2 II → T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I5 II → T.I6 II → T.I7 → T.I8 II (hhFl Ψ N II) → T.Prop6 II frob → T.PropA II → T.PropF II C' rd Lval → T.VolEq → T.SlopeLower II C rd Lval → T.T1 II ∧ T.ThmB II (hhFl Ψ N II) ∧ T.T2 II (2 * C + 3 * C' + 5) rd Lval ∧ T.MeanSlope II (2 * C + 3 * C' + 5) rd Lval := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.chain_tower
end
