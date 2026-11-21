import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionUnitaryLeviRadicalActionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement

section
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartUnip

open Matrix

theorem rat_Tm {D : D7} (A : HSp D) (μ : D.host.E) :
    (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (Matrix.fromCols (dblDec A).jX (incA D μ • (dblDec A).jY)).submatrix id finSumFinEquiv.symm := by
  ext i j
  rcases h : finSumFinEquiv.symm j with k | k <;>
    simp [rat, Tm, HypDec.jX, HypDec.jY, Matrix.submatrix_apply, h, Matrix.map_apply]

theorem cancel_mul {R : Type*} [CommRing R] {k a m : ℕ} {P : Matrix (Fin k) (Fin (m + m)) R}
    {M : Matrix (Fin k) (Fin a) R} {N : Matrix (Fin a) (Fin m ⊕ Fin m) R}
    (h : P = M * N.submatrix id finSumFinEquiv.symm) : P.submatrix id finSumFinEquiv = M * N := by
  subst h
  ext i s
  simp [Matrix.mul_apply, Matrix.submatrix_apply]

theorem unscale {R : Type*} [CommRing R] {k m : ℕ} {X Y Z : Matrix (Fin k) (Fin m) R} {b : Matrix (Fin m) (Fin m) R}
    {u v : R} (huv : u * v = 1) (h : X * b + v • Y = v • Z) : Z = Y + X * (u • b) := by
  have h3 := congrArg (fun M => u • M) h
  simp only [smul_add, smul_smul, huv, one_smul] at h3
  rw [Matrix.mul_smul, add_comm, h3]

theorem skew_of_image {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S) (c : Mx D ρ ρ)
    (hY : mt S g ⬝ d.jY = d.jY + d.jX ⬝ c) : c ∈ skewA D ρ := by
  have h0 : adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ (mt S g ⬝ d.jY)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ (mt_unitary S g), d.gram_YY]
  rw [hY] at h0
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY,
    d.gram_XY, cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add] at h0
  exact mem_skewA.2 (eq_neg_of_add_eq_zero_left h0)

theorem chart_unip : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (g : GA D (dblSp A)) (b : Mx D A.rank A.rank), mat (κ g) = blk4 1 b 0 1 →
    ∃ c : skewA D A.rank, c.1 = incA D μ⁻¹ • b ∧ g = (dblDec A).nC c := by
  intro D A μ hμ κ hκ g b hg
  have hT := hκ g
  rw [hg, rat_Tm, blk4, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks] at hT
  have hT' := cancel_mul hT
  rw [mul_fromCols, Matrix.submatrix_submatrix, Function.comp_id, Equiv.symm_comp_self, Matrix.submatrix_id_id] at hT'
  obtain ⟨h1, h2⟩ := fromCols_inj hT'
  rw [Matrix.mul_one, Matrix.mul_zero, add_zero] at h1
  rw [Matrix.mul_one, Matrix.mul_smul] at h2
  have hunit : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ.1, map_one]
  have hX : mt (dblSp A) g ⬝ (dblDec A).jX = (dblDec A).jX := h1.symm
  have hY : mt (dblSp A) g ⬝ (dblDec A).jY = (dblDec A).jY + (dblDec A).jX ⬝ (incA D μ⁻¹ • b) :=
    unscale hunit h2
  refine ⟨⟨incA D μ⁻¹ • b, skew_of_image (dblDec A) g _ hY⟩, rfl, ?_⟩
  refine (dblDec A).ga_ext ?_ (Matrix.ext fun _ j => Fin.elim0 j) ?_
  · rw [hX, HypDec.nC_jX]
  · rw [hY, HypDec.nC_jY]

end GlobalTheory.ChartUnip
end

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardUnitaryChart_unipotent_eq_wittUnipotent : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (g : GA D (dblSp A)) (b : Mx D A.rank A.rank), mat (κ g) = blk4 1 b 0 1 → ∃ c : skewA D A.rank, c.1 = incA D μ⁻¹ • b ∧ g = (dblDec A).nC c := by
  atlas_forward_decl GlobalTheory.ChartUnip.chart_unip
end

section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Unip

theorem trace_algebraMap_mul_gen {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (a : R) (t : S) :
    Algebra.trace R S (algebraMap R S a * t) = a * Algebra.trace R S t := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem trace_mul_smul_gen {R : Type} [CommRing R] {n : ℕ} (s : R) (T b : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (T * (s • b)) = s * Matrix.trace (b * T) := by
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

theorem incA_xiZero_mul_inv_eq_algebraMap_neg (D : D7) (μ : D.host.E) (lam : D.host.F)
    (hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ) :
    incA D D.host.xi0 * incA D μ⁻¹ =
      algebraMap (AF D.host.F) (AE D) (-algebraMap D.host.F (AF D.host.F) lam) := by
  have hxm : D.host.xi0 * μ⁻¹ = -algebraMap D.host.F D.host.E lam := by
    rw [hlam, neg_div, neg_neg, div_eq_mul_inv]
  have hinc : incA D (algebraMap D.host.F D.host.E lam) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) lam) := by
    show (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] AF D.host.F ⊗[D.host.F] D.host.E)
      (algebraMap D.host.F D.host.E lam) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E)]
  rw [← map_mul, hxm, map_neg, hinc, map_neg]

theorem neg_trHalf_eq (D : D7) (μ : D.host.E) (lam : D.host.F)
    (hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ) (t : AE D) :
    -(trHalf D (incA D μ⁻¹ * t)) = algebraMap D.host.F (AF D.host.F) lam * halfTr t := by
  have h1 : Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D μ⁻¹ * t)) =
      -algebraMap D.host.F (AF D.host.F) lam * Algebra.trace (AF D.host.F) (AE D) t :=
    (congrArg (Algebra.trace (AF D.host.F) (AE D)) ((mul_assoc _ _ t).symm.trans
      (congrArg (· * t) (incA_xiZero_mul_inv_eq_algebraMap_neg D μ lam hlam)))).trans (trace_algebraMap_mul_gen _ t)
  have h2 : ∀ h a z : AF D.host.F, -(h * (-a * z)) = a * (h * z) := fun h a z => by ring
  exact (congrArg (fun y => -(algebraMap D.host.F (AF D.host.F) (1 / 2) * y)) h1).trans (h2 _ _ _)

theorem chr_eq_shift (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (μ : D.host.E) (lam : D.host.F)
    (hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ) {n : ℕ} (T b : Mx D n n) (c : skewA D n)
    (hc : c.1 = incA D μ⁻¹ • b) :
    chr ψ T c = shift ψ lam (halfTr (Matrix.trace (b ⬝ T : Mx D n n))) := by
  have h1 : Matrix.trace (T ⬝ c.1 : Mx D n n) = incA D μ⁻¹ * Matrix.trace (b ⬝ T : Mx D n n) :=
    (congrArg (fun y : Mx D n n => Matrix.trace (T ⬝ y : Mx D n n)) hc).trans (trace_mul_smul_gen _ T b)
  exact congrArg ψ ((congrArg (fun y => -(trHalf D y)) h1).trans (neg_trHalf_eq D μ lam hlam _))

theorem transport_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ (g : G D A.rank) (b : Mx D A.rank A.rank), mat g = blk4 1 b 0 1 → ∀ Φ x, (omS g Φ).1 x = shift ψ lam (halfTr (Matrix.trace (b ⬝ GlobalTheory.StdUnn.inner B x x : Mx D A.rank A.rank))) * Φ.1 x := by
  intro D ψ A B χB omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam g b hg Φ x
  obtain ⟨c, hc, hgc⟩ := GlobalTheory.T.standardUnitaryChart_unipotent_eq_wittUnipotent D A μ hμ κ hκ (κ.symm g) b (by rw [MulEquiv.apply_symm_apply]; exact hg)
  obtain ⟨f, hf, hfΦ⟩ := ((GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D) ψ hW.std θ hθ A B ν 𝓨 hν).2.1 Φ.1 Φ.2
  have h1 := hT (κ.symm g) f hf Φ hfΦ.symm
  rw [MulEquiv.apply_symm_apply] at h1
  rw [h1, hgc, ((GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions D ψ A B χB omh hW ν 𝓨 hν f hf).2.2.1 c x), hfΦ]
  exact congrArg (· * Φ.1 x) (chr_eq_shift D ψ μ lam hlam _ b c hc)

end GlobalTheory.StdUnn.Unip
end
