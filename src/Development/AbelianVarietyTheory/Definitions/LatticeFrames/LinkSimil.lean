import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SymplecticAdjointInclusionZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.StCheck

open GlobalTheory.Size (posSp)
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem jointCont (D : D7) : JointCont D := fun _ _ _ _ _ _ h _ hf => GlobalTheory.ThetaJointCont.continuous_om_oriented h hf



theorem trace_inverseGram_conj_smul_eq {R : Type} [CommRing R] {m n : ℕ} (c : R) (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin m) (Fin n) R)
    (g : Matrix (Fin n) (Fin n) R) (y : Matrix (Fin n) (Fin m) R) :
    (a ⬝ (b ⬝ ((c • g) ⬝ y))).trace = c * (a ⬝ (b ⬝ (g ⬝ y))).trace := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]

set_option maxHeartbeats 1600000 in

theorem hO_ofAdj (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (c : D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = c • L'.gram) (x y : WO S L') :
    hO L S (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ x))
      (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ y)) =
      incA D (c / (D.host.xi0 * star D.host.xi0)) * hO S L' y x := by
  have h : adj (rat τ : Mx D L.rank L'.rank) ⬝ (gA L ⬝ (rat τ : Mx D L.rank L'.rank)) = incA D c • gA L' := by
    rw [gA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]; exact congrArg rat hτ
  rw [hO_eq_trace, hO_eq_trace, ofAdj, ofAdj]
  simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel, trace_smul, smul_eq_mul]
  rw [trace_mul_comm (rat τ : Mx D L.rank L'.rank), Matrix.mul_assoc y, trace_mul_comm y]
  simp only [Matrix.mul_assoc]
  rw [cancel₃ h]
  have h0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have h1 : incA D (c / (D.host.xi0 * star D.host.xi0)) =
      incA D (-D.host.xi0⁻¹) * (cA D (incA D (-D.host.xi0⁻¹)) * incA D c) := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, ← map_mul]
    congr 1
    rw [star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    field_simp
  have h2 := trace_inverseGram_conj_smul_eq (R := AE D) (incA D c) (giA S) (adj x) (gA L') y
  rw [h1, mul_assoc, mul_assoc]
  exact congrArg (fun t => incA D (-D.host.xi0⁻¹) * (cA D (incA D (-D.host.xi0⁻¹)) * t)) h2




theorem mt_inv_ofAdj (L W : HSp D) (n : GA D W) (z : Mx D L.rank W.rank) :
    mt W n⁻¹ ⬝ ofAdj L W z = ofAdj L W (z ⬝ mt W n) := by
  simp only [ofAdj, mt_inv, adj_mul, Matrix.mul_smul, Matrix.mul_assoc, gA_giA_cancel]

theorem incAdj_eq {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (L : HSp D) (y : Mx D L.rank ρ) :
    d.incAdj L y = ofAdj L W (y ⬝ d.pX) := by
  simp only [ofAdj, d.incAdj_apply, d.incY_apply, d.pX_eq, adj_mul, adj_adj, adj_gA, Matrix.mul_smul, Matrix.mul_assoc,
    giA_gA_cancel]

theorem projection_mul_ofAdjoint {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (L : HSp D) (z : Mx D L.rank W.rank) :
    d.p0 ⬝ ofAdj L W z = ofAdj L W₀ (z ⬝ d.j0) := by
  simp only [ofAdj, d.p0_eq, adj_mul, Matrix.mul_smul, Matrix.mul_assoc, gA_giA_cancel]

theorem tau_zEll {ρ σ : ℕ} {B : BesLev D σ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') :
    (rat l.τ : Mx D B.L.rank L'.rank) ⬝ zEll L' ρ ζ' = yZero B.L ρ B.ζ := by
  rw [zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, yZero, zEll, ← Matrix.neg_vecMulVec]
  congr 1
  funext i; exact map_neg (incA D) _

theorem link_point {ρ σ : ℕ} {B : BesLev D σ} {L' W W₀ : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')
    (d : HypDec W W₀ ρ) (n : GA D W) : ptT d B.L (yZero B.L ρ B.ζ) n = l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) := by
  rw [ptT, incAdj_eq, mt_inv_ofAdj, projection_mul_ofAdjoint, Link.κ, ptS, d.extX_apply, ← tau_zEll l]
  simp only [Matrix.mul_assoc]


theorem link_simil {σ : ℕ} {B : BesLev D σ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Link B L' ζ') : l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (B.L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

example (D : D7) : ∃ τ : Matrix (Fin 1) (Fin 1) D.host.E,
    τᴴ ⬝ ((show Matrix (Fin 1) (Fin 1) D.host.E from (diagSp D 1 ![true] 0 1).gram) ⬝ τ) =
      (-(D.host.xi0 * star D.host.xi0)) • (show Matrix (Fin 1) (Fin 1) D.host.E from (diagSp D 1 ![false] 1 0).gram) := by
  refine ⟨D.host.xi0 • 1, ?_⟩
  rw [diagSp_gram, diagSp_gram]
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [Examples₂.sgn, mul_comm]

end GlobalTheory.Unf.StCheck

end
