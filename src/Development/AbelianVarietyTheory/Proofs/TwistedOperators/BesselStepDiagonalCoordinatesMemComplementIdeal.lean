module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulMemComplId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StaircaseIdealConjugateInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF.DiagCoord

variable {D : D7}

theorem auxiliaryCoordinate_mem_staircaseIdeal {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {t : Fin B.rank → D.host.E} (ht : t ∈ d.lat Λ 𝔟) (r : Fin c) (hr : r.1 + r.1 + 1 ≠ c) :
    ((d.aᴴ * B.gram) *ᵥ t) r ∈ 𝔟 r.rev := by
  obtain ⟨y, -, v, hv, rfl⟩ := ht
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => (B.herm.eq (B.frame j) (B.frame i) : star (B.gram j i) = B.gram i j)
  have hperp : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have h1 := congrArg Matrix.conjTranspose d.perp
    have e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) = (frameMat B A d.ι)ᴴ := rfl
    rw [e, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero] at h1
    rw [← h1, Matrix.mul_assoc]
  have hgram : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hperp, hgram, zero_mulVec, zero_add]
  rw [mulVec, dotProduct, Finset.sum_eq_single r.rev]
  · have : antiDiagonalSignGramMatrix c ε r r.rev = 1 := by
      have := r.2
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev]
      rw [if_pos (by omega), if_neg (fun h => hr (by rw [Fin.ext_iff, Fin.val_rev] at h; omega))]
    rw [this, one_mul]; exact hv _
  · intro q _ hq
    have : antiDiagonalSignGramMatrix c ε r q = 0 := by
      have := r.2; have := q.2
      simp only [antiDiagonalSignGramMatrix]
      rw [if_neg (fun h => hq (by rw [Fin.ext_iff, Fin.val_rev]; omega))]
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem negPair_colsOf {n c k : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (hG : ∀ i j, star (G j i) = G i j)
    (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (w : Fin k → D.host.E) (s : Fin n → D.host.E) (p : Fin k) :
    ∑ j, (∑ l, star (s l) * (-G) l j) * colsOf a f w j p = -(w p * star (((aᴴ * G) *ᵥ s) (f p))) := by
  simp only [colsOf, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, star_sum, star_mul', star_star, hG,
    Matrix.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem entry_rankOne {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E) (e : Matrix (Fin n) (Fin l) D.host.E) (a : D.host.E)
    (t : Fin m → D.host.E) (g : Fin n → D.host.E) (p : Fin k) (p' : Fin l) :
    (q * Matrix.of (fun i j => a * t i * g j) * e) p p' = a * (q *ᵥ t) p * ∑ j, g j * e j p' := by
  simp only [Matrix.mul_apply, Matrix.of_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem stairId_mul_inv_succ (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) {c₁ c₂ : ℕ}
    (q₁ : Fin c₁) (q₂ : Fin c₂) (hc : c₂ = c₁ + 1) (hq : q₂.1 = q₁.1 + 1) :
    stairId 𝔞 𝔞' c₁ q₁ * (stairId 𝔞 𝔞' c₂ q₂)⁻¹ = 𝔞' := by
  unfold stairId
  rw [show c₂ - q₂.1 = c₁ - q₁.1 by omega, hq, pow_succ 𝔞' (q₁.1 + 1)]
  have h1 : 𝔞 ^ (c₁ - q₁.1) ≠ 0 := pow_ne_zero _ h𝔞
  have h2 : 𝔞' ^ (q₁.1 + 1) ≠ 0 := pow_ne_zero _ h𝔞'
  field_simp

theorem colsOf_gram {n c k : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin c) D.host.E) (f g : Fin k → Fin c)
    (w w' : Fin k → D.host.E) (p q : Fin k) :
    ((colsOf a f w)ᴴ * G * colsOf a g w') p q = star (w p) * w' q * (aᴴ * G * a) (f p) (g q) := by
  simp only [colsOf, Matrix.mul_apply, conjTranspose_apply, star_mul', Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.XCharBF.DiagCoord
