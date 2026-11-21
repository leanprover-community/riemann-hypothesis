import Mathlib
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.TiedValNorm
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStepG
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.CoefGram


theorem map_inv_eq {K L : Type} [Field K] [Field L] {n : ℕ} (f : K →+* L) (A : Matrix (Fin n) (Fin n) K) :
    A⁻¹.map f = (A.map f)⁻¹ := by
  have h1 : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  have h2 : (A.map f).adjugate = A.adjugate.map f := (RingHom.map_adjugate f A).symm
  ext a b
  rw [Matrix.map_apply, Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv', h1, h2,
    Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_inv₀, Matrix.map_apply]

theorem posDef_of_hasSignature {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  have h1 : (P.valᴴ * G.reindex e e * P.val).PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h2 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1
  have h3 : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [h3]
  exact h2.submatrix e.injective

theorem gramP_posDef (D : D7) (σ : D.host.E →+* ℂ) : ((gramP D).map σ).PosDef := by
  letI := D.host.cmStar
  have hsig := D.sp.X'_sig σ
  have h0 : D.sp.X'.sig σ = (D.sp.X'.rank, 0) := D.X'_posDef σ
  rw [h0] at hsig
  have h1 : (D.sp.X'.gram.map σ).PosDef := posDef_of_hasSignature _ hsig
  exact h1.submatrix (finCongr (rankP D)).symm.injective



end GlobalTheory.Core.CoefGram
