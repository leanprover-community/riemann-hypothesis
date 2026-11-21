import Formalism.LocalToGlobal.HermitianForms.TiedBrRow

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Matrix

theorem exists_change {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (M M' : ι → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hP : P ∈ CSpan lam) : ∃ Q ∈ CSpan lam, fnOf G s M' P = fnOf G s M Q := by
  refine ⟨_, ?_, fnOf_change G s M M' hM P⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hP)

variable {D : D7} {u : D.what₂.Word}


theorem atInf_inv_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) (hA : IsUnit A.det) (τ : D.what₂.Tau) :
    IsUnit (atInf (embT D) A⁻¹ τ).det := by
  unfold atInf
  have h := (Matrix.isUnit_nonsing_inv_det A hA).map (embT D τ)
  first
  | (rw [RingHom.map_det, RingHom.mapMatrix_apply] at h; exact h)
  | simpa [RingHom.map_det] using h
  | simpa [AlgHom.map_det] using h



variable (Tf : FormsTied D u)
  (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
  (hB : ∀ w c, IsUnit (B w c).det)

include hB





omit hB in

structure PendRest (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop where
  exP : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c, ∃ P ∈ CSpan ((D.fm u).lam D.R.m),
    (∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl).eY s)) ∧
    ∀ z : (D.mem u).P.Wrow, Tf.valP.eW z c = fnOf _ (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) →
      coPT Tf B w z c = Formalism.L2.Ker.brTen D u (coMT Tf B w c (φ ((D.fm u).til c)))
  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coMT Tf B w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w ((D.fm u).lam D.R.m)
  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔
    ∀ c, coPT Tf B w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg
  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m,
    ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMT Tf B w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coMT Tf B w c (φ ((D.fm u).til c))))).re
  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (Formalism.MainNotions.product_first_zeroth_parts.nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPT Tf B w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coPT Tf B w z c))).re


end Formalism.L2.Forms
