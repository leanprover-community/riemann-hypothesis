import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

variable (D : D7) (u : D.what₂.Word)

def BwIncl : Prop :=
  ∀ w, OverT D u w →
    ∀ i, i ≤ D.R.m → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
      ∀ x ∈ (D.fm u).Bw i w v,
        ((D.mem u).A.T : D.what₂.LL) ^ (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) • x ∈ (D.fm u).S i w

theorem emb_tpow_smul (i n : ℕ) (x : ((D.fm u).lat i).V) :
    (D.fm u).emb i (((D.mem u).A.T : D.what₂.LL) ^ n • x) = tpow D u n • (D.fm u).emb i x := by
  rw [LinearMap.map_smulₛₗ, map_pow, map_natCast]
  rfl



theorem eval_subP {ι : Type} [Fintype ι] {n : ℕ} (N Z : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => (N x.1 * Z x.1) x.2.1 x.2.2) P =
      MvPolynomial.eval (fun x : ι × Fin n × Fin n => Z x.1 x.2.1 x.2.2) (Formalism.L2.Forms.subP N P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Formalism.L2.Forms.subP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, MvPolynomial.eval_X, hp]
    simp [Formalism.L2.Forms.subP, Matrix.mul_apply, MvPolynomial.eval_sum]

theorem fnOf_mul {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (N M : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.L2.Forms.fnOf G s (fun τ => N τ * M τ) P =
      Formalism.L2.Forms.fnOf G s M (MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * Formalism.L2.Forms.subP N P) := by
  funext y
  simp only [Formalism.L2.Forms.fnOf, LinearMap.coe_mk, AddHom.coe_mk, map_mul, MvPolynomial.eval_C]
  have h := eval_subP N (fun τ => M τ * y.1 τ) P
  simp only [← Matrix.mul_assoc] at h
  rw [h]
  simp only [Matrix.mul_assoc (N _), Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical

variable (D : D7) (u : D.what₂.Word)

def bwA_N {n : ℕ} (τv : D.what₂.Tau) (B B' : GL (Fin n) D.host.E) :
    D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => if τ = τv then atInf (embT D) (B'⁻¹ * B : GL (Fin n) D.host.E).1 τ else 1

theorem bwA_N_mul {n : ℕ} (τv : D.what₂.Tau) (B B' : GL (Fin n) D.host.E) :
    (fun τ => bwA_N D τv B B' τ * atInf (embT D) (B⁻¹ : GL (Fin n) D.host.E).1 τ) =
      fun τ => if τ = τv then atInf (embT D) (B'⁻¹ : GL (Fin n) D.host.E).1 τ
        else atInf (embT D) (B⁻¹ : GL (Fin n) D.host.E).1 τ := by
  funext τ
  unfold bwA_N
  split_ifs with h
  · simp only [atInf]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  · rw [one_mul]

def BwLocBases (Tt : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i),
    (∃ B : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B) ∧
    ∀ v, ∃ B' : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B'

def BwSubInt (Tt : FormsTied D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
    ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B →
      IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B' →
      ∀ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i),
        tpow D u (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) •
          (MvPolynomial.C (∏ τ, (bwA_N D ((D.fm u).tauOf w v) B B' τ).det ^ shiftOf (lamT u i) τ) *
            subP (bwA_N D ((D.fm u).tauOf w v) B B') P) ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i)

def BwLocGlob (Tt : FormsTied D u) : Prop :=
  ∀ w, OverT D u w → ∀ i (hi : i ≤ D.R.m) (y : ((D.fm u).lat i).V),
    (∀ c, ∃ B : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B ∧
      ∃ Q ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i), ∀ z, (D.fm u).emb i y c z =
        fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q ((Tt.val i hi).eY z)) →
    y ∈ (D.fm u).S i w



end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end
