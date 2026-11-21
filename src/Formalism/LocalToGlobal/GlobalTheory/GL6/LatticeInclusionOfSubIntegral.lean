import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionFamilyOf

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
