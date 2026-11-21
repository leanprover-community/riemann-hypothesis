import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

noncomputable section
namespace GlobalTheory.FockAlg.Model
open Formalism.BasicNotions.TH MvPolynomial

def fockEmb (σ : Type) [DecidableEq σ] :
    MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2 :=
  (basisMonomials σ ℂ).constr ℂ fun α =>
    lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ)

theorem isFockIsometry_fockEmb (σ : Type) [DecidableEq σ] : IsFockIP (fockEmb σ) := by
  intro α β
  have h : ∀ γ : σ →₀ ℕ, fockEmb σ (monomial γ 1) =
      lp.single 2 γ ((Real.sqrt (γ.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) := by
    intro γ
    have := (basisMonomials σ ℂ).constr_basis ℂ (fun α : σ →₀ ℕ =>
      (lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) :
        lp (fun _ : σ →₀ ℕ => ℂ) 2)) γ
    simpa [fockEmb] using this
  rw [h, h, lp.inner_single_left]
  split_ifs with e
  · subst e
    have h0 : 0 ≤ α.prod fun _ k => (k.factorial : ℝ) :=
      Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    rw [lp.single_apply_self, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt h0]
    simp [Finsupp.prod]
  · rw [lp.single_apply_ne _ _ _ e, inner_zero_right]






theorem subset_genSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) : S ⊆ genSub act S :=
  fun _ hx => Submodule.mem_sInf.2 fun _ hN => hN.1 hx

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (Z : Mat p q) (y : V) (hy : y ∈ genSub act S) :
    act Z y ∈ genSub act S :=
  Submodule.mem_sInf.2 fun N hN => hN.2 Z y (Submodule.mem_sInf.1 hy N hN)

def charAct (p q : ℕ) (c : ℚ) : Mat p q →ₗ[ℂ] Module.End ℂ ℂ :=
  ((c : ℂ) • Matrix.traceLinearMap (Ix p q) ℂ ℂ).smulRight 1

theorem charAct_apply (p q : ℕ) (c : ℚ) (Z : Mat p q) (v : ℂ) :
    charAct p q c Z v = (c : ℂ) * Z.trace * v := by
  simp [charAct]

theorem mem_wt (p q : ℕ) (c : ℚ) (μ : Ix p q → ℚ) (v : ℂ) :
    v ∈ wtSub (charAct p q c) μ ↔ ∀ a, (c : ℂ) * v = μ a * v := by
  simp [wtSub, charAct_apply, Eab, sub_eq_zero]

@[reducible] def charMod (p q : ℕ) (c : ℚ) : GKMod p q where
  V := ℂ
  act := charAct p q c
  lie := by
    intro X Y
    ext
    simp [charAct_apply, Matrix.trace_mul_comm X Y]; ring
  kfin := fun v => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩
  wts := fun v => Submodule.mem_iSup_of_mem (fun _ => c) ((mem_wt _ _ _ _ _).2 fun _ => rfl)


def lamHalf : Ix 1 1 → ℚ := Sum.elim (fun _ => 1 / 2) (fun _ => -1 / 2)



def vac : Pol 1 0 1 0 →ₗ[ℂ] TensorProduct ℂ (charMod 1 0 (1 / 2)).V (charMod 1 0 (1 / 2)).V :=
  (lcoeff ℂ 0).smulRight ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ) : TensorProduct ℂ ℂ ℂ)

theorem mat_eq (Z : Mat 1 0) : Z = Z (.inl 0) (.inl 0) • Eab (.inl 0) (.inl 0) := by
  ext a b
  rcases a with a | a
  · rcases b with b | b
    · rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; simp [Eab]
    · exact b.elim0
  · exact a.elim0



end GlobalTheory.FockAlg.Model
