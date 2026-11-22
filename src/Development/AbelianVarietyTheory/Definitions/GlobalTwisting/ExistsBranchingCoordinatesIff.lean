module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

variable {D : D7} {u : D.what₂.Word}

variable {X : Ch D u}

theorem fockF_self_eq {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f =
    ((∑ m ∈ f.support, Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold Formalism.REAL.fockF
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc : f.coeff m * star (f.coeff m) = ((Complex.normSq (f.coeff m) : ℝ) : ℂ) := Complex.mul_conj _
  rw [hc, Complex.ofReal_mul, Complex.ofReal_natCast]

theorem fockF_self_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (Formalism.REAL.fockF f f).re := by
  rw [fockF_self_eq, Complex.ofReal_re]
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
  refine Finset.sum_pos (fun n hn => ?_) ⟨m, MvPolynomial.mem_support_iff.mpr hm⟩
  have h1 : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have h2 : 0 < Complex.normSq (f.coeff n) := Complex.normSq_pos.mpr h1
  have h3 : (0 : ℝ) < ((∏ k ∈ n.support, (n k).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun k _ => Nat.factorial_pos _)
  exact mul_pos h2 h3

end GlobalTheory.LvT
