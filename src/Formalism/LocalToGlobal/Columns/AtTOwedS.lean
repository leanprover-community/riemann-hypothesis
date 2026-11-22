module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.AtTLemmas

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

end Gen

section Seen

variable {X : Fields} {Pr : Primes X}

theorem Fields.Ok.nonempty_Tau (hX : X.Ok) : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos

theorem conjP_pullW_mem_vT_iff (hPr : Pr.Ok) (u : Pr.Word) (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) :
    conjPrime₂ (pullW τ w) ∈ Pr.vT u ↔ X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal :=
  mem_divs (hPr.piT_ne_zero u) _

theorem owedS_T_mem {u : Pr.Word} (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.K)} {τ : X.Tau}
    (h : X.embO τ (Pr.piT u) ∈ w.asIdeal ∨ X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal) : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal := by
  have e : (Pr.T u : 𝓞 X.K) = X.embO τ (Pr.piT u) * X.embO τ (X.conjO (Pr.piT u)) := by
    rw [← map_mul, hPr.piT_norm u, map_natCast]
  rw [e]
  rcases h with h | h
  · exact Ideal.mul_mem_right _ _ h
  · exact Ideal.mul_mem_left _ _ h

theorem seenBarC.T_mem (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word} {w : HeightOneSpectrum (𝓞 X.K)} (h : seenBarC Pr u w) :
    (Pr.T u : 𝓞 X.K) ∈ w.asIdeal := by
  obtain ⟨τ⟩ := hX.nonempty_Tau
  exact owedS_T_mem hPr (Or.inr (h τ))

variable [Nonempty X.Tau]

variable {R : Ranks} (W : Wts X Pr.Word R)

end Seen

section Exist

variable {X : Fields} {Pr : Primes X}

end Exist

end Formalism.L2.Col
