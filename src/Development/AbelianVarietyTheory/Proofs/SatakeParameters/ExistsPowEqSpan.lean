import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdLawAtOfSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfFibres
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwU.MuUnr

theorem le_exp_neg_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  rw [← WithZero.exp_log h0] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem finPart_eq_one {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (z : (GlobalTheory.CMVal.Af E)ˣ)
    (hu : ∀ P, Valued.v ((z : GlobalTheory.CMVal.Af E) P) = 1)
    (hc : ∀ P, χ.UnrAt P ∨ (χ.TameAt P ∧ Valued.v ((z : GlobalTheory.CMVal.Af E) P - 1) < 1)) :
    GlobalTheory.CMVal.finPart χ z = 1 := by
  have e : (fun P => χ.loc P (GlobalTheory.CMVal.coord P z)) = fun _ => 1 := funext fun P => by
    rcases hc P with h | ⟨h, h'⟩
    · exact h _ (hu P)
    · exact h _ (hu P) (le_exp_neg_one' h')
  have h := GlobalTheory.CMVal.Fibre.hasProd_loc χ z
  rw [e] at h
  exact h.unique hasProd_one

theorem exists_pow_eq_span {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (n : ℕ) (s : 𝓞 F), 0 < n ∧ v.asIdeal ^ n = Ideal.span {s} := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set n := Fintype.card (ClassGroup (𝓞 F)) with hn
  have hvn : v.asIdeal ^ n ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv n
  have e : (⟨v.asIdeal ^ n, hvn⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨v.asIdeal, hv⟩ ^ n := Subtype.ext (by simp)
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ n, hvn⟩ = 1 := by
    rw [e, map_pow]
    exact pow_card_eq_one
  obtain ⟨s, hs⟩ := ((ClassGroup.mk0_eq_one_iff hvn).1 h1).principal
  exact ⟨n, s, Fintype.card_pos, hs⟩


end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU.MuUnr

open GlobalTheory.Mem.Col2 (afIso afIso_tmul_one mem_rInt_iff)


end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU.MuUnr

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}




end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU

open GlobalTheory.Mem.Col2 (afIso afIso_tmul_one mem_rInt_iff)
open GlobalTheory.TwU.MuUnr

end GlobalTheory.TwU
