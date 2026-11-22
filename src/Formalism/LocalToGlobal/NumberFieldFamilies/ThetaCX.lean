module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaC
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
public import Formalism.LocalToGlobal.JointCharacters.SameChr

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Host Formalism.L2.JoinChr Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

variable {D : D7}

def plE (τ : D.what₂.Tau) : InfinitePlace D.host.E := InfinitePlace.mk (tauE D τ)

theorem conj_tauE_ne (τ τ' : D.what₂.Tau) : ComplexEmbedding.conjugate (tauE D τ) ≠ tauE D τ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, tauE_sqrtMinusD, tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have := sqrt_d_pos D
  linarith

theorem plE_bij (D : D7) : Function.Bijective (plE (D := D)) := by
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with e | e
    · exact tauE_inj e
    · exact absurd e (conj_tauE_ne τ τ')
  · intro w
    obtain ⟨τ, h | h⟩ := tauE_or w.embedding
    · exact ⟨τ, by unfold plE; rw [h, InfinitePlace.mk_embedding]⟩
    · exact ⟨τ, by unfold plE; rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]⟩

theorem plE_complex (τ : D.what₂.Tau) : (plE τ).IsComplex := by
  rw [plE, InfinitePlace.isComplex_mk_iff]
  exact fun h => conj_tauE_ne τ τ h

namespace AdBC

variable (B : AdBC D)

end AdBC

section Dens

variable {L : Type} [Field L] [NumberField L]

end Dens

namespace AdBC

variable (B : AdBC D)

end AdBC

section Frame

variable {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

variable (B : AdBC D)

variable {ψ : AddChar (AF D.host.F) ℂ} (Gc : ChrGaps B) (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ)
  (f : Free Om)

end Frame

end Formalism.L2.Fam.ThC

end
