module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DescentConstants
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

section Weights

end Weights

section Numbers

end Numbers

section Transport

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt
open Formalism.L2.Pj hiding kap

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

variable {Dw : Datum H}

def psiOf {T : Par D} (h : T.PinHost) (t : D.what₂.Tau) : Psi T.H := ⟨DV.tauEmb D t, h.2.2.2 t⟩

theorem psiOf_bijective {T : Par D} (h : T.Pins) : Function.Bijective (psiOf h.1) := by
  have hj : InR D 1 := ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩
  refine ⟨fun s t e => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val e), fun τ => ?_⟩
  obtain ⟨t, ht⟩ := ((GlobalTheory.WeightExponents.weight_exponents D T h 1 hj
    (WeightAlgebra.wscalar D 1 0 Even.zero)).2.2.1 τ.1).1 τ.2
  exact ⟨t, Subtype.ext ht.symm⟩

variable {T : Par D} {j : ℕ}

theorem sig_eq (h : T.Pins) (hj : InR D j) :
    (T.Dw j).p = pp D j ∧ (T.Dw j).q = qq D j ∧ (T.Dw j).p + (T.Dw j).q = D.R.r := by
  obtain ⟨h1, h2, -⟩ := h.2.2.2 j hj
  refine ⟨h1, h2, ?_⟩
  have := D.R.m_add_three_le_k
  have := hj.1
  have := hj.2
  rw [h1, h2]
  simp only [Ranks.sigW, Ranks.r]; omega

theorem dimFlag_eq (h : T.Pins) (hj : InR D j) : dimFlag (T.Dw j) = placeRankTwoOne.dimY D := by
  rw [dimFlag, Formalism.DegreeFormula.dimFl, (sig_eq h hj).2.2, ← Fintype.card_of_bijective (psiOf_bijective h), D.what₂.card_Tau,
    placeRankTwoOne.dimY, Nat.choose_two_right]

end Transport

end GlobalTheory.SlopeRec
