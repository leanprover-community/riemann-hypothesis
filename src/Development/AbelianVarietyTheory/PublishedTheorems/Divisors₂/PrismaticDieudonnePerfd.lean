module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import ReciprocityTheory.DualLattices.AinfFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

attribute [instance] CycPerfd.ring CycPerfd.nonunit CycPerfd.complete

end GlobalTheory.Published
