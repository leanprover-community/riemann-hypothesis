module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoSeq

section General

variable {O : Type} [CommRing O] {X T T' S : Scheme.{0}} {A B A' B' : X.Modules}

variable (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ)

variable {α β α' β' r}

end General

section Dieu

variable {O : Type} [CommRing O] (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}}
  [Algebra k Γ(C, ⊤)] {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Dieu

end GlobalTheory.TwoSeq
