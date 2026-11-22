module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

abbrev Letter : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

variable {Dw}

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def FlagPt.frame {Ω : Type} [Field Ω] (y : FlagPt Z Ω) : EigFrame Z y.fK (y.y ≫ genι Z) :=
  ⟨y.u, y.tan, y.eig, y.basis⟩

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (fl : s.Flag)
  {C : CxSt D.what₂.LL} (hm : ∀ k, Mets (fl.C k) C)

end GlobalTheory.ShFam.Pad
