module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConstantOneMemNonvanishing
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open scoped ComplexConjugate

namespace GlobalTheory.CxForm

section Values

variable {n : ℕ}

end Values

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ}

namespace ArRing

variable {B : BottChern} {h : IsRegVar p D} (R : ArRing B h) {r : ℕ} (E : HermVB p r)

end ArRing

open Limits

variable (q) in
def IsRelAcyclic (π : Y ⟶ X) (L : LB Y) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (W : κ → Y.Opens),
    (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = π ⁻¹ᵁ U → ∀ n, (AbLaw.cechLB q L W).ExactAt (n + 1)

end GlobalTheory.CxForm
