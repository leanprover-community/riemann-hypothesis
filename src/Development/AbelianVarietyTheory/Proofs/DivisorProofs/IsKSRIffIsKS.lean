module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Frames GlobalTheory.AllWt
open Formalism.L2.Pj
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsKSR (Φ : Finset (E →+* ℂ)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (x' : Sp (DualNumber S) ⟶ Xo.X) (M : HIx Dw Φ → S) : Prop :=
  ∃ (A : Over (Sp S)) (_ : GrpObj A) (A' : Over (Sp (DualNumber S))) (_ : GrpObj A')
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (epsRed S) i) (ψ : LinearMap.BilinForm S (HdR A))
    (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A),
    IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧
    IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
    (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧
    ∀ (τ : Φ) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, IsLieComb (fun b => M ⟨τ, a, b⟩) (ub τ.1) w ∧
      IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w

theorem isKSR_iff_isKS {Φ : Finset (E →+* ℂ)} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {x' : Sp (DualNumber K) ⟶ Xo.X} {M : HIx Dw Φ → K} : IsKSR Φ y x' M ↔ IsKS Φ y x' M := Iff.rfl

end GlobalTheory.FlagTan
