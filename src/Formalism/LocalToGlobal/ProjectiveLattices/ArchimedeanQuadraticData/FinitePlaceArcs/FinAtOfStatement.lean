module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.FunDef
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridge
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc
public import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCoreSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangeSt

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

attribute [instance] FinSite.nf FinSite.um FinSite.cs

def lcoeffPoly {ι K₁ : Type} [Field K₁] (P : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ) : MvPolynomial ι K₁ :=
  ∑ μ ∈ P.support, MvPolynomial.monomial μ ((P.coeff μ).coeff m)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def frameSub {K : Type} [Field K] (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → K) (Y : ArcLt Dw → K) : ArcLt Dw → K :=
  fun x => (∑ l, Y ⟨x.1, x.2.1, l⟩ * Bm x.1 l x.2.2) * (lam x.1 x.2.2)⁻¹

variable {D : D7} {T : Core D} {j : ℕ}

variable {h : LawsCore T} {ka : WeightFamilies.Wt D j} {CR Tt cc : ℝ}

end Formalism.L2.Pj.QAt
