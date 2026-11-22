module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes

open NumberField IsDedekindDomain Module AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AllWt
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

section Action

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

variable {l l' : Level H} {r : ℕ}

variable (Xo' : Moduli Dw l') (c' : Coeff l') {K : Type} [Field K] (ι : K →+* c'.F)
  (e : Basis (Fin r) (Rs l) (LaMod Dw l))

variable {Xo' c'} {n : ℕ} (U' : ∀ σ : c'.F →+* ℂ, Unf Xo' c' σ n)

end Action

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (T : CoreJ D) (i : Fin D.R.m)

variable {T i} {l' : Level T.Q.H} {Xo' : Moduli (T.Q.Dw ((i : ℕ) + 1)) l'} {c' : Coeff l'}

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes
