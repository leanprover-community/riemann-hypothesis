module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundSplitOfIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Mixed

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

abbrev endT (T : Over X) (φ : A ⟶ A) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ≫ φ)

def IsNormEnd (φ : A ⟶ A) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) : Prop :=
  LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (eSec A))
    (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))

end Mixed

end ReciprocityTheory.ChartRestriction.G.PullbackSections
