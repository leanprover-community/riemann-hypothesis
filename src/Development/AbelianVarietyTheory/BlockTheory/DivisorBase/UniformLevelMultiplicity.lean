module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

variable (T : CoreJ D) (j : ℕ)

variable [Algebra T.Q.c.F D.what₂.LL]

end GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets
