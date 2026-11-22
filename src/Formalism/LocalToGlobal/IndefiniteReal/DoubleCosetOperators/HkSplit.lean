module

public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.HeckeCommuteOfCompatibility
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.UG

open scoped TensorProduct

namespace Formalism.IndefR.NX

section Ext

variable {S S' R : Type} [CommRing S] [CommRing S'] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

end Ext

section Place

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

end Place

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

variable {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

end Local

section Emb

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {v : HeightOneSpectrum (𝓞 D.host.F)}

end Emb

section Level

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Level

section Clauses

variable {G : Type} [Group G]

end Clauses

section Checks

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Checks

end Formalism.IndefR.NX
