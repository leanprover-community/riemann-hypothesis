module

public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.UG

namespace Formalism.IndefR.NX

section Op

variable {G H : Type} [Group G] [Group H] {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

end Op

section Twist

variable {H : Type} [Group H] {k : Type} [CommRing k]

end Twist

section GLv

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)

variable {v n} {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module ℂ W]

end GLv

section Reps

variable {G H : Type} [Group G] [Group H] {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

end Reps

section Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

end Concrete

section Checks

open Formalism.BasicNotions Formalism.L2.Theta

end Checks

end Formalism.IndefR.NX
