module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def trInf (D : D7) (x : Ainf D.host.F) : ℝ :=
  ∑ v : InfinitePlace D.host.F, (v.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding v (x v)).re

def realAd (D : D7) (s : InfinitePlace D.host.F → ℝ) : AF D.host.F :=
  pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (fun v => s v.1, 0)) 0

def realPt (D : D7) (p : (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)) : AE D :=
  realAd D p.1 ⊗ₜ[D.host.F] (1 : D.host.E) + realAd D p.2 ⊗ₜ[D.host.F] D.host.xi0

@[reducible] def measWA (A B : HSp D) : MeasurableSpace (WA A B) := borel _

def idemFin (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D :=
  algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))

open Classical in
def idemInf (D : D7) (v : InfinitePlace D.host.F) : AE D :=
  algebraMap (AF D.host.F) (AE D) (pairA D.host.F (Pi.single v 1) 0)

end GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices

end
