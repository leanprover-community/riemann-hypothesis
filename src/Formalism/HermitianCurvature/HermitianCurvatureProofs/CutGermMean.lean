module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AverageOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanBoundsLimits
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Tactic.Linter.Style

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.crystallineComparison Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace

noncomputable section

open Classical

def bD {f : ℕ} (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La] :
    Module.Basis (Fin (Module.finrank ℤ La)) ℝ (V f) :=
  (Pi.basisFun ℝ (Fin (Module.finrank ℤ La))).map (PairingConjugationLemmas.Le La).symm

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {s : ℕ} {β ε' : ℂ}
  {ut : ℂ → ℂ → H} {bt : ℂ → H} {SS : ℝ}

def uL (hG : PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS) (x : ℂ) :
    Lp H 2 (volume : Measure ℂ) :=
  if hx : x ≠ 0 then
    ((PBK.memLp_cvec s ut x hx).1 (hG.memU () (Finset.mem_singleton_self _) x hx)).toLp (PBK.cvec s ut x)
  else 0

def aL (hG : PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS) (x : ℂ) :
    Lp H 2 (volume : Measure ℂ) :=
  if hx : x ≠ 0 then
    ((PBK.memLp_cvec s (fun x D => PBK.mainD s β ε' bt x D) x hx).1
      (hG.memLp_mainD (Finset.mem_singleton_self ()) x)).toLp (PBK.cvec s (fun x D => PBK.mainD s β ε' bt x D) x)
  else 0

variable (hG : PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS)

end vec

end

end Formalism.FourierDecayAlt.P.CutBP
