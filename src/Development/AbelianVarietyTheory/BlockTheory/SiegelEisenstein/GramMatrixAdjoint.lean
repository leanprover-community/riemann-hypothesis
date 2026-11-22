module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open scoped TensorProduct NNReal Matrix ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

variable {D}

def mmul {k l r : ℕ} (x : Mx D k l) (y : Mx D l r) : Mx D k r := HMul.hMul x y

def adj {k l : ℕ} (x : Mx D k l) : Mx D l k := Formalism.UG.cT (cA D) x

variable (D)

variable {D}

section Space

variable {m n : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E)

def wittIdx : ℕ :=
  sSup {r | ∃ W : Submodule D.host.E (Fin m → D.host.E),
    (∀ x ∈ W, ∀ y ∈ W, hE D.sp.cm.sig T x y = 0) ∧ Module.finrank D.host.E W = r}

def gramQ (x y : Mx D m n) : Mx D n n :=
  mmul (mmul (adj x) (T.map (incA D))) y

def trA (z : AE D) : AF D.host.F := Algebra.trace (AF D.host.F) (AE D) z

def pairing (ψ : AddChar (AF D.host.F) ℂ) (x y : Mx D m n) : ℂ := ψ (trA (Matrix.trace (gramQ T x y)))

end Space

section Weil

variable {θ : InfFam D} {m n : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E}

end Weil

end GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks

end
