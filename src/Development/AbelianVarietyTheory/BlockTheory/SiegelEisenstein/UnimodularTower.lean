module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChainOnto
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {c : Com D} {u : D.what₂.Word}

section ColStep

variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)}

end ColStep

section Dbl

variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)}

end Dbl

section Fin2

variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T}

end Fin2

end GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower

end
