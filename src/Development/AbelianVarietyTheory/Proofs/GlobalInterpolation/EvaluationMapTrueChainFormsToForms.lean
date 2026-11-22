module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueWeightsEqDescentShiftedWeightsInterlaceStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BranchingOk

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

