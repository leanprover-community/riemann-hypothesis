module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayerParametersAdmissible

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Db

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.Mem.Df NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

def setDivZ {C : Cols B} (Z : TC.Later B C) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) : TC.Later B C :=
  { Z with V := { Z.V with div := (setDiv (assemble B C Z.W Z.V Z.S Z.N Z.G) N h).div } }

theorem D_setDivZ (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) :
    w.D (setDivZ Z N h) = setDiv (w.D Z) N h := rfl

section Layers

variable {K : Ctx} {w : ColW B f T} {Z : w.Lt}

end Layers

end GlobalTheory.Mem.Db

end
