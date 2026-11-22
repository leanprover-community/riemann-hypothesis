module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def intVec (D : D7) (n : ℕ) : Set (Fin n → D.host.E) := {x | ∀ k, IsIntegral ℤ (x k)}

def IsFinComb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO S T), (∀ k, (x k).map (infPart D) = 0) ∧ f = ∑ k, c k • heisO ψ S T (x k) f₀

abbrev stdHom {D : D7} (S T : HSp D) : AddSubgroup (WO S T) := latO S T (intVec D S.rank) (intVec D T.rank) fun _ => True

def IsRatDatum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ Φ : WO S T → ℂ, IsSBHalf e (stdHom S T) Φ ∧ (∀ γ, Φ (γ.map fun a => e * incA D a) = Ξ γ) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ Φ f

section Dat
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

variable {I l Z u} {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}

namespace ColDat
variable (A : ColDat I l Z u Ch) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
  (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))

end ColDat
end Dat

def IsEmbTop {D : D7} (z0 : Fin (D.R.N D.R.m) → D.host.E) (emb : GA D D.sp.X' →* GA D (D.sp.X D.R.m)) : Prop :=
  ∀ h, IsExt D z0 (incA D) ((mt _ h).reindex (finCongr (rankP D)) (finCongr (rankP D)))
    ((mt _ (emb h)).reindex (finCongr (rankN D _ le_rfl)) (finCongr (rankN D _ le_rfl)))

end GlobalTheory.AdForm
