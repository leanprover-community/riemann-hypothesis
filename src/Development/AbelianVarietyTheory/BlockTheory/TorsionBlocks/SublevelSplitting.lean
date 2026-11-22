module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def matF (V : HSp D) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
  Units.val (h : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))

def compAtPl (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : Bridge.Gf V) :
    Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  (matF V h).map (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E))

variable (D) in
def IsSplitPl (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ P P' : HeightOneSpectrum (𝓞 D.host.E), P ≠ P' ∧ P.under (𝓞 D.host.F) = v ∧ P'.under (𝓞 D.host.F) = v

def SuppSplitOff (V : HSp D) (bad : ℕ) (h : Bridge.Gf V) : Prop :=
  ∃ Sp : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    (∀ v ∈ Sp, IsSplitPl D v ∧ (bad : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, v ∉ Sp → compAtPl V v h = 1

def IsOpenLev (V : HSp D) (J' : Subgroup (Bridge.Gf V)) : Prop :=
  IsOpen ((J'.comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V))

variable {T : Type}

section Row

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Row

end GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting

end
