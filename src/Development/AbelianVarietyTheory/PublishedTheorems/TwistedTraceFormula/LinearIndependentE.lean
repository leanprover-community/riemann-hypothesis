module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)
open scoped TensorProduct NNReal Classical

namespace GlobalTheory.TruncKer

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

structure WittFrame (V : HSpace E) where

  e : Fin (wittIndex V) → V.V

  f : Fin (wittIndex V) → V.V
  ee : ∀ i j, V.hD (e i) (e j) = 0
  ff : ∀ i j, V.hD (f i) (f j) = 0
  ef : ∀ i j, V.hD (e i) (f j) = if i = j then 1 else 0

namespace WittFrame

variable {V : HSpace E} (Φ : WittFrame V)

def sub (u : SV (wittIndex V)) : Submodule E V.V := Submodule.span E (Φ.e '' {i | u i = 1} ∪ Φ.f '' {i | u i = -1})

variable (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

def levi (P : Finset (SV (wittIndex V))) : Subgroup (HA R hc.sig V.gram) :=
  ⨅ u ∈ P, parab hc V R (Φ.sub u) ⊓ parab hc V R (Φ.sub (-u))

def IsGood (L : Submodule (𝓞 E) (Fin V.rank → E)) (a : GL (Fin V.rank) (AF F ⊗[F] E)) : Prop :=
  Submodule.IsLattice E L ∧ (∀ v, IsSelfDualAt hc.sig V.gram L v) ∧
  (∀ i, V.frame.equivFun (Φ.e i) ∈ L ∧ V.frame.equivFun (Φ.f i) ∈ L) ∧ IsMajorantFrame hc.sig V.gram a ∧
  ∀ (w : InfinitePlace F) (i : Fin (wittIndex V)),
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ hc.sig) (Formalism.UG.bc (compInf F E w) a⁻¹).1 * (Formalism.UG.bc (compInf F E w) a⁻¹).1) *ᵥ
      coordR V w.Completion (Φ.e i) = JR w.Completion V.gram *ᵥ coordR V w.Completion (Φ.f i)

end WittFrame

def IsSSPart {n : ℕ} (γ s : Matrix (Fin n) (Fin n) E) : Prop :=
  Module.End.IsSemisimple (Matrix.toLin' s) ∧ Commute γ s ∧ IsNilpotent (γ - s)

def IsSSClass {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (𝔬 : Set (GRat σ J)) : Prop :=
  ∃ δ : GRat σ J, Module.End.IsSemisimple (Matrix.toLin' δ.1.1) ∧
    𝔬 = {γ | ∃ s : GRat σ J, IsSSPart γ.1.1 s.1.1 ∧ IsConj δ s}

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (K : Subgroup (GA D V))

abbrev GF (V : HSp D) : Type := GRat D.sp.cm.sig V.gram

abbrev rat (V : HSp D) : GF V →* GA D V := ratEmb D.sp.cm.sig V.gram

end GlobalTheory.TruncKer

end
