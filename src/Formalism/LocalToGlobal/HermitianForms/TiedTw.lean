module

public import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
public import Formalism.LocalToGlobal.HermitianColumns.TiedQCJoint
public import Formalism.LocalRingCardinality.DataKerP

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure TwAtT (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) where

  eVT : (Tw.A u μ).vT ≃ (D.mem u).A.vT

  eFv : ∀ v, (Tw.A u μ).Fv v ≃+* (D.mem u).A.Fv (eVT v)
  psiT : ∀ v x, (Tw.A u μ).psiT v x = (D.mem u).A.psiT (eVT v) (eFv v x)
  rhoT : ∀ v a φ, (Tw.A u μ).rhoT v a (D.e0Tw u μ φ) =
    D.e0Tw u μ ((D.mem u).A.rhoT (eVT v) (Units.map ((eFv v : (Tw.A u μ).Fv v ≃+* (D.mem u).A.Fv (eVT v)) : (Tw.A u μ).Fv v →* (D.mem u).A.Fv (eVT v)) a) φ)
  Mu0 : (Tw.A u μ).Mu0 = (D.mem u).A.Mu0.map (D.e0Tw u μ : _ →ₗ[ℂ] _)
  duStar : (Tw.A u μ).duStar = (D.mem u).A.duStar
  Dstar : (Tw.A u μ).Dstar = (D.mem u).A.Dstar
  GamP : (Tw.A u μ).GamP = (D.mem u).A.GamP

  tauOf : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ v, (Tw.fm u μ).tauOf w v = (D.fm u).tauOf w (eVT v)
  seenP : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (Tw.fm u μ).seenP w = (D.fm u).seenP w

def TwAtT.eV {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} (a : TwAtT Tw u μ) (At : AtTTied u) :
    (Tw.A u μ).vT ≃ PlT D u := a.eVT.trans At.eV

def TwAtT.res {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} (a : TwAtT Tw u μ) (At : AtTTied u) (v : (Tw.A u μ).vT) :
    𝓞 D.host.E →+* (Tw.A u μ).Fv v := ((a.eFv v).symm : _ →+* _).comp (At.res (a.eVT v))

variable {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def okQ (D : D7) (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : D.what₂.places.Pl) : Prop :=
  ∀ v ∈ Q, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal

end Formalism.L2.Forms

end
