module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalRingCardinality.DataTies

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters

structure SignedPar (n : ℕ) where
  lam : Fin n → ℝ
  sgn : Fin n → Bool
  hc : Formalism.QuantumDeterminants.IsHCParam lam

namespace SignedPar

variable {n : ℕ} (P : SignedPar n)

def p : ℕ := (Finset.univ.filter fun a => P.sgn a = true).card

def q : ℕ := (Finset.univ.filter fun a => P.sgn a = false).card

def IsOfSig (p q : ℕ) : Prop := P.p = p ∧ P.q = q

def low : Fin n → ℝ := Formalism.QuantumDeterminants.lowK P.sgn P.lam

end SignedPar

section Chains

variable {R : Ranks} (c : HCParam R)

end Chains

section Adelic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end Adelic

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsDSPar {n : ℕ} (P : SignedPar n) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsDS P.sgn P.lam σ

end Rep

section Signatures

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

end Signatures

end GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters
