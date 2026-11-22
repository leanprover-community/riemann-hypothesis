module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BrEqv

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

abbrev FrN (D : D7) (n : ℕ) : Type := Frames (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ))

def inB (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) :
    D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => (B τ)⁻¹ * compAt θ τ (mt V g) * B τ

def volLev {V : HSp D} (v : Vol V) (U : Subgroup (GA D V)) : ℝ := (v.μ {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ}).toReal

def stabOrd {V : HSp D} (U : Subgroup (GA D V)) (h : GA D V) : ℕ :=
  Nat.card {γ : GQ V // ∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h = h * k * κ}

structure IsReps (V : HSp D) (U : Subgroup (GA D V)) {cl : Type} (h : cl → GA D V) : Prop where
  le : U ≤ GfC V
  cpt : IsCompact (U : Set (GA D V))
  opn : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V))
  fin : ∀ c, h c ∈ GfC V
  dec : ∀ g, ∃ γ ∈ GQ V, ∃ c, ∃ k ∈ GinfC V, ∃ κ ∈ U, g = γ * (h c * k) * κ
  uniq : ∀ c c', ∀ γ ∈ GQ V, ∀ k ∈ GinfC V, ∀ κ ∈ U, h c' = γ * (h c * k) * κ → c = c'

attribute [instance] ClsDat.fin ClsDat.finT

end GlobalTheory.SeeSaw

end
