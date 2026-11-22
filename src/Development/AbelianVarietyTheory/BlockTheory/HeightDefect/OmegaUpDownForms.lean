module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsQuotInt (V : HSp D) (c : ℝ) (φ : GA D V → ℂ) (z : ℂ) : Prop :=
  AllSome (fun m : Measure (GA D V) × Set (GA D V) => IsVolPair D V m.1 m.2) fun m =>
    IntegrableOn φ m.2 m.1 ∧ z = (c : ℂ) * ∫ g in m.2, φ g ∂m.1

namespace Core

variable {X : ThetaX D} {T : ThetaTied D X} (C : Core T)

end Core

section
variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χA χB : (AE D)ˣ →* Circle} {om : Rep ψ A B}

end

end GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients

end
