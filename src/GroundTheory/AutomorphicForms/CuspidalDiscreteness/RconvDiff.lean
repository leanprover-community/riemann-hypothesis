module

public import Mathlib
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DiffBound
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.TorusReduction

@[expose] public section

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
