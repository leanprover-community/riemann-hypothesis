module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective

@[expose] public section

open Pointwise

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

end General

section DVR

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_quotient_span_singleton_dvr (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a :=
  Ring.ord_eq_addVal a

section Free

variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

end Free

variable {V : Type*} [AddCommGroup V] [Module R V] [Module.IsTorsionFree R V]
  {A : Submodule R V}

end DVR

end GlobalTheory
