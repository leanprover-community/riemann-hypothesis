module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Trace.Quotient
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.ResDisc

open IsLocalRing

theorem isUnit_discr_of_isMaximal_map {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Finite (ResidueField R)] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
    (hmax : (Ideal.map (algebraMap R S) (maximalIdeal R)).IsMaximal) :
    IsUnit (Algebra.discr R b) := by
  haveI : Module.Free R S := Module.Free.of_basis b
  haveI : Module.Finite R S := Module.Finite.of_basis b
  letI := Ideal.Quotient.field (maximalIdeal R)
  letI := Ideal.Quotient.field (Ideal.map (algebraMap R S) (maximalIdeal R))
  haveI : Finite (R ⧸ maximalIdeal R) := ‹Finite (ResidueField R)›
  haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    Module.Finite.of_basis (basisQuotient b)
  haveI : Algebra.IsSeparable (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    inferInstance
  have h1 : Ideal.Quotient.mk (maximalIdeal R) (Algebra.discr R b) =
      Algebra.discr (R ⧸ maximalIdeal R) (basisQuotient b) := by
    rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
    congr 1
    ext k m
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, basisQuotient_apply, ← map_mul, Algebra.trace_quotient_mk]
  have h2 := Algebra.discr_not_zero_of_basis (R ⧸ maximalIdeal R) (basisQuotient b)
  rw [← h1] at h2
  by_contra h
  exact h2 (Ideal.Quotient.eq_zero_iff_mem.2 ((mem_maximalIdeal _).2 h))

end GlobalTheory.UnitLemma.Unr.ResDisc
