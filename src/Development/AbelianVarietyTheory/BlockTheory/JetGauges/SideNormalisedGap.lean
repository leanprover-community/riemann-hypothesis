module

public import Mathlib
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.IsLowUnitH
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.PeriodIntegrals.BesselPeriodGGP
public import Formalism.PeriodIntegrals.BesselMapUniq
public import Formalism.PeriodIntegrals.KFinSmooth
public import Formalism.HermitianCurvature.StatementB

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap

open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU IsOrthProjOnto InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def mulP {k r : ℕ} (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

theorem measurable_mulP {k r : ℕ} : Measurable (mulP (k := k) (r := r)) := by
  unfold mulP
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  fun_prop

def muS {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) := (μW.prod μN).map mulP

section Side

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

end Side

end GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap
