module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.VolFromSW

@[expose] public section

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

end Gen

section Spec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

theorem um_countable_HFinIn (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    Countable (HFinIn (AF F) σ J) := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  have : Countable (GL (Fin M) E) :=
    Function.Injective.countable (f := fun u : GL (Fin M) E => (u : Matrix (Fin M) (Fin M) E))
      (fun _ _ h => Units.ext h)
  have hx : ∀ x : HFinIn (AF F) σ J, ∃ u : GL (Fin M) E,
      Formalism.UG.bc (inclR (AF F)) u = ((x : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) := by
    intro x
    have h : ((x : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) ∈ HFin (AF F) σ J :=
      Subgroup.mem_subgroupOf.1 x.2
    unfold HFin at h
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 h
    exact ⟨u, hu⟩
  refine Function.Injective.countable (f := fun x => (hx x).choose) ?_
  intro x y hxy
  have h1 := (hx x).choose_spec
  have h2 := (hx y).choose_spec
  simp only at hxy
  rw [hxy] at h1
  exact Subtype.ext (Subtype.ext (h1.symm.trans h2))

end Spec

end PI.VolStabSW
