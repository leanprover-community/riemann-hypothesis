module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.FlipDecAlt
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlipUSymmCont
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.DecompositionUnitaryShift
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.FlipDec
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.OccurrenceOfWalk
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

noncomputable section

open Finset

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

theorem flip_discrete_series_holds : FlipDS := fun m ε lam K _ _ σ =>
  ⟨isDS_of_flip, GlobalTheory.CompanionTheory.NegDS.isDS_flip m K ε lam σ⟩

theorem decEx2_of (h1 : DecLe) (h2 : FlipDS) (h3 : FlipDec) : DecEx2 := by
  intro m ε lam H _ _ π hf ht hp hds hgap
  by_cases hle : #{a : Fin m | ε a = false} ≤ #{a : Fin m | ε a = true}
  · obtain ⟨X, hX⟩ := h1 m ε lam H π hf hle hp hds hgap
    exact ⟨X, hX⟩
  · have hds' : IsDS (fun a : Fin m => !ε a) lam π := (h2 m ε lam H π).2 hds
    have hf' : ∃ a : Fin m, (!ε a) = false := by
      obtain ⟨a, ha⟩ := ht
      exact ⟨a, by simp [ha]⟩
    have hle' : #{a : Fin m | (!ε a) = false} ≤ #{a : Fin m | (!ε a) = true} := by
      simp only [Bool.not_eq_false', Bool.not_eq_true']
      omega
    have hgap' : Formalism.QuantumDeterminants.GapAtLeast (fun a : Fin m => !ε a) lam (200 * (m : ℝ) ^ 3) := by
      intro a b hab
      apply hgap a b
      intro h
      apply hab
      simp [h]
    obtain ⟨X, hX⟩ := h1 m (fun a => !ε a) lam H π hf' hle' hp hds' hgap'
    exact h3 m ε lam H π X hX

theorem decomposition_existence_holds : DecEx2 := decEx2_of decomposition_le_holds flip_discrete_series_holds flip_decomposition_holds

theorem walk : StepL → StepM → Base → Occ := occurrence_of_walk

end PositivityTheory.RgHe.Dec
