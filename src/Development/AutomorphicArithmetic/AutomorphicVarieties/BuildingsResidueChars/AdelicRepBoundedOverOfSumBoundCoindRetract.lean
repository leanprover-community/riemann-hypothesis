module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
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
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
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

@[expose] public section

open CategoryTheory in
theorem UpperTheory.adelic_rep_bounded_over_of_sum_bound_coind_retract :
    UpperTheory.V.Af.CohB.SumBound → UpperTheory.V.Af.BA.CoindRetract → UpperTheory.V.Af.BA.BddOver := by
  intro hSum hRet
  unfold UpperTheory.V.Af.BA.BddOver
  intro G _ S hS hB
  unfold UpperTheory.V.Af.CohB.Bdd at hB ⊢
  obtain ⟨c, hc⟩ := hB
  refine ⟨c, fun A => ?_⟩
  obtain ⟨π, ι, hπι⟩ := hRet G S hS A
  have hq : ∀ q, Module.rank ℂ ↑(groupCohomology A q) ≤
      Module.rank ℂ ↑(groupCohomology (Rep.res S.subtype A) q) := by
    intro q
    have h1 := hSum G Unit A (fun _ => Rep.coind S.subtype (Rep.res S.subtype A))
      (fun _ => π) (fun _ => ι) (by rw [Fintype.sum_unique]; exact hπι) q
    rw [Fintype.sum_unique,
      ((groupCohomology.coindIso (Rep.res S.subtype A) q).toLinearEquiv).rank_eq] at h1
    exact h1
  calc UpperTheory.V.Af.CohB.totCoh A
      = Cardinal.sum (fun q => Module.rank ℂ ↑(groupCohomology A q)) := rfl
    _ ≤ Cardinal.sum (fun q => Module.rank ℂ ↑(groupCohomology (Rep.res S.subtype A) q)) :=
      Cardinal.sum_le_sum _ _ hq
    _ = UpperTheory.V.Af.CohB.totCoh (Rep.res S.subtype A) := rfl
    _ ≤ c * Module.rank ℂ ↑(Rep.res S.subtype A) := hc _
    _ = c * Module.rank ℂ ↑A := rfl
