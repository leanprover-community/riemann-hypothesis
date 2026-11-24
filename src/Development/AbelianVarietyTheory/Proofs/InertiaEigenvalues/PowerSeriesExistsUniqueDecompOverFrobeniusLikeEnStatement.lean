module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEn
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped PowerSeries Pointwise

theorem _root_.GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧, f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j) := by
  first | exact @GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main | exact GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main | (intros; apply GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main <;> assumption)
