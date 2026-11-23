module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleConditionLogDerivativeTransition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cech_cocycle_condition_log_derivative_transition : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (W₀ : Z.Opens) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W₀ d → ∀ (J : Type) (W : J → Z.Opens) (j : J → L.ι), (∀ i, W i ≤ W₀) → ∀ (hj : ∀ i, W i ≤ L.U (j i)) (i i' i'' : J), resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (d (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) * resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val) + resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (d (W i' ⊓ W i'') (resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i'')).val) * resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i''))⁻¹.val) = resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (d (W i ⊓ W i'') (resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i'')).val) * resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i''))⁻¹.val) := by
  first | exact @GlobalTheory.DlogCocycle.dlog_cocycle | exact GlobalTheory.DlogCocycle.dlog_cocycle | (intros; apply GlobalTheory.DlogCocycle.dlog_cocycle <;> assumption)
