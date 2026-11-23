module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UpTie.LeadCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.UpTie.LeadCount.bdd_mul_pow (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {la L : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) (hQ : X.IsBddSec L Q) (k : ℕ) : X.IsBddSec (la + k • L) (P * Q ^ k) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [succ_nsmul, ← add_assoc, pow_succ, ← mul_assoc]
    exact _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_mul X ih hQ


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.UpTie.LeadCount.bdd_mul_prod {n : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {la L : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) {s : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hs : ∀ k, X.IsBddSec L (s k)) (α : Fin n → ℕ)
    (t : Finset (Fin n)) : X.IsBddSec (la + (∑ k ∈ t, α k) • L) (P * (∏ k ∈ t, s k ^ α k)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hP
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, add_comm (α a), add_smul, ← add_assoc,
      mul_comm (s a ^ α a), ← mul_assoc]
    exact _root_.GlobalTheory.UpTie.LeadCount.bdd_mul_pow X ih (hs a) (α a)

end GlobalTheory.UpTie.LeadCount
