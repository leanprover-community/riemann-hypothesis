module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusActionWeightedCharts
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_torus_action_weighted_charts : Out.Laws → Out.Laws2 → ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F F' : J → (Φ.H 1).Sec) (π : Φ.Pol N) (m : Matrix J J k) (Ch : GlobalTheory.ZJ.Charts Φ.G.left) (e : Ch.I ≃ J) (cl : Φ.E.X → Ch.Cl), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → IsUnit m.det → (∀ i, IsLin Φ.G.hom F (m i) (F' i)) → (∀ α β, cl α = cl β ↔ ∃ n, α = β + N • n) → cl 0 = Ch.c₀ → (∀ i j, m (e i) j ≠ 0 → Ch.wt i = cl (cls j)) → (∀ i, Ch.W i = nonzeroLocus (F' (e i.1)) ∧ ∀ j, IsRatio (F' (e j)) (F' (e i.1)) (Ch.W i) (Ch.r i j)) → ∃ c : Fin (Module.finrank ℤ Φ.E.X) → Ch.Cl, GlobalTheory.ZJ.Charts.Split (H := Φ.G) Ch c := by
  first | exact @GlobalTheory.ZH.FibTorus.exists_split | exact GlobalTheory.ZH.FibTorus.exists_split | (intros; apply GlobalTheory.ZH.FibTorus.exists_split <;> assumption)
