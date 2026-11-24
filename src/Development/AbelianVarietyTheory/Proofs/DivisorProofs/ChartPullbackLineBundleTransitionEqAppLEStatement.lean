module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLE
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.chartPullback_lineBundle_transition_eq_appLE : ∀ (Y Y' : Scheme.{0}) (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) (cp : ChartPull A' A h) (i j : A'.ι), ((A'.g i j : Γ(Y', A'.U i ⊓ A'.U j)ˣ) : Γ(Y', A'.U i ⊓ A'.U j)) = (h.appLE (A.U (cp.idx i) ⊓ A.U (cp.idx j)) (A'.U i ⊓ A'.U j) (le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j)))).hom ((A.g (cp.idx i) (cp.idx j) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))ˣ) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))) := by
  first | exact @GlobalTheory.chartPull_g_appLE | exact GlobalTheory.chartPull_g_appLE | (intros; apply GlobalTheory.chartPull_g_appLE <;> assumption)
