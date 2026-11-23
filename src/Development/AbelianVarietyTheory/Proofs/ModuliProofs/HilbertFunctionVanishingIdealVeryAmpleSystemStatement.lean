module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionVanishingIdealVeryAmpleSystem
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.hilbertFunction_vanishingIdeal_veryAmpleSystem : ∀ (K σ : Type) [Field K] [Finite σ] [Nonempty σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → ∃ Q : Polynomial ℚ, ∀ᶠ e : ℕ in Filter.atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℚ) = Q.eval (e : ℚ) ∧ dimDeg (idealOf p M th (𝟙 X)) e + r = Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  first | exact @GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf | exact GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf | (intros; apply GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf <;> assumption)
