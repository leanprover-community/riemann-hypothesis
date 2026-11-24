module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
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
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC

open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB

variable {f p q N' : ℕ}

def dk (w : V (nD f p q)) (k : Fin f) : ℝ := (1 - Zof w k * (Zof w k)ᴴ).det.re

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC

variable {f p q N' : ℕ}

theorem contDiff_det_of {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {m : ℕ} {M : E → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun x => M x i j) : ContDiff 𝕜 ∞ fun x => (M x).det := by
  have e : (fun x => (M x).det) = fun x =>
      ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, M x (σ j) j := by
    funext x; rw [Matrix.det_apply']
  rw [e]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun j _ => h _ _)

theorem cd_coord {n : ℕ} (i : Fin n) : ContDiff ℂ ∞ fun v : V n => v i := by
  have h : (fun v : V n => v i) = ⇑(EuclideanSpace.proj i : V n →L[ℂ] ℂ) := by
    funext v; simp
  rw [h]; exact ContinuousLinearMap.contDiff _

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
