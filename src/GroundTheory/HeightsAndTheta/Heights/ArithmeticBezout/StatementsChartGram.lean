module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (maDensity)

def gramVol {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) : ℝ :=
  let w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  (Matrix.det (Matrix.of fun a b => ∑ i, star (w a i) * w b i)).re

def ChartGramMA.Statement : Prop :=
  ∀ (e n : ℕ) (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ),
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ v y') → v y ≠ 0 →
      maDensity (fun _ y' => Real.log ‖WithLp.toLp 2 (v y')‖) y =
        (e.factorial : ℝ) / Real.pi ^ e * gramVol v y / ‖WithLp.toLp 2 (v y)‖ ^ (2 * (e + 1))

end GroundTheory.Heights₂.Heights
