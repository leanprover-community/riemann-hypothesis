module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundSemiPosNefOnFibresStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithNefVolumeUpperBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVarietyStatement
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem arithHilbertSamuel_of_ampleHS :
    GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → GlobalTheory.Published.ArithHilbertSamuel := by
  intro hC hA hS k _ X _ p D hX L N a hL ha
  refine ⟨Eventually.of_forall fun m => GlobalTheory.T.finite_smallSec_hermitian_line_bundle_arith_variety k X p D hX _, ?_⟩
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  have hupper : ∀ᶠ m : ℕ in atTop,
      Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤
        (a / (D + 1).factorial + c) * (m : ℝ) ^ (D + 1) :=
    GlobalTheory.T.arith_nef_volume_upper_bound hC hA hS k X p D hX L N a hL ha c hc
  have hlower : ∀ᶠ m : ℕ in atTop,
      (a / (D + 1).factorial - c) * (m : ℝ) ^ (D + 1) ≤
        Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) :=
    GlobalTheory.T.arithHilbertSamuel_lowerBound_semiPos_nefOnFibres hC hA k X p D hX L N a (nefFib_of_isNef hL) hL.semiPos ha c hc
  filter_upwards [hupper, hlower] with m h1 h2
  have hm : ‖(m : ℝ) ^ (D + 1)‖ = (m : ℝ) ^ (D + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs, hm, abs_le]
  constructor <;> linarith

end GlobalTheory.HSNef
