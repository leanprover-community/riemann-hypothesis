module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerCovolumeProductPowTwoSidedBounds
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.layer_covolume_product_pow_two_sided_bounds : ∀ (v : ℝ) (f k r m a b : ℕ) (x : ℝ≥0∞), 1 ≤ v → m ≤ r → a ≤ r ^ 2 → b ≤ r ^ 2 → ENNReal.ofReal ((8 * v) ^ (-(f : ℝ))) ^ m ≤ x → x ≤ ENNReal.ofReal ((8 * v) ^ (f : ℝ)) ^ m → ENNReal.ofReal (v ^ (k * m * f) / (8 * v) ^ (2 * (r + 1) ^ 2 * f)) ≤ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ∧ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ≤ ENNReal.ofReal (v ^ (k * m * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) := by
  first | exact @GlobalTheory.DegVol.RefCov.prod_pow_bounds | exact GlobalTheory.DegVol.RefCov.prod_pow_bounds | (intros; apply GlobalTheory.DegVol.RefCov.prod_pow_bounds <;> assumption)
