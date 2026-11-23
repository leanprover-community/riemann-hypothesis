module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceCoordSqSumLeHilbertSchmidtUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.traceCoord_sq_sum_le_hilbertSchmidt_unitaryGroup : ∀ (n d : ℕ) (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ i, Formalism.REAL.inG ε (E i)) → ∀ g : Formalism.REAL.UJ ε, (uMat g - 1) - Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε ∈ Submodule.span ℝ (Set.range E) → ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 ≤ Formalism.REAL.hs (uMat g - 1) ∧ Formalism.REAL.hs (uMat g - 1) ≤ ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 + Formalism.REAL.hs (uMat g - 1) ^ 2 / 4 := by
  first | exact @GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le | exact GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le | (intros; apply GlobalTheory.NilCov.sum_coord_sq_le_hs_and_hs_le <;> assumption)
