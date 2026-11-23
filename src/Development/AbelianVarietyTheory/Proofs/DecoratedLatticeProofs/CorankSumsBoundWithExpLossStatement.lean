module

public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSumsBoundWithExpLoss
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.corankSums_bound_with_expLoss : ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ), Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k m f b g v NT 1 → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k m f b v NT Xi → 0 ≤ Gam → Gam ≤ Real.exp ((k : ℝ) / 8) → ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Gam Xi ≤ (Real.sqrt g)⁻¹ ^ (k * f) ∧ ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k m f s b g v Gam Xi ≤ Real.exp (-((k : ℝ) * f * Real.log k) / 2) := by
  first | exact @GlobalTheory.Core.Deg.corankSums_expLoss | exact GlobalTheory.Core.Deg.corankSums_expLoss | (intros; apply GlobalTheory.Core.Deg.corankSums_expLoss <;> assumption)
