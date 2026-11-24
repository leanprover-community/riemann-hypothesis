module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictBlockOrder
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

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.exists_strict_block_order : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N), ∃ β : Fin N → ℕ, ∀ x y, β x < β y ↔ blk e x < blk e y := by
  first | exact @GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk | exact GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk | (intros; apply GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk <;> assumption)
