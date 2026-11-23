module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelMovesCosetVectorIntegralPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.blockLevel_moves_cosetVector_integral_point : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 → ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ k ∈ intG D a, W.Om 1 h (cosetV D δ 𝔪 0 a d e0) = c • W.Om k 1 (cosetV D δ 𝔪 0 a d e0) := by
  first | exact @GlobalTheory.FunObj.CosetMove.om_cosetV_block | exact GlobalTheory.FunObj.CosetMove.om_cosetV_block | (intros; apply GlobalTheory.FunObj.CosetMove.om_cosetV_block <;> assumption)
