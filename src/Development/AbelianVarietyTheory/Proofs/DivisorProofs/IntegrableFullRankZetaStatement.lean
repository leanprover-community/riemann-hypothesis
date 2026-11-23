module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankZeta
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

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

theorem _root_.GlobalTheory.T.integrable_full_rank_zeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) := by
  first | exact @GlobalTheory.FullRankCoinv.integrable_fibre_target | exact GlobalTheory.FullRankCoinv.integrable_fibre_target | (intros; apply GlobalTheory.FullRankCoinv.integrable_fibre_target <;> assumption)
