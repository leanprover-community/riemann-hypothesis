module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrame
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

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.firstVertex_iteratedLevelChain_in_frame :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (s : ℕ) (t : Type) [Fintype t] [DecidableEq t]
      (κ : ℕ) (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin (s + 1))),
    ((∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ γ : GL (Fin κ) k,
        u * embX (s + 1) γ ∈ P.J → ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
      (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb → IsUpperUnip Fin.val gb.val →
        ∃ hm : embX (s + 1) γ ∈ P.J,
          (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
      ∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ hm : u ∈ P.J,
        (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) →
    ∀ (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (c : ℕ) (H : 0 + c = s + 1),
      (prX (Cgrp ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J 1) :
        Set (GL (XIx (Fin κ) t 0) k)) = colGroup (k := k) κ t ∧
      (∀ γ ∈ colGroup (k := k) κ t,
        ∃ hm : embX c γ ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J,
          (((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨_, hm⟩ : ℂ) =
            colChar ψ ϖ γ) ∧
      ∀ u ∈ N k (XIx (Fin κ) t 0) c 1,
        ∀ hm : u ∈ ((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).J,
          (((_root_.GlobalTheory.StepData.typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨u, hm⟩ : ℂ) =
            ψ (simpleSum u) := by
  first | exact @GlobalTheory.FirstVertexFrame.firstVertex_typeChain | exact GlobalTheory.FirstVertexFrame.firstVertex_typeChain | (intros; apply GlobalTheory.FirstVertexFrame.firstVertex_typeChain <;> assumption)
