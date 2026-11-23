module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankFiltrationStepStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ν ϖ ≠ 1 →
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), ∃ Φ₀ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Φ₀ Y = 0) ∧
      Φ - Φ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} := by
  intro k _ _ _ _ a d _ ν β _ hν ϖ hϖ hνϖ Φ hΦ
  have key : ∀ r ≤ a, Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ)) ⊔
      GlobalTheory.RankCoinv.twistSpan ν β := by
    intro r hr
    induction r with
    | zero => exact Submodule.mem_sup_left ⟨hΦ, fun Y hY => absurd hY (Nat.not_lt_zero _)⟩
    | succ r ih =>
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (ih (by omega))
      have := GlobalTheory.T.low_rank_filtration_step k (Fin a) (Fin d) ϖ hϖ ν β hν hνϖ r (by simpa using hr) x hx
      exact Submodule.add_mem _ this (Submodule.mem_sup_right hy)
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (key a le_rfl)
  refine ⟨x, hx.1, fun Y hY => hx.2 Y (lt_of_le_of_ne (by simpa using Y.rank_le_card_height) hY), ?_⟩
  have e : Φ - x = y := by rw [← hxy]; abel
  rw [e]; exact hy
