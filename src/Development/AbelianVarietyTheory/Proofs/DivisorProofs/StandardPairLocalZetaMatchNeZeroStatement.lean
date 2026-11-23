module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairLocalZetaMatchNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.standardPair_localZetaMatch_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c m a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → ν = α / β → 1 ≤ c → GlobalTheory.SplitFlip.CondLE ϖ c ν →
    GlobalTheory.SplitFlip.CondLE ϖ m α → GlobalTheory.SplitFlip.CondLE ϖ m β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') =
        GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') ∧
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') ≠ 0 := by
  first | exact @GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | exact GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | (intros; apply GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB <;> assumption)
