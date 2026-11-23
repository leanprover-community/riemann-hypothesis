module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureOrthogonalBasesPlaneCompare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.adelicTwoStepMeasure_orthogonalBases_plane_compare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x₁ : Fin 1 → Fin (M + 1) → E) (a₁ : F) (B₁ : Matrix (Fin (M + 1)) (Fin M) E) (J₁' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (a₂ : F) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (y₁ y₂ : Fin 1 → Fin M → E) (b₁ b₂ : F) (γ : GL (Fin 2) E), StepData σ J x₁ a₁ B₁ J₁' → StepData σ J x₂ a₂ B₂ J₂' → b₁ ≠ 0 → b₂ ≠ 0 → hE σ J₁' (y₁ 0) (y₁ 0) = algebraMap F E b₁ → hE σ J₂' (y₂ 0) (y₂ 0) = algebraMap F E b₂ → ![x₂ 0, B₂.mulVec (y₂ 0)] = lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] → ∀ (ν₁ ν₂ : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν₁' ν₂' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (N₁ N₂ : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)), IsStdX s σ J a₁ ν₁ → IsStdX s σ J₁' b₁ ν₁' → IsStdX s σ J a₂ ν₂ → IsStdX s σ J₂' b₂ ν₂' → TwoStep (AF F) σ J x₁ B₁ ν₁ ν₁' N₁ → TwoStep (AF F) σ J x₂ B₂ ν₂ ν₂' N₂ → N₂ = N₁.map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)))) := by
  first | exact @GlobalTheory.GaugeEx.twoStep_adelic_swap | exact GlobalTheory.GaugeEx.twoStep_adelic_swap | (intros; apply GlobalTheory.GaugeEx.twoStep_adelic_swap <;> assumption)
