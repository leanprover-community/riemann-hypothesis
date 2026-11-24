module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isPair_move_by_integralUnipotent : ∀ (D : D7) (T T' : D.host.E) (Λ : LatV D) (g : ℕ) (F : Fg D T) (F' F'' A B : Fg D T') (β n' n'' : (hS D).V ≃ₗ[D.host.E] (hS D).V), IsPair Λ F F' F'' β g → n' ∈ NLam Λ F → n'' ∈ NLam Λ F → FrameEqv D n' F' A → FrameEqv D n'' F'' B → IsAutLam (hS D) Λ (n'' * β * n'⁻¹) ∧ (Xsp A).map ((n'' * β * n'⁻¹ : (hS D).V ≃ₗ[D.host.E] (hS D).V) : (hS D).V →ₗ[D.host.E] (hS D).V) = Xsp B ∧ (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  first | exact @GlobalTheory.LoopC.PairMove.pair_move | exact GlobalTheory.LoopC.PairMove.pair_move | (intros; apply GlobalTheory.LoopC.PairMove.pair_move <;> assumption)
