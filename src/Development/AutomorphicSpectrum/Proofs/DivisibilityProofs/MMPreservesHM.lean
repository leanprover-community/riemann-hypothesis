module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct SchwartzMap LineDeriv ContDiff Matrix Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Lie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] in
private theorem conj_extensionEmbedding_of_isReal {w : InfinitePlace F} (hw : w.IsReal) (y : w.Completion) :
    starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w y) =
      InfinitePlace.Completion.extensionEmbedding w y := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw y]
  exact Complex.conj_ofReal _

theorem piInf_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piInf τ (cA σ x) = (starRingEnd ℂ) (piInf τ x) := by
  obtain ⟨hF, -, -, hστ⟩ := h
  induction x using TensorProduct.inductionOn with
  | tmul a e =>
    rw [show cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e by simp [cA]]
    change InfinitePlace.Completion.extensionEmbedding w (evInf F w a) * τ.1 (σ e) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w (evInf F w a) * τ.1 e)
    rw [map_mul, conj_extensionEmbedding_of_isReal (hF.isReal w), starRingEnd_apply, hστ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  simp [piInf, compInf, infEmb, inclR]

end GlobalTheory.CompanionTheory.Ar.RT.Lie

end
