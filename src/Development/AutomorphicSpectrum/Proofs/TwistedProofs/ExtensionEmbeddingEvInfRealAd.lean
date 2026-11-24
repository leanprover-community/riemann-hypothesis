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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.CompanionTheory.RealAdeleComponent

open scoped TensorProduct
open GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem extensionEmbedding_evInf_realAd {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F t)) = (t : ℂ) := by
  have h := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t)
  have e : evInf F w (realAd F t) = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t)) w := rfl
  rw [e]
  generalize (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t) = y at h
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
  by_cases hw : w.IsReal
  · have h1 := congrFun (congrArg Prod.fst h) ⟨w, hw⟩
    have h2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (y w) = t := h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, h2]
  · have h1 := congrFun (congrArg Prod.snd h) ⟨w, InfinitePlace.not_isReal_iff_isComplex.1 hw⟩
    exact h1

theorem piInf_realAd_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) (t : ℝ) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • x) = (t : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  | tmul a e =>
    have h : ∀ b : AF F, piInf τ (b ⊗ₜ[F] e) =
        InfinitePlace.Completion.extensionEmbedding w (evInf F w b) * τ.1 e := fun b => rfl
    rw [TensorProduct.smul_tmul', smul_eq_mul, h, h, map_mul, map_mul, extensionEmbedding_evInf_realAd, mul_assoc]

end GlobalTheory.CompanionTheory.RealAdeleComponent

end
