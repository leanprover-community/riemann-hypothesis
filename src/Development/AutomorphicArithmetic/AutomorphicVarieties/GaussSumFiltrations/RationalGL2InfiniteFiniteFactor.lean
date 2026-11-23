module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRatDetPos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.RatPts

theorem pInf_algebraMap (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    TR.pInf F (algebraMap F (Ad F) x) = rhom x := by
  funext v
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
    ((algebraMap F (Ad F) x).1 v) = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x
  rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  simpa using InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe
    (IsTotallyReal.isReal v) (WithAbs.toAbs _ x)

theorem pInf_ratGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) = toInf γ := by
  ext i j v
  exact congrFun (pInf_algebraMap F (γ i j)) v

theorem ratGL_real_fin : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F),
    ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧
      ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  intro F _ _ _ γ
  refine ⟨?_, fun h => ?_⟩
  · rw [← pInf_ratGL]
    exact (TR.infGL_mul_finGL (ratGL F 2 γ)).symm
  · obtain ⟨τ, hτ⟩ := GlobalTheory.WeakApproxGL.exists_rat_det_pos F 2 h
    refine ⟨τ, fun v => ?_⟩
    have e := hτ v
    rwa [MonoidHom.comp_apply, pInf_ratGL] at e

end GlobalTheory.HilbertThetaSeries.RatPts

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.rational_GL2_infinite_finite_factor : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F), ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  first | exact @GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | exact GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | (intros; apply GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin <;> assumption)
