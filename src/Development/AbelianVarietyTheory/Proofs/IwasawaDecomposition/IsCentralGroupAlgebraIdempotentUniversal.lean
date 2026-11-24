module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TupOfOneMemLabT
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem eIdem_all : ∀ D : D7, EIdem D := by
  intro D
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let φ : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp (algebraMap ↥D.LL0 D.what₂.LL)
  have hφ : Function.Injective φ := φ.injective
  let M := MonoidAlgebra.mapRingHom (G0g D.nd) φ
  have hM : Function.Injective M := by
    intro x y h
    refine MonoidAlgebra.ext (Finsupp.ext fun g => hφ ?_)
    have := congrArg (fun z => z.coeff g) h
    simpa [M, MonoidAlgebra.mapRingHom] using this
  have he : M (eL D) = D.ntypes.e0 := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    have := D.nStage_trivialCharacter_coeff_eq g
    simpa [M, eL, MonoidAlgebra.mapRingHom, φ] using this
  have hc : ∀ a, D.ntypes.e0 * a = a * D.ntypes.e0 := fun a => by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_comm _ a
  have hi : D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_mul_self _
  have hs : ∀ g : G0g D.nd, M (MonoidAlgebra.of _ _ g) = MonoidAlgebra.of _ _ g := fun g => by
    simp [M, MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom]
  refine ⟨hM ?_, fun g => hM ?_⟩
  · rw [map_mul, he, hi]
  · rw [map_mul, map_mul, he, hs, hc]

end GlobalTheory.HeightCounting.FormsStep
