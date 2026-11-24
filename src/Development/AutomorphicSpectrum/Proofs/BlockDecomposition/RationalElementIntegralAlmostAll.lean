module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocalHypotheses

theorem eventually_val_le_one (E : Type) [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : Pl E in cofinite, Valued.v (algebraMap E (w.adicCompletion E) x) ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 E) x
  rw [Filter.eventually_cofinite]
  refine h.subset fun w hw => ?_
  have hw' : ¬ Valued.v ((x : E) : w.adicCompletion E) ≤ 1 := hw
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', not_le] at hw'
  exact hw'

theorem ratW_mem_KGL_eventually (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E) :
    ∀ᶠ w : Pl E in cofinite, ratW n w δ ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hall : ∀ M : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j : Fin n,
      Valued.v (algebraMap E (w.adicCompletion E) ((M : Matrix (Fin n) (Fin n) E) i j)) ≤ 1 := by
    intro M
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact eventually_val_le_one E _
  filter_upwards [hall δ, hall δ⁻¹] with w h1 h2
  rw [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val]
  refine ⟨fun i j => h1 i j, fun i j => ?_⟩
  have key : (ratW n w δ)⁻¹ = ratW n w δ⁻¹ := (map_inv (ratW n w) δ).symm
  rw [key]
  exact h2 i j

end GlobalTheory.CompanionTheory.LocalHypotheses
