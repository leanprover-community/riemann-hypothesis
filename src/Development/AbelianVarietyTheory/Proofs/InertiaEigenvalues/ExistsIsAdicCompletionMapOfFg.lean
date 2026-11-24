module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Completeness
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.AdicComplExists

variable {L : Type} [CommRing L] {J : Ideal L}

theorem evalₐ_algebraMap' (n : ℕ) (r : L) :
    AdicCompletion.evalₐ J n (algebraMap L (AdicCompletion J L) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem mem_map_pow_iff (hfg : J.FG) (n : ℕ) (y : AdicCompletion J L) :
    y ∈ (J ^ n).map (algebraMap L (AdicCompletion J L)) ↔ AdicCompletion.evalₐ J n y = 0 := by
  rw [← Submodule.restrictScalars_mem L, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (J ^ n • ⊤ : Ideal L) = J ^ n := by ext x; simp
  exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq L h').injective).symm

end GlobalTheory.BSP.AdicComplExists


open GlobalTheory.BSP.AdicComplExists in
theorem GlobalTheory.BSP.isCompl_exists : ∀ (L : Type) [CommRing L] (J : Ideal L), J.FG →
    ∃ (Q : Type) (_ : CommRing Q) (i : L →+* Q), IsCompl i J := by
  intro L _ J hfg
  refine ⟨AdicCompletion J L, inferInstance, algebraMap L (AdicCompletion J L), ⟨?_, ?_, ?_⟩⟩
  · rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete hfg
  · intro x n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
    exact ⟨r, by rw [mem_map_pow_iff hfg, map_sub, evalₐ_algebraMap', hr, sub_self]⟩
  · intro a n ha
    rw [mem_map_pow_iff hfg, evalₐ_algebraMap'] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha
