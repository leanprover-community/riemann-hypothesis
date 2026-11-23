module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.UniformTransfer.UnitaryIntegralLevel
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
import Development.WeilBound.ThetaLifts.LatticeBasics.FarRight

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisUnif.EIdemP

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eSF_eq (S : Finset (Pl F)) : eSF S = ((1, ∑ v ∈ S, singleFin v 1) : AF F) := by
  simp only [eSF, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]

open Classical in
theorem evalV_sum (S : Finset (Pl F)) (u : Pl F) :
    evalV F u (∑ v ∈ S, singleFin v 1) = if u ∈ S then 1 else 0 := by

  rw [map_sum]
  have hs : ∀ v : Pl F, evalV F u (singleFin v 1) = if u = v then 1 else 0 := by
    intro v
    have e1 : evalV F u (singleFin v 1) = (singleFin v (1 : Fv F v) : Af F) u := rfl
    have e2 : (singleFin v (1 : Fv F v) : Af F) = singleV F v 1 := rfl
    rw [e1, e2]
    unfold singleV
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl]
      exact RestrictedProduct.single_eq_same _ _ _
    · rw [if_neg huv]
      exact RestrictedProduct.single_eq_of_ne _ _ huv
  simp only [hs]
  rw [Finset.sum_ite_eq]

end GlobalTheory.CompanionTheory.RgEisUnif.EIdemP
