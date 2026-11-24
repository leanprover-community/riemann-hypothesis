module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.TensorProduct.Maps
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

section Ring

variable (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]

abbrev Op : Type := ℤ_[p] ⊗[ℤ] OE

def bar [StarRing OE] : Op p OE ≃ₐ[ℤ_[p]] Op p OE :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p])
    (AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut OE)) (fun n => by simp))

variable {p OE}

def extend {O : Type} [CommRing O] [Algebra ℤ_[p] O] (σ : OE →+* O) : Op p OE →ₐ[ℤ_[p]] O :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] O) σ.toIntAlgHom (fun _ _ => Commute.all _ _)

end Ring

@[ext] structure Place (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] where

  e : Op p OE
  idem : IsIdempotentElem e
  ne_zero : e ≠ 0
  primitive : ∀ f : Op p OE, IsIdempotentElem f → f * e = f → f = 0 ∨ f = e

namespace Place

variable {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]

abbrev Ow (w : Place p OE) : Type := Op p OE ⧸ Ideal.span {1 - w.e}

def toOw (w : Place p OE) : OE →+* w.Ow :=
  (Ideal.Quotient.mk _).comp
    (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] Op p OE).toRingHom

end Place

section Gauss

variable {p : ℕ} [Fact p.Prime]

end Gauss

end GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
