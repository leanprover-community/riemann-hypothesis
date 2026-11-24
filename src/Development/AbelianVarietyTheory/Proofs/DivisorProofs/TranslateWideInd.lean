module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom
variable {F : Type} [Field F] [NumberField F]


open Classical in
def cls (I : Ideal (𝓞 F)) : ClassGroup (𝓞 F) := if h : I ∈ (Ideal (𝓞 F))⁰ then ClassGroup.mk0 ⟨I, h⟩ else 1


open Classical in
def wideInd (C : ClassGroup (𝓞 F)) : Ideal (𝓞 F) → ℚ := fun I => if cls I = C then 1 else 0

theorem cls_of_ne_bot {I : Ideal (𝓞 F)} (h : I ≠ ⊥) :
    cls I = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero h⟩ := by
  rw [cls, dite_eq_left]

theorem cls_mul {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : cls (I * J) = cls I * cls J := by
  rw [cls_of_ne_bot hI, cls_of_ne_bot hJ, cls_of_ne_bot (mul_ne_zero hI hJ), ← map_mul]
  rfl

theorem cls_span {a : 𝓞 F} (ha : a ≠ 0) : cls (Ideal.span {a}) = 1 := by
  have h : Ideal.span {a} ≠ ⊥ := by simpa using ha
  rw [cls_of_ne_bot h, ClassGroup.mk0_eq_one_iff]
  exact ⟨⟨a, rfl⟩⟩

theorem cls_span_mul {a : 𝓞 F} (ha : a ≠ 0) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : cls (Ideal.span {a} * I) = cls I := by
  rw [cls_mul (by simpa using ha) hI, cls_span ha, one_mul]

theorem isRayFun_wideInd (𝔣 : Ideal (𝓞 F)) (C : ClassGroup (𝓞 F)) : IsRayFun 𝔣 (wideInd C) := by
  intro I J hI hJ e
  obtain ⟨a, b, ha, hb, -, -, -, e⟩ := e
  have : cls I = cls J := by rw [← cls_span_mul ha hI.1, e, cls_span_mul hb hJ.1]
  unfold wideInd
  rw [this]

theorem translate_wideInd {a : 𝓞 F} (ha : a ≠ 0) (C : ClassGroup (𝓞 F)) :
    GlobalTheory.RayZeta.translate (Ideal.span {a}) (wideInd C) = wideInd C := by
  funext I
  by_cases hI : I = ⊥
  · simp [GlobalTheory.RayZeta.translate, hI]
  · simp only [GlobalTheory.RayZeta.translate, wideInd]
    rw [cls_span_mul ha hI]

end GlobalTheory.ZetaDenom
