module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
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

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem ofCard_symm_apply_eq_sort {n : ℕ} (s : Finset (Fin n)) (k : ℕ) (hk : k < s.card) :
    Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (rfl : s.card = s.card)) ⟨k, hk⟩ =
      (s.sort (· ≤ ·))[k]'(by rw [Finset.length_sort]; exact hk) := by
  show s.orderEmbOfFin rfl ⟨k, hk⟩ = _
  rw [Finset.orderEmbOfFin_apply]
  rfl

noncomputable def dlogBasis {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    Module.Basis (Fin n) K Ω[K⁄ℤ] :=
  (Module.Basis.mk hx.1 (by rw [hx.2])).unitsSMul fun i => (x i)⁻¹

theorem dlogBasis_apply {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) (i : Fin n) :
    dlogBasis x hx i = dlog (x i) := by
  rw [dlogBasis, Module.Basis.unitsSMul_apply, Module.Basis.mk_apply, Units.smul_def]
  rfl

theorem logWedge_eq_basis {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    logWedge x = ⇑(dlogBasis x hx).ExteriorAlgebra := by
  funext s
  rw [ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    logWedge]
  congr 1
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_ofFn, Function.comp_apply, dlogBasis_apply]
    rw [ofCard_symm_apply_eq_sort]

theorem logWedge_basis : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ), IsCoord x →
    LinearIndependent K (logWedge x) ∧ Submodule.span K (Set.range (logWedge x)) = ⊤ := by
  intro K _ n x hx
  rw [logWedge_eq_basis x hx]
  exact ⟨(dlogBasis x hx).ExteriorAlgebra.linearIndependent, (dlogBasis x hx).ExteriorAlgebra.span_eq⟩

end GlobalTheory.LogDR
