module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal.Cmp

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

def ren (π : Equiv.Perm (Fin g)) : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ π).toContinuousLinearEquiv

theorem ren_apply (π : Equiv.Perm (Fin g)) (z : Fin g → ℂ) : ren π z = z ∘ π := rfl

theorem ren_single (π : Equiv.Perm (Fin g)) (j : Fin g) : ren π (Pi.single j 1) = Pi.single (π.symm j) 1 := by
  funext i
  rw [ren_apply, Function.comp_apply]
  by_cases h : i = π.symm j
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    exact h (by rw [← h']; simp)

section Rename₂

variable (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (π : Equiv.Perm (Fin g))
  (x : Frame X.Ψ r)

theorem pv_ren (v : Fin r → E) : pv X (π.trans idx) x v = ren π (pv X idx x v) := rfl

private theorem perMat_trans_idx_eq_submatrix (s : Fin g → Fin g ⊕ Fin g) :
    perMat X bas (π.trans idx) s x = (perMat X bas idx s x).submatrix π (Equiv.refl _) := by
  ext i k
  simp [perMat_apply]

theorem hMat_ren : hMat X bas (π.trans idx) x = (hMat X bas idx x).submatrix (Equiv.refl _) π := by
  simp only [hMat]
  rw [perMat_trans_idx_eq_submatrix, Matrix.inv_submatrix_equiv]

theorem hMat_mulVec_ren (z : Fin g → ℂ) : hMat X bas (π.trans idx) x *ᵥ ren π z = hMat X bas idx x *ᵥ z := by
  rw [hMat_ren, ren_apply, Matrix.submatrix_mulVec_equiv]
  ext i
  simp [Function.comp_def]

theorem tauMat_ren : tauMat X bas (π.trans idx) x = tauMat X bas idx x := by
  simp only [tauMat]
  rw [hMat_ren, perMat_trans_idx_eq_submatrix, Matrix.submatrix_mul_equiv]
  simp

theorem imInv_ren : imInv X bas (π.trans idx) x = imInv X bas idx x := by
  simp only [imInv, tauMat_ren]

theorem hx_ren (z w : Fin g → ℂ) : hx X bas (π.trans idx) x (ren π z) (ren π w) = hx X bas idx x z w := by
  simp only [hx, hMat_mulVec_ren, imInv_ren]

variable {X bas idx x}

def anFibRen [Algebra c.F ℂ] {e : Fin g ≃ Lt1 Dw} {L : Lt E r} {y : FrPt Xo c ℂ}
    (A : AnFib X bas (π.trans idx) (π.trans e) x L y) : AnFib X bas idx e x L y where
  ex z := A.ex (ren π z)
  ex_add z w := by rw [map_add (f := _), A.ex_add]
  ex_onto := A.ex_onto.comp (ren π).surjective
  ex_ker z := by simp only [A.ex_ker, pv_ren, (ren π).injective.eq_iff]
  ex_lin a z := A.ex_lin a (ren π z)
  hol U f := ⟨(A.hol U f).1.preimage (ren π).continuous,
    (A.hol U f).2.comp (ren π).differentiable.differentiableOn fun _ h => h⟩
  der ℓ := by
    refine ⟨by simpa only [map_zero] using (A.der ℓ).1, fun U h f => ((A.der ℓ).2 U h f).trans ?_⟩
    have := (ren π).comp_right_fderiv (f := fun z => valAt' (A.ex z).left U f) (x := 0)
    rw [map_zero] at this
    change _ = fderiv ℂ ((fun z => valAt' (A.ex z).left U f) ∘ ren π) 0 _
    rw [this, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ren_single]
    rfl
  fr j z := A.fr j (ren π z)
  fr_hol j := (A.fr_hol j).comp (ren π).differentiable.differentiableOn fun _ h => h
  fr_ne j z := A.fr_ne j _
  fr_g j j' z := A.fr_g j j' _
  fr_0 j := by rw [map_zero]; exact A.fr_0 j
  χ := A.χ
  χ_norm := A.χ_norm
  fr_per v hv j z h := by
    rw [A.fr_per v hv j _ h, pv_ren, hx_ren, hx_ren, map_add (f := _)]

end Rename₂

end

end GlobalTheory.ClsVal.Cmp
