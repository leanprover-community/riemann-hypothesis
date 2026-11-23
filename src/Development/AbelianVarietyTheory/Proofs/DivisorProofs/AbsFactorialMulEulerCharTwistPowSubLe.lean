module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEvalSubTopLe
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
import Mathlib.Tactic.Basify
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

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem abs_factorial_mul_chi_twist_lbPow_sub_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, L.IsLB → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * chi k (twist F (lbPow L m)) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  intro k _ _ X _ hproj d F _ hsupp L hL
  have hv : DiffVanish (d + 1) (chiPic k F) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) F hproj hsupp
  obtain ⟨p, hpdeg, hpeval, hpcoeff⟩ := hv.exists_polynomial_int ℚ (cls L hL) 0
  obtain ⟨C, hC⟩ := abs_factorial_mul_eval_sub_top_le d p hpdeg
  refine ⟨C, fun m => ?_⟩
  have hmd : multiDiff (fun _ : Fin d => cls L hL) (chiPic k F) 0 =
      interNum k F (fun _ : Fin d => L) :=
    hv.multiDiff_chiPic (L := fun _ : Fin d => L) (by simp) (fun _ => hL) 0
  have hchi : chi k (twist F (lbPow L m)) = chiPic k F ((m : ℤ) • cls L hL) := by
    rw [← twistZ_natCast]
    exact chi_twistZ k F hL (m : ℤ)
  have heval : p.eval (m : ℚ) = (chi k (twist F (lbPow L m)) : ℚ) := by
    have e := hpeval (m : ℤ)
    rw [zero_add, ← hchi, Int.cast_natCast] at e
    exact e
  have hfac : (d.factorial : ℚ) * p.coeff d = (interNum k F (fun _ : Fin d => L) : ℚ) := by
    rw [hpcoeff, hmd, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast d.factorial_ne_zero), one_mul]
  have h := hC m
  rw [heval, hfac] at h
  have h' : ((|(d.factorial : ℤ) * chi k (twist F (lbPow L m)) -
      interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| : ℤ) : ℚ) ≤
      ((C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) : ℤ) : ℚ) := by
    push_cast
    exact h
  exact_mod_cast h'

end GlobalTheory
