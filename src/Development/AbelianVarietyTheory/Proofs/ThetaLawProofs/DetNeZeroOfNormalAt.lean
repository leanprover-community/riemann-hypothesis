module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyEq

theorem det_ne_zero_of_normalAt (hU : ThetaUnifAV) (x : KeyIn ℂ) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c : ℂ} (h : NormalAt x τ M a b c) : M.det ≠ 0 := by
  obtain ⟨u, -, -, -, -, -, h₆⟩ := h
  obtain ⟨u₀, -, -, -, -, -, -, hd, -⟩ := hU x.P x.rig x.rig_gen
  have := x.P.isAb.comm
  obtain ⟨hex, htan, -⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  intro h0
  obtain ⟨d, hd0, hdM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have key : ∀ (e : Fin x.P.g → ℂ) (w), Matrix.vecMul e M = 0 → IsLieComb e x.v w → u₀.IsDiff 0 w := by
    intro e w he hw
    have h1 := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v e w x.basis.1 h₆ hw
    have e1 : ∑ j, e j • (2 * Real.pi * Complex.I : ℂ)⁻¹ • M j =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • Matrix.vecMul e M := by
      rw [Matrix.vecMul_eq_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    rw [e1, he, smul_zero] at h1
    intro U hU' f
    rw [h1 U hU' f, map_zero, map_zero]
  obtain ⟨w, hw⟩ := (hex d).exists
  obtain ⟨w', hw'⟩ := (hex 0).exists
  have hww : w = w' := (hd 0).unique ⟨htan _ _ hw, key _ _ hdM hw⟩
    ⟨htan _ _ hw', key _ _ (Matrix.zero_vecMul M) hw'⟩
  subst hww
  exact hd0 ((x.basis.2 w (htan _ _ hw)).unique hw hw')

end GlobalTheory.KeyEq
end
