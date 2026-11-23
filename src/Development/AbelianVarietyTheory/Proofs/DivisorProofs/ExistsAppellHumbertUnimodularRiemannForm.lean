module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Hermitian
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.PolUnif

theorem hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (x : Fin g → ℂ) :
    (hermForm Hm x x).im = 0 := by
  have h := hH.im_star_dotProduct_mulVec_self (star x)
  rw [star_star] at h
  exact h

theorem exists_unif_riemannForm : ∀ (h : ℕ) (P : Out.PolAV (Sp ℂ)), P.g = h → ∃ (u : HolUnif P.A P.L h) (Hm : Matrix (Fin h) (Fin h) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ ∧ (∀ x y : u.Λ, (Ef x y : ℝ) = (hermForm Hm x y).im) ∧ Function.Bijective Ef ∧ (∀ x, Ef x x = 0) ∧ Module.Free ℤ u.Λ ∧ Module.Finite ℤ u.Λ ∧ Module.finrank ℤ u.Λ = 2 * h ∧ ∀ (n : ℕ) (x y : u.Λ) (e : ℂˣ), 0 < n → (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / n) → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((n : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e) := by
  intro h P hg
  subst hg
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hbij, hW⟩ := GlobalTheory.thetaUnifAV_all P rig hrig
  haveI : DiscreteTopology u.Λ := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  refine ⟨u, Hm, χ, Ef, hAH, hE, hbij, fun x => ?_, ZLattice.module_free ℝ u.Λ, ZLattice.module_finite ℝ u.Λ, ?_, hW⟩
  · have h1 := hE x x
    rw [hermForm_self_im hAH.1] at h1
    exact_mod_cast h1
  · rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]

end GlobalTheory.PolUnif
