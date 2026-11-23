module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.Algebra.GroupWithZero.Action.Regular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelTor

theorem sFam_charZero_affineOpen : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (U : F.X.affineOpens),
    Nontrivial Γ(F.X, U) → CharZero Γ(F.X, U) := by
  intro g n F U hU
  have hW : IsAffineOpen (U : F.X.Opens) := U.2
  have : SmoothOfRelativeDimension (g * (g + 1) / 2) F.s := F.smooth
  have : Smooth F.s := by first | exact SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s | exact F.smooth.smooth | infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW.fromSpec ≫ F.s)
  have h₁ : φ.hom.Flat := by rw [← Flat.SpecMap_iff, hφ]; infer_instance
  letI : Algebra (cycAway n) Γ(F.X, U) := φ.hom.toAlgebra
  have : Module.Flat (cycAway n) Γ(F.X, U) := h₁
  refine charZero_of_inj_zero fun k hk => by_contra fun h0 => ?_
  have hk' : ((k : cycAway n) : ℂ) ≠ 0 := by simpa using h0
  have hne : (k : cycAway n) ≠ 0 := fun h => hk' (by rw [h]; rfl)
  have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(F.X, U)) (r := (k : cycAway n))
    (mem_nonZeroDivisors_of_ne_zero hne)).right_eq_zero_of_smul (x := 1) (by rw [Algebra.smul_def, _root_.mul_one, map_natCast]; exact hk)
  exact one_ne_zero this

end GlobalTheory.SiegelTor
