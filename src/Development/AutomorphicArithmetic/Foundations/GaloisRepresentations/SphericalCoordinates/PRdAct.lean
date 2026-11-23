module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem actOn_inC {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (c : G.C) (w : VQ D) :
    actOn L.rep (AfP p) (inC G (AfP p) c) ((1 : AfP p) ⊗ₜ w) = (1 : AfP p) ⊗ₜ (L.rep c w) := by
  simp only [actOn, inC, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  erw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, one_mul, Module.End.baseChangeHom, AlgHom.comp_apply]
  exact LinearMap.baseChange_tmul _ _ _

private theorem actG_toAf {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (B : GlobalTheory.LKCx.Form G)
    (y : GlobalTheory.LKCx.grp G B.β) (w : VQ D) :
    L.actG (B.toAf y) (actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ w)) =
      actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) w)) := by
  have hval : (L.actG (B.toAf y) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
      = actOn L.rep (AfP p) ((trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := rfl
  rw [hval, ← Module.End.mul_apply, ← map_mul,
    show (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (trivX B : AfP p ⊗[ℚ] G.C)
        = (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) by
      simp [mul_assoc],
    map_mul, Module.End.mul_apply, actOn_inC]

theorem rdAct_of : RdAct := by
  intro p _ D G L B y h₁ h₂ w
  simp only [rd, actY]
  conv_rhs =>
    rw [← Module.End.mul_apply, ← map_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one, map_mul,
      Module.End.mul_apply, actG_toAf]

end UpperTheory.Gal.W2
