module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem baseChangeAlgebraRepresentationAction_injective {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hrep : Function.Injective rep) (R : Type) [CommRing R] [Algebra ℚ R] :
    Function.Injective (actOn rep R) := by
  classical
  set b := Module.finBasis ℚ V
  let g : C →ₗ[ℚ] (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V) → ℚ) :=
    LinearMap.pi (fun ij => (b.coord ij.2).comp ((LinearMap.applyₗ (b ij.1)).comp rep.toLinearMap))
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hrep
    rw [map_zero]
    refine b.ext (fun i => b.ext_elem (fun j => ?_))
    have := congrFun hx (i, j)
    simpa [g] using this
  have hlg : Function.Injective (LinearMap.lTensor R g) :=
    Module.Flat.lTensor_preserves_injective_linearMap g hg
  have key : ∀ (y : R ⊗[ℚ] C) (i j : Fin (Module.finrank ℚ V)),
      TensorProduct.piScalarRight ℚ R R _ (LinearMap.lTensor R g y) (i, j) =
        TensorProduct.rid ℚ R (LinearMap.lTensor R (b.coord j) (actOn rep R y ((1 : R) ⊗ₜ b i))) := by
    intro y i j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have h1 : actOn rep R (r ⊗ₜ x) ((1 : R) ⊗ₜ b i) = r ⊗ₜ (rep x (b i)) := by
        simp only [actOn, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply]
        change r • ((rep x).baseChange R ((1 : R) ⊗ₜ b i)) = _
        rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]
      simp [g, Algebra.smul_def]
    | add y z hy hz => simp only [map_add (f := _), Pi.add_apply, LinearMap.add_apply, hy, hz]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  apply hlg
  rw [map_zero]
  apply (TensorProduct.piScalarRight ℚ R R _).injective
  rw [map_zero]
  funext ij
  rw [key, hy]
  simp

theorem actOn_rep_afP_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G),
    Function.Injective (actOn L.rep (AfP p)) := by
  intro p _ D G L
  haveI := D.finLa
  exact baseChangeAlgebraRepresentationAction_injective L.rep L.rep_inj (AfP p)

end GlobalTheory.LKGeo
