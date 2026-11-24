module

public import GroundTheory.GlobalFields.NormResidueSymbol.RationalCyclotomic
public import GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import GroundTheory.GlobalFields.NormResidueSymbol.RationalContinuous
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup Topology
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace DirichletHecke

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

abbrev modulus (N : ℕ) [NeZero N] : ℕ+ := ⟨N, Nat.pos_of_neZero N⟩

def unitsMod (N : ℕ) [NeZero N] : ℤ̂ˣ →* (ZMod N)ˣ :=
  Units.map (ProfiniteInteger.proj (modulus N)).toMonoidHom

def toCircle : (ZMod N)ˣ →* Circle where
  toFun a := ⟨χ a, mem_sphere_zero_iff_norm.2 (χ.unit_norm_eq_one a)⟩
  map_one' := Circle.ext (by simp)
  map_mul' a b := Circle.ext (by simp only [Units.val_mul, map_mul]; rfl)


def galoisCharacter : Gal(maxCyclotomic/ℚ) →* Circle :=
  (toCircle χ).comp ((unitsMod N).comp cycCharacter.toMonoidHom)

theorem coe_galoisCharacter (σ : Gal(maxCyclotomic/ℚ)) :
    (galoisCharacter χ σ : ℂ) = χ (ProfiniteInteger.proj (modulus N) (cycCharacter σ : ℤ̂)) :=
  rfl

theorem continuous_toCircle_unitsMod : Continuous fun u : ℤ̂ˣ ↦ toCircle χ (unitsMod N u) := by
  have h : Continuous fun u : ℤ̂ˣ ↦ (χ (ProfiniteInteger.proj (modulus N) (u : ℤ̂)) : ℂ) :=
    continuous_of_discreteTopology.comp
      ((ProfiniteInteger.continuous_proj _).comp Units.continuous_val)
  exact continuous_induced_rng.2 h

def heckeCharacter : HeckeCharacter ℚ where
  toMonoidHom := (galoisCharacter χ).comp reciprocityMap
  continuous_toFun := by
    have h : ⇑((galoisCharacter χ).comp reciprocityMap) =
        (fun u : ℤ̂ˣ ↦ toCircle χ (unitsMod N u)) ∘ fun x ↦ (unitPart x)⁻¹ := by
      funext x
      simp [galoisCharacter, cycCharacter_reciprocityMap]
    change Continuous ((galoisCharacter χ).comp reciprocityMap : IdeleClassGroup ℚ → Circle)
    rw [h]
    exact (continuous_toCircle_unitsMod χ).comp continuous_unitPart.inv

theorem heckeCharacter_apply (x : IdeleClassGroup ℚ) :
    heckeCharacter χ x = galoisCharacter χ (reciprocityMap x) :=
  rfl

theorem coe_heckeCharacter_apply (x : IdeleClassGroup ℚ) :
    (heckeCharacter χ x : ℂ) = χ (ProfiniteInteger.proj (modulus N) ((unitPart x)⁻¹ : ℤ̂ˣ)) := by
  rw [heckeCharacter_apply, coe_galoisCharacter, cycCharacter_reciprocityMap]

end DirichletHecke

end

end GroundTheory.Global
