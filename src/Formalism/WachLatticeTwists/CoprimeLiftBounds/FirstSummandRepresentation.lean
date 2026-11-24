module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

section Lattices
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]

theorem yY_one (r : G →* A) (χ : G →* T'ˣ) (E : A) : yY r χ E 1 = 0 := by
  apply Subtype.ext
  show ((((χ 1)⁻¹ : T'ˣ) : T') • r 1 - 1) * E = 0
  rw [map_one, map_one, inv_one, Units.val_one, one_smul, sub_self, zero_mul]

theorem yY_mul (r : G →* A) (χ : G →* T'ˣ) (E : A) (g h : G) :
    yY r χ E (g * h) = yY r χ E g + uElt r χ g • yY r χ E h := by
  apply Subtype.ext
  have hc : ∀ k, ycoc r χ E k = (uElt r χ k - 1) * E := fun k => rfl
  show ycoc r χ E (g * h) = ycoc r χ E g + uElt r χ g * ycoc r χ E h
  rw [hc, hc, hc, uElt_mul, sub_mul, sub_mul, sub_mul, mul_sub, one_mul, mul_assoc]
  abel

def ytRep (O : Type*) [CommRing O] [Algebra O A] (r : G →* A) (χ : G →* T'ˣ) (E : A) :
    Representation O G (Ymod r χ E × O) where
  toFun g :=
    { toFun := fun p => (uElt r χ g • p.1 + p.2 • yY r χ E g, p.2)
      map_add' := fun p p' => Prod.ext (by
        show uElt r χ g • (p.1 + p'.1) + (p.2 + p'.2) • yY r χ E g = _ + _
        rw [smul_add, add_smul]; exact add_add_add_comm _ _ _ _) rfl
      map_smul' := fun c p => Prod.ext (by
        show uElt r χ g • (c • p.1) + (c • p.2) • yY r χ E g = c • (_ + _)
        rw [smul_add, smul_comm, smul_assoc]) rfl }
  map_one' := LinearMap.ext fun p => Prod.ext (by
    show uElt r χ 1 • p.1 + p.2 • yY r χ E 1 = p.1
    rw [uElt_one, one_smul, yY_one, smul_zero, add_zero]) rfl
  map_mul' g h := LinearMap.ext fun p => Prod.ext (by
    show uElt r χ (g * h) • p.1 + p.2 • yY r χ E (g * h) =
      uElt r χ g • (uElt r χ h • p.1 + p.2 • yY r χ E h) + p.2 • yY r χ E g
    rw [uElt_mul, yY_mul, mul_smul, smul_add, smul_add, smul_comm (uElt r χ g) p.2]; abel) rfl

def ytEmb (O : Type*) [CommRing O] [Algebra O A] (r : G →* A) (χ : G →* T'ˣ) (E : A) :
    Ymod r χ E × O →ₗ[O] A × O where
  toFun p := ((p.1 : A) + p.2 • E, p.2)
  map_add' p p' := Prod.ext (by
    show ((p.1 + p'.1 : Ymod r χ E) : A) + (p.2 + p'.2) • E = _ + _
    rw [Submodule.coe_add, add_smul]; exact add_add_add_comm _ _ _ _) rfl
  map_smul' c p := Prod.ext (by
    show ((c • p.1 : Ymod r χ E) : A) + (c • p.2) • E = c • (_ + _)
    rw [Submodule.coe_smul_of_tower, smul_add, smul_assoc]) rfl

def FirstSummandSubmodule (O : Type*) [CommRing O] [Algebra O A] (e₁ : A) : Submodule O A :=
  LinearMap.range (LinearMap.mulLeft O e₁)

end Lattices

def FirstSummandRepresentation : Prop :=
  ∀ (O A T' G : Type*) [CommRing O] [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (e₁ : A) (ε : G →* Oˣ),
    ∃ ρ₁ : Representation O G (FirstSummandSubmodule O e₁), ∀ g b, ((ρ₁ g b : FirstSummandSubmodule O e₁) : A) =
      ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹))

end Formalism.RepresentationBoundsCohomology.BR
