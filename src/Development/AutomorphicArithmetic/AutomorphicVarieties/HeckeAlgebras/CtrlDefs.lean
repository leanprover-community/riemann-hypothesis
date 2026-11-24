module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open IsLocalRing Matrix

namespace UpperTheory.V.Hi

def mIm (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (k : ℕ) : Submodule O Ω :=
  Submodule.map (Algebra.linearMap O Ω) (maximalIdeal O ^ k)

theorem mem_mIm {O Ω : Type} [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] {k : ℕ} {w : Ω} :
    w ∈ mIm O Ω k ↔ ∃ x ∈ maximalIdeal O ^ k, algebraMap O Ω x = w := Iff.rfl

namespace Frame

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {Ω : Type} [Field Ω]
  {O : Type} [CommRing O] [IsLocalRing O] [Algebra O Ω] (m : ℕ) (W : WtRep X.I O Ω)

def unt : Module.End Ω (Fin m → X.Fn Ω (W.d + 1)) where
  toFun F i g := ((W.ξ g.2)⁻¹).val *ᵥ F i g
  map_add' F F' := by ext i g k; simp only [Pi.add_apply, mulVec_add]
  map_smul' c F := by ext i g k; simp only [Pi.smul_apply, mulVec_smul, RingHom.id_apply]

theorem unt_apply (F : Fin m → X.Fn Ω (W.d + 1)) (i : Fin m) (g : Ga × Gp) :
    X.unt m W F i g = ((W.ξ g.2)⁻¹).val *ᵥ F i g := rfl

theorem ctrl_apply (F : Fin m → X.Fn Ω (W.d + 1)) (g : Ga × Gp) (i : Fin m) :
    X.ctrl m W F g i = X.unt m W F i g 0 := rfl

def Lat (Λ : Submodule O Ω) : Submodule O (Fin m → X.Fn Ω (W.d + 1)) where
  carrier := {F | ∀ i g k, X.unt m W F i g k ∈ Λ}
  add_mem' h h' i g k := by
    simpa only [map_add, Pi.add_apply] using Λ.add_mem (h i g k) (h' i g k)
  zero_mem' i g k := by rw [map_zero]; exact zero_mem _
  smul_mem' c F h i g k := by
    rw [LinearMap.map_smul_of_tower]; exact Λ.smul_mem c (h i g k)

theorem mem_lat (Λ : Submodule O Ω) (F : Fin m → X.Fn Ω (W.d + 1)) :
    F ∈ X.Lat m W Λ ↔ ∀ i g k, X.unt m W F i g k ∈ Λ := Iff.rfl


variable {m} in
abbrev ClO (τ : X.Ub →* GL (Fin m) O) (U : Subgroup X.Ub) (c : ℕ) (φ : X.I.T →* Oˣ) :
    Submodule Ω (Fin m → X.Fn Ω (W.d + 1)) :=
  X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) W.ξ U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)

end Frame

end UpperTheory.V.Hi
