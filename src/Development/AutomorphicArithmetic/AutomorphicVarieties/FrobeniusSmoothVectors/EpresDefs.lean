module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Mathlib.RingTheory.MvPowerSeries.Inverse
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def sg (K : Type) [CommRing K] (j : ZMod 2) : K := (-1) ^ j.val

def pw (a b : Fin 3) : ZMod 2 := ((w 3 a - w 3 b : ℤ) : ZMod 2)

def adp (K : Type) [CommRing K] (j : ZMod 2) : Submodule K (Matrix (Fin 3) (Fin 3) K) where
  carrier := {X | ∀ a b, pw a b ≠ j → X a b = 0}
  add_mem' h h' a b e := by simp [h a b e, h' a b e]
  zero_mem' _ _ _ := rfl
  smul_mem' c X h a b e := by simp [h a b e]

def prp (K : Type) [CommRing K] (j : ZMod 2) : Matrix (Fin 3) (Fin 3) K →ₗ[K] adp K j where
  toFun X := ⟨Matrix.of fun a b => if pw a b = j then X a b else 0, fun a b e => by simp [e]⟩
  map_add' X Y := Subtype.ext (by ext a b; by_cases e : pw a b = j <;> simp [e])
  map_smul' c X := Subtype.ext (by ext a b; by_cases e : pw a b = j <;> simp [e])

def evp {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (j : ZMod 2) : Submodule O R where
  carrier := {x | σ x = sg R j * x}
  add_mem' {x y} (h : _ = _) (h' : _ = _) := show _ = _ by rw [map_add (f := _), h, h', mul_add]
  zero_mem' := show _ = _ by simp
  smul_mem' c x (h : _ = _) := show _ = _ by rw [map_smul, h, mul_smul_comm]

section Pres

variable (O : Type) [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R)

def derp (j : ZMod 2) : Submodule (ResidueField O) (R →ₗ[O] ResidueField O) :=
  PtDer (res O R) (ResidueField O) ⊓
    { carrier := {D | ∀ x, D (σ x) = sg (ResidueField O) j * D x}
      add_mem' := fun h h' x => by simp only [LinearMap.add_apply, h x, h' x, mul_add]
      zero_mem' := fun x => by simp
      smul_mem' := fun c D h x => by simp only [LinearMap.smul_apply, h x, smul_eq_mul, mul_left_comm] }

structure GPres where
  a : ℕ
  g : ℕ
  p : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R
  κ : Type
  [fin : Fintype κ]
  f : κ → MvPowerSeries (Fin a ⊕ Fin g) O
  wf : κ → ZMod 2
  surj : Function.Surjective p
  var : ∀ s, p (MvPowerSeries.X s) ∈ maximalIdeal R
  part : ∀ j, (wtPart O (Space.Loc.par a g) j).map p.toLinearMap = evp σ j
  homog : IsHomog O (Space.Loc.par a g) (RingHom.ker p)
  min : ∀ h ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) h ∈ maximalIdeal O
  hf : ∀ u, f u ∈ wtPart O (Space.Loc.par a g) (wf u)
  ker : RingHom.ker p = Ideal.span (Set.range f)
  indep : ∀ c : κ → O, ∑ u, c u • f u ∈ maximalIdeal (MvPowerSeries (Fin a ⊕ Fin g) O) * RingHom.ker p →
    ∀ u, c u ∈ maximalIdeal O

attribute [instance] GPres.fin

end Pres

structure Space.Loc.IsInv {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {F : Frame l (ResidueField O)} {S : Space O F 3} {x : Ideal S.A} (L : S.Loc x) (σ : L.R →ₐ[L.O'] L.R) : Prop where
  sq : ∀ y, σ (σ y) = y
  ent : ∀ g a b, L.ρ.r g a b ∈ evp σ (pw a b)
  base : ∀ y : S.B, L.b y ∈ evp σ 0

end UpperTheory.V.Fr
