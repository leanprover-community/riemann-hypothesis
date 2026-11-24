module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

@[expose] public section

noncomputable section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

def DD.map {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (g : ℕ) (f : X →ₐ[A] X') :
    DD X g →ₐ[A] DD X' g where
  toFun x := ⟨f x.a, fun j => f (x.ep j), fun j => f (x.ep' j), f x.eta⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  commutes' a := by
    show _ = DD.C (algebraMap A X' a)
    have : algebraMap A (DD X g) a = DD.C (algebraMap A X a) := rfl
    rw [this]
    ext <;> simp

section

variable {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (g : ℕ) (f : X →ₐ[A] X')
  (x : DD X g)

@[simp] theorem DD.map_a : (DD.map g f x).a = f x.a := rfl
@[simp] theorem DD.map_ep (j) : (DD.map g f x).ep j = f (x.ep j) := rfl
@[simp] theorem DD.map_ep' (j) : (DD.map g f x).ep' j = f (x.ep' j) := rfl
@[simp] theorem DD.map_eta : (DD.map g f x).eta = f x.eta := rfl

instance [Finite X] : Finite (DD X g) := Finite.of_equiv _ (DD.equiv (X := X) (g := g)).symm

end

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n)

abbrev NP.redD (g m : ℕ) : DD x.A g →ₐ[x.A] DD (x.Am m) g := DD.map g (Ideal.Quotient.mkₐ x.A _)

def NP.UnipOn (H : Subgroup F.Γ) : Prop :=
  ∀ (m : ℕ) (h : F.G₀), (h : F.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (mat x.ρ (h ^ l ^ e) - 1) i j ∈ Ideal.span {x.t ^ m}

end UpperTheory.V.Pa
