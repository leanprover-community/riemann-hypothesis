module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.IntDown
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

namespace UpperTheory.V.Z.Sym.Loc.PK

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}


variable (O τ) in
def Gu : Subgroup (Etau K τ)ˣ where
  carrier := {u | IsIntegral O (u : Etau K τ) ∧ IsIntegral O ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)}
  one_mem' := by simp [isIntegral_one]
  mul_mem' {a b} ha hb := ⟨by simpa using ha.1.mul hb.1, by
    rw [_root_.mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  inv_mem' {a} ha := ⟨ha.2, by simpa using ha.1⟩


variable (O) in
def Ord (y : Etau K τ) : Set (Etau K τ) := (Submodule.span O {1, y} : Submodule O (Etau K τ))


variable (O) in
def Hu (y : Etau K τ) : Subgroup (Etau K τ)ˣ where
  carrier := {u | PS.ml u (Ord O y) = Ord O y}
  one_mem' := PS.ml_one _
  mul_mem' {a b} ha hb := by
    change PS.ml (a * b) _ = _
    rw [PS.ml_mul, show PS.ml b (Ord O y) = Ord O y from hb, show PS.ml a (Ord O y) = Ord O y from ha]
  inv_mem' {a} ha := by
    change PS.ml a⁻¹ _ = _
    conv_lhs => rw [← show PS.ml a (Ord O y) = Ord O y from ha]
    rw [← PS.ml_mul, inv_mul_cancel, PS.ml_one]

def yy (π : O) (m : ℕ) (x : Etau K τ) : Etau K τ := algebraMap O K (π ^ m) • x

structure Cond (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ) : Prop where
  irr : Irreducible π
  gen : Gen1 (O := O) x
  tr : QuadraticAlgebra.trace x = 0
  sq : x * x = algebraMap O (Etau K τ) (e : O)
  om : (ω : Etau K τ) = algebraMap O (Etau K τ) h + yy π n x

end UpperTheory.V.Z.Sym.Loc.PK
