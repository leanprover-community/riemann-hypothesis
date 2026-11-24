module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign
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

open Matrix Finset

namespace GlobalTheory.CompanionTheory.RealCount.Tope

variable {n : ℕ}

abbrev LP (n : ℕ) := AddMonoidAlgebra ℂ (Fin n → ℤ)

def chr (z : Fin n → ℂˣ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun μ := ∏ a, ((z a ^ (Multiplicative.toAdd μ a) : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' μ ν := by
    simp only [toAdd_mul, Pi.add_apply, _root_.zpow_add, Units.val_mul, Finset.prod_mul_distrib]

def evL (z : Fin n → ℂˣ) : LP n →ₐ[ℂ] ℂ := AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (chr z)

def altL (m : Fin n → ℤ) : LP n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • AddMonoidAlgebra.single (fun i => m (σ i)) (1 : ℂ)

def delZ (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def pPL (n : ℕ) : LP n :=
  ∏ a : Fin n, ∏ b : Fin n, (1 + AddMonoidAlgebra.single (Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) (1 : ℂ))

def frL (n : ℕ) : LP n →ₐ[ℂ] LP n :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (2 • AddMonoidHom.id (Fin n → ℤ))

def cPoly (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) : LP n :=
  ∑ μ ∈ s, AddMonoidAlgebra.single μ (c μ)

end GlobalTheory.CompanionTheory.RealCount.Tope
