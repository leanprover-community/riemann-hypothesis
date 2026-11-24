module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal
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

open NumberField IsDedekindDomain

namespace UpperTheory.V.ZK.Ct

structure Dat (Y I : Type) [AddCommGroup Y] [AddCommGroup I] where

  g : Module.End ℤ Y

  gI : Module.End ℤ I

  d : Y →ₗ[ℤ] I

  n : ℕ

  a : ℕ
  comm : ∀ y, d (g y) = gI (d y)
  g_pow : g ^ n = 1
  gI_pow : gI ^ n = 1
  n_pos : 0 < n
  two_le : 2 ≤ a
  tf : ∀ (m : ℤ) (x : I), m ≠ 0 → m • x = 0 → x = 0

def mt (Y : Type) [AddCommGroup Y] (m : ℕ) : Submodule ℤ Y :=
  LinearMap.range ((m : ℤ) • (LinearMap.id : Y →ₗ[ℤ] Y)) ⊔ Submodule.torsion ℤ Y

namespace Dat

variable {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I)

def del : Module.End ℤ Y := D.g - (D.a : ℤ) • 1

def delI : Module.End ℤ I := D.gI - (D.a : ℤ) • 1

def nm : Module.End ℤ Y := ∑ j ∈ Finset.range D.n, ((D.a : ℤ) ^ j) • D.g ^ (D.n - j)

def U : Submodule ℤ Y := (LinearMap.range D.delI).comap D.d

abbrev W : Type := D.U ⧸ (LinearMap.range D.del ⊔ Submodule.torsion ℤ Y).submoduleOf D.U

abbrev EQ : Type :=
  LinearMap.ker D.d ⧸ ((LinearMap.ker D.d).map D.del ⊔ Submodule.torsion ℤ Y).submoduleOf (LinearMap.ker D.d)

abbrev ClQ : Type := I ⧸ (LinearMap.range D.d ⊔ LinearMap.range D.delI)

def SelInv (l : ℕ) : Set (Y ⧸ mt Y l) :=
  {x | ∃ y : Y, Submodule.Quotient.mk y = x ∧ D.g y - y ∈ mt Y l ∧ ∃ i : I, D.d y = (l : ℤ) • i}

end Dat

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]

structure IsDat (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)) : Prop where
  n_eq : D.n = orderOf γ
  a_eq : D.a = a
  g_eq : ∀ α : Fˣ, D.g (Additive.ofMul α) = Additive.ofMul (actU γ⁻¹ α)
  gI_eq : ∀ 𝔡 P, D.gI 𝔡 P = 𝔡 (actP γ P)
  d_eq : ∀ (α : Fˣ) P, D.d (Additive.ofMul α) P = ordP P α

def SelL (l : ℕ) (L : Type) [Field L] [NumberField L] : Set (Lˣ ⧸ (powMonoidHom l : Lˣ →* Lˣ).range) :=
  {x | ∃ y : Lˣ, QuotientGroup.mk y = x ∧
    ∀ p : HeightOneSpectrum (𝓞 L), (l : 𝓞 L) ∉ p.asIdeal → (l : ℤ) ∣ ordP p y}

end UpperTheory.V.ZK.Ct

end
