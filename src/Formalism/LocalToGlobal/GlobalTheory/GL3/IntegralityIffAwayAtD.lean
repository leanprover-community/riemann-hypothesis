module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

def OneAt (D : D7) (p : ℕ) (𝔞 : IdE D) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ 𝔞, (s : D.host.E) * x ∈ (1 : IdE D)) ∧ (s : D.host.E) ∈ 𝔞

def LemmaU (D : D7) : Prop :=
  ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (𝔞 : IdE D),
    N1 D 𝔞 → OneAt D p 𝔞 → χ 𝔞 ∈ Qbar ∧ ‖lamC lam (χ 𝔞)‖ = 1

def DetOneAt (D : D7) : Prop :=
  ∀ (p N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L → OneAt D p (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L)

def ChiFacUnit (D : D7) : Prop :=
  ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N') L' →
      Base.chiFac χ N N' L L' ∈ Qbar ∧ ‖lamC lam (Base.chiFac χ N N' L L')‖ = 1

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
