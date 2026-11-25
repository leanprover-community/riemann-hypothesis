module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Mathlib.RingTheory.WittVector.Isocrystal
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

@[expose] public section

noncomputable section

open MvPowerSeries GlobalTheory.Katz

namespace GlobalTheory.KatzF

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ} {σ : Type}


variable (k) in
def sig : Fr p k →+* Fr p k := (WittVector.FractionRing.frobenius p k : Fr p k →+* Fr p k)

def powX (R : Type) [CommRing R] (σ : Type) (n : ℕ) : σ → MvPowerSeries σ R := fun i => X i ^ n

def frobS (f : MvPowerSeries (Fin d) (Fr p k)) : MvPowerSeries (Fin d) (Fr p k) :=
  subst (powX (Fr p k) (Fin d) p) (MvPowerSeries.map (sig p k) f)

def IsF {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (F : Mod p h → Mod p h) : Prop :=
  ∀ f : quasiLog p h, ∃ g : quasiLog p h, g.1 = frobS p f.1 ∧
    F (Submodule.Quotient.mk f) = Submodule.Quotient.mk g

def IsPull {e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k}
    (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k) (m : Mod p hν → Mod p hμ) : Prop :=
  ∀ f : quasiLog p hν, ∃ g : quasiLog p hμ, g.1 = subst (fun j => Katz.lift p (φ j)) f.1 ∧
    m (Submodule.Quotient.mk f) = Submodule.Quotient.mk g

end GlobalTheory.KatzF
