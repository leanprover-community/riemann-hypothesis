module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries

def JetsIntegral {σ : Type} {l : ℕ} [Fact l.Prime] (F : MvPowerSeries σ ℂ_[l]) : Prop :=
  ∀ a : σ →₀ ℕ, ‖(a.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff a F‖ ≤ 1

def IsRBasis (D : D7) {l : ℕ} [Fact l.Prime] (ρ : D.host.E → ℂ_[l]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (g : Matrix (Fin N) (Fin N) ℂ_[l]) : Prop :=
  g.det ≠ 0 ∧
    Submodule.span 𝓞_ℂ_[l] (Set.range fun a : Fin N => fun k => g k a) =
      Submodule.span 𝓞_ℂ_[l] ((fun (x : Fin N → D.host.E) k => ρ (x k)) '' (L : Set (Fin N → D.host.E)))


end GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries
