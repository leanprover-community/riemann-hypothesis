module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
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

namespace Formalism.L2.GlobalTheoryTheory.Jets

open NumberField Formalism.BasicNotions Formalism.MainNotions Classical

section Pieces

variable {R : Ranks} (host : Host R) {LL : Type} [Field LL] [NumberField LL] (embLL : LL →+* ℂ)
  {Tau : Type} [Fintype Tau] (eTau : Tau ≃ R.Psi)

def lamOfH (cc : Ideal (𝓞 host.K)) (δ : ℂ) : AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * host.φ₀ (((c : host.K) : host.E))}

def embTH (τ : Tau) : host.E →+* ℂ := host.emb (eTau τ : R.GG)

def mmMH (M : IntermediateField ℚ ℂ) [NumberField M] : Submodule (𝓞 M) (Tau → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (host.AA0 : Submodule (𝓞 host.E) host.E),
    v = fun τ => TaylorLogMetric.liftM M (embTH host eTau τ a)}

def ellTH (M : IntermediateField ℚ ℂ) [NumberField M] (τ : Tau) : Submodule (𝓞 M) M :=
  (mmMH host eTau M).comap (LinearMap.single (𝓞 M) (fun _ : Tau => (M : Type)) τ)

structure CurveDat where
  δ : ℂ
  delta_pow_twelve_eq_discr : δ ^ 12 = TaylorLogMetric.discr (lamOfH host host.ccK 1)
  M : IntermediateField ℚ ℂ
  [nf : NumberField M]
  eL : LL ≃+* M
  emb : ∀ y, ((eL y : M) : ℂ) = embLL y
  fr : Tau → M
  fr_ne : ∀ τ, fr τ ≠ 0
  gen : ∀ τ, ellTH host eTau M τ = Submodule.span (𝓞 M) {fr τ}

attribute [instance] CurveDat.nf

variable {host embLL eTau}

end Pieces

end Formalism.L2.GlobalTheoryTheory.Jets
