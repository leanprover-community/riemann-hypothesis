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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField


variable {M : Type*} [Field M] [NumberField M]


def conjOf {D : D7} {M : IntermediateField ℚ ℂ} (e : D.what₂.LL ≃+* M) (s : D.what₂.LL →+* ℂ) : M →ₐ[ℚ] ℂ :=
  (s.comp (e.symm : M →+* D.what₂.LL)).toRatAlgHom

def OmegaCompatible (D : D7) (δ : ℂ) : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (e : D.what₂.LL ≃+* M),
    (∀ y, ((e y : M) : ℂ) = D.what₂.embLL y) ∧
    TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK δ) M ∧
    ∀ τ, ∃ d : M, TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {d} ∧
      ∀ s : D.what₂.LL →+* ℂ, D.gx.Om τ s =
        (Real.pi * ‖conjOf e s d‖ ^ 2 / TaylorLogMetric.area (TaylorLogMetric.lamConj M (conjOf e s) (TaylorLogMetric.lamOf D D.host.ccK δ)))⁻¹

end Formalism.L2.GlobalTheoryTheory

end
