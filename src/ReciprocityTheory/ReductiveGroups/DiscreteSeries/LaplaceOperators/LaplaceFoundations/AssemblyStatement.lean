module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

def PsiForStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ),
    S7.IsHCParam lam → S7.IsMu lam μ → GapAtLeast ε lam h → 1 ≤ S7.q0 ε → 8 * (n : ℝ) * S7.q0 ε < h →
    IsPsiFor ε lam T (S7.PsiM T μ) ∧ ContinuousOn (S7.PsiM T μ) (UJset ε)

def LinkStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), StdGap ε lam → IsPsiFor ε lam T Ψ →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
      IsHWSmooth ε σ lam w ∧ ∀ g ∈ UJset ε, ⟪w, σ g w⟫_ℂ = ⟪T.w, Ψ g T.w⟫_ℂ

def AssemblyStatement : Prop :=
  PairingPropertiesStatement → TangentPairingStatement → NsetExpInjectiveSurjective → CayleyMajorantBound → GaussianLimitHaar → ExistsUnitaryHaarProbability →
    WhittakerSchurOrthogonality → LamTStatement → PsiForStatement → LinkStatement → StepIBaseStatement

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
