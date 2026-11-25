module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
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

namespace GlobalTheory.HTW

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

def TateDualRule {G : Type}
    [Group G]
    [TopologicalSpace G]
    {Qp K₀ K : Type}
    [Field Qp]
    [Field K₀]
    [Field K]
    [Algebra Qp K₀]
    [Algebra Qp K]
    [Algebra K₀ K]
    [IsScalarTower Qp K₀ K]
    {B BdR : Type}
    [CommRing B]
    [CommRing BdR]
    [Algebra Qp B]
    [Algebra K₀ B]
    [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR]
    [Algebra K₀ BdR]
    [Algebra K BdR]
    [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR]
    [IsScalarTower Qp K₀ BdR]
    [TopologicalSpace Qp] (PD : PeriodData G Qp K₀ K B BdR) : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsCrys PD A.ρ → IsDual1 PD A.ρ A'.ρ P →
    IsCrys PD A'.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), multV PD A'.ρ τ (-a - 1) = multV PD A.ρ τ a

end GlobalTheory.HTW

namespace GlobalTheory.Published

open Formalism.BasicNotions Formalism.BasicNotions.Loc

end GlobalTheory.Published
