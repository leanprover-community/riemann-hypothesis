module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
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

namespace GlobalTheory.CompanionTheory.Ar.Top

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.LowerBoundFree

def StokesAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
    [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
    (X : ComponentSetting D O Lt) (B : ℕ) : Prop :=
  ∀ a : ℝ, StokesLimit.Hyp X B a →
    ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

def RootTower.HasBaseDegreeSettingStrict {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N)
    (II : IntersectionSystem) (Ch Cu rd Lval : ℝ) (B : ℕ) (c : T.Comp) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (Ω : Type) (_ : Field Ω) (_ : Algebra ℚ Ω)
    (E : Ψ → Type) (_ : ∀ τ, AddCommGroup (E τ)) (_ : ∀ τ, Module Ω (E τ)) (D : ComponentData II Ψ K ι Ω E)
    (O Lt : Type) (_ : CommRing O) (_ : AddCommGroup Lt) (_ : Module O Lt) (X : ComponentSetting D O Lt),
    D.N = N ∧ D.j = T.j ∧ X.rd = rd ∧ X.Lval = Lval ∧
    CuspBundlePos X ∧ MUConjInvariant X ∧ HtInterior Ch X ∧ HtBoundary Ch X ∧ CuspMean Cu X ∧ 0 < degMu X.H ∧
    ArLimExists X.H X.S B ∧ StokesAt X B ∧
    T.PPc II B c (testPoly T.j) = slX X B * (((dimX Ψ N T.j : ℝ) + 1) * (T.vol c * testDeg Ψ N T.j))

end GlobalTheory.CompanionTheory.Ar.Top
