module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic

@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def ratG {X : Type} [Group X] (Γ K : Subgroup X) : Subgroup K := (Γ ⊓ K).subgroupOf K

def LCSC (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  LocallyCompactSpace G ∧ SecondCountableTopology G ∧ T2Space G ∧ IsTopologicalGroup G

def DiscC {X : Type} [Group X] [TopologicalSpace X] (Γ K : Subgroup X) : Prop :=
  Countable (ratG Γ K) ∧ DiscreteTopology (ratG Γ K)

def Semi {X : Type} [Group X] [TopologicalSpace X] (K N H : Subgroup X) : Prop :=
  (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) ∧
    ∃ e : (N × H) ≃ₜ K, ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X)

def ConjInv {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X] (N H : Subgroup X) : Prop :=
  ∀ μN : Measure N, μN.IsHaarMeasure → ∀ h ∈ H, ∀ f : X → ENNReal, Measurable f →
    ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μN = ∫⁻ n, f (n : X) ∂μN

def ProdF {X : Type} [Group X] [MeasurableSpace X] (K N H : Subgroup X)
    (μK : Measure K) (μN : Measure N) (μH : Measure H) : Prop :=
  ∀ f : X → ENNReal, Measurable f →
    ∫⁻ k, f (k : X) ∂μK = ∫⁻ m, ∫⁻ h, f ((m : X) * (h : X)) ∂μH ∂μN

def SubLCSC : Prop :=
  ∀ (X : Type) [Group X] [TopologicalSpace X] (Γ K : Subgroup X), LCSC X → IsClosed (K : Set X) →
    Countable Γ → DiscreteTopology Γ → LCSC K ∧ DiscC Γ K

def ProdHaarG : Prop :=
  ∀ (X : Type) [Group X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (K N H : Subgroup X), Semi K N H → LCSC K → LCSC N → LCSC H → ConjInv N H →
    ∀ μN : Measure N, μN.IsHaarMeasure → ∀ μH : Measure H, μH.IsHaarMeasure →
    ∃ μK : Measure K, μK.IsHaarMeasure ∧ ProdF K N H μK μN μH

def DiscHA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    Countable (HFinIn (AF F) σ J) ∧ DiscreteTopology (HFinIn (AF F) σ J)

def TensTop : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsTopologicalRing (AF F ⊗[F] E) ∧ T2Space (AF F ⊗[F] E) ∧
      LocallyCompactSpace (AF F ⊗[F] E) ∧ SecondCountableTopology (AF F ⊗[F] E)

end PI.VolSemiDirect.W
