module

public import Formalism.PeriodIntegrals.LocHerm
public import Formalism.PeriodIntegrals.AlgebraMapMemO
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
import Mathlib.Tactic.Linter.HaveILetI
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

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.OProj

def Concl {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module E W] (P : Submodule M.L.O W), P.FG →
    Module.Projective M.L.O P

def SqCase : Prop :=
  AllLoc fun {F} _ _ _ {E} _ _ _ _ M =>
  ∀ θ ∈ M.L.O, M.L.cj θ = -θ → ∀ D : 𝒪[F], (D : F) ≠ 0 → θ * θ = algebraMap F E D →
    (∃ s : F, s * s = D) → Concl M

def NonSqCase : Prop :=
  AllLoc fun {F} _ _ _ {E} _ _ _ _ M =>
  ∀ θ ∈ M.L.O, M.L.cj θ = -θ → ∀ D : 𝒪[F], (D : F) ≠ 0 → θ * θ = algebraMap F E D →
    (¬ ∃ s : F, s * s = D) → Concl M

theorem locOProj_of (hS : SqCase) (hN : NonSqCase) : PI.LocHerm.LocOProj := by
  intro F _ _ _ E _ _ _ _ M hM
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨θ, hθ, hc, D, hD0, hD⟩ := PI.LocHerm.SlopeTestRemainingChoices.exists_theta (L := M.L)
  by_cases hs : ∃ s : F, s * s = D
  · exact hS F E M hM θ hθ hc D hD0 hD hs
  · exact hN F E M hM θ hθ hc D hD0 hD hs

end PI.LocHerm.OProj
