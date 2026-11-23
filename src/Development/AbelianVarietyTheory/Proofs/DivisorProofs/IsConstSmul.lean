module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotTransfer

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem ker_smul (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T) (κ : ℂ)
    (P : PolF D WW.rank A.rank) (h : GA D WW) (g : GA D A) :
    X.ker ψ θ t (κ • P) h g = κ * X.ker ψ θ t P h g := by
  simp only [Tri.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem isConst_smul {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {c : T → ℂ}
    (h : X.IsConst ψ θ c) {κ : ℂ} (hκ : κ ≠ 0) : X.IsConst ψ θ fun t => κ * c t := by
  obtain ⟨⟨t₁, h₁⟩, P, P', H⟩ := h
  refine ⟨⟨t₁, mul_ne_zero hκ h₁⟩, κ • P, P', fun t => ⟨fun g => ⟨?_, ((H t).1 g).2⟩, (H t).2.1, fun g => ?_⟩⟩
  · have := ((H t).1 g).1.const_mul κ
    have e : X.ker ψ θ t (κ • P) g = fun x => κ * X.ker ψ θ t P g x := funext fun x => ker_smul X ψ θ t κ P g x
    rw [IntegrableOn, e]
    exact this
  · have e : X.I ψ θ t (κ • P) g = κ * X.I ψ θ t P g := by
      simp only [Tri.I, ker_smul, MeasureTheory.integral_const_mul]
    rw [e, (H t).2.2 g, mul_assoc]

end GlobalTheory.BotTransfer
