module

public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteEpsilonOperator
public import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.GlobalTheory.DivPassage
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

section Bridge

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {U : Type} [AddCommGroup U] [Module K U]

theorem epOp_eq_epP (σ : Representation K G U) (P : Subgroup G) (ψ : P →* Kˣ) (χ : P →* (𝓞 K)ˣ)
    (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    Formalism.IndefR.IndefiniteEpsilonOperator.epOp σ ⟨P, ψ⟩ = Formalism.IndefR.TransferLatticeStatement.epP P χ σ := by
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.epOp Formalism.IndefR.TransferLatticeStatement.epP
  simp only [hχ]
  congr
  exact Subsingleton.elim _ _

theorem nOf_eq_nS {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W) (P : Subgroup G) (ψ : P →* Kˣ)
    (χ : P →* (𝓞 K)ˣ) (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨P, ψ⟩ = Formalism.IndefR.TransferLatticeStatement.nS τ P χ := by
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.TransferLatticeStatement.nS
  first
  | (unfold Formalism.IndefR.IndefiniteEpsilonOperator.epSp; rw [epOp_eq_epP τ P ψ χ hχ])
  | (simp only [Formalism.IndefR.IndefiniteEpsilonOperator.epSp, epOp_eq_epP τ P ψ χ hχ])
  | (rw [← epOp_eq_epP τ P ψ χ hχ]; rfl)

end Bridge

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

end In

end Formalism.IndefR.CxPass
