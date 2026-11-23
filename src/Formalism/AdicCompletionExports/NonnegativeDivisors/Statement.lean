module

public import Formalism.LocalToGlobal.Divisibility.LiftLat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

namespace Formalism.AdicCompletionExports.NonnegativeDivisors

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

structure NRec where

  Pl : Type

  supp : Finset Pl

  tw : Pl → Prop

  lwP : Pl → ℝ

  logWeight_nonneg : ∀ w, 0 ≤ lwP w

  ramIdx : Pl → ℕ

  etaJ : ℕ → Pl → ℚ

  etaJ_nonneg : ∀ j w, 0 ≤ etaJ j w

  dZ0 : ℕ → ℕ

  m : ℕ

  f : ℕ

  b : ℝ

  L : ℝ

  x : ℝ

  Nc : ℝ

  vvTerm : ℕ → ℝ

namespace NRec

variable (R : NRec)

def lifts : Finset ℕ := Finset.Icc 1 R.m


end NRec

section Ties

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)
  (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K))) (R : NRec)
  (ι : HeightOneSpectrum (𝓞 K) → R.Pl) (lift : J → ℕ)

def TieInj : Prop := Set.InjOn ι Tw

def TieLw : Prop := ∀ y ∈ Tw, Formalism.DivisionValues.lw y = R.lwP (ι y)

def TieRam : Prop := ∀ y ∈ Tw, (Formalism.EigenvalueLevelCeiling.ramw y : ℝ) = (R.ramIdx (ι y) : ℝ)

def TieTw : Prop := ∀ y ∈ Tw, ι y ∈ R.supp ∧ R.tw (ι y)

def TieLift : Prop := ∀ j, lift j ∈ R.lifts

def TieEta : Prop := ∀ y ∈ Tw, ∀ j, ((F.etaJ P ψ Zs j (μ y) y : ℚ) : ℝ) = (R.etaJ (lift j) (ι y) : ℝ)

def TieRank : Prop :=
  ∀ j, (R.dZ0 (lift j) : ℝ) = ((F.R F.μ0).dZ (F.lvl P ψ) (Zs.Z F.μ0) : ℝ)

structure Ties : Prop where
  inj : TieInj Tw R ι
  lw : TieLw Tw R ι
  ram : TieRam Tw R ι
  tw : TieTw Tw R ι
  lifts : TieLift R lift
  eta : TieEta F P ψ Zs μ Tw R ι lift
  rank : TieRank F P ψ Zs R lift

end Ties

end Formalism.AdicCompletionExports.NonnegativeDivisors
