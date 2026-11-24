module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Formalism.LocalToGlobal.LatticeGeometry.CompNe
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

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.WeightedDeltaMeans.LowerBoundLinearPower, Formalism.LocalToGlobal.LatticeGeometry.PluckerHadamard.FlagIntegralKillsPowerSums

-- ===== clump member: Formalism.WeightedDeltaMeans.LowerBoundLinearPower =====
-- clump-header: {"m": "Formalism.WeightedDeltaMeans.LowerBoundLinearPower", "h": "module\n\npublic import Mathlib.Algebra.MvPolynomial.PDeriv\npublic import Mathlib.Basic.Real.Basic\npublic import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Finset MvPolynomial Filter Topology

noncomputable section

namespace Formalism.ShimuraLimitIdentity

abbrev Pol (Ψ : Type) (N : ℕ) := MvPolynomial (Ψ × Fin N) ℝ

def top (N j : ℕ) : Finset (Fin N) := univ.filter (fun i : Fin N => i.val < j)

def psumAt {Ψ : Type} {N : ℕ} (τ : Ψ) (k : ℕ) : Pol Ψ N := ∑ i : Fin N, X (τ, i) ^ k

def Sh {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) (j : ℕ) (τ : Ψ) (F : Pol Ψ N) : ℝ :=
  I (∑ i ∈ top N j, pderiv (τ, i) F)

def Tot {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) (τ : Ψ) (F : Pol Ψ N) : ℝ :=
  I (∑ i : Fin N, pderiv (τ, i) F)

def Kills {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) : Prop :=
  ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → ∀ G : Pol Ψ N, I (psumAt τ k * G) = 0

end Formalism.ShimuraLimitIdentity
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.WeightedDeltaMeans.LowerBoundLinearPower =====

-- ===== clump member: Formalism.LocalToGlobal.LatticeGeometry.PluckerHadamard.FlagIntegralKillsPowerSums =====
-- clump-header: {"m": "Formalism.LocalToGlobal.LatticeGeometry.PluckerHadamard.FlagIntegralKillsPowerSums", "h": "module\n\npublic import Formalism.WeightedDeltaMeans.LowerBoundLinearPower\npublic import Formalism.LocalToGlobal.LatticeGeometry.CompNe\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions MvPolynomial Filter Topology Finset

namespace Formalism.L2.Geo

section Alg

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

def smallBlock (N j : ℕ) : Finset (Fin N) := univ.filter (fun i : Fin N => j ≤ i.val)

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def a0Mu (j : ℕ) : Pol Ψ N := ∑ τ : Ψ, ∑ i ∈ smallBlock N j, X (τ, i)

def blockVandermondePolynomial (τ : Ψ) (S : Finset (Fin N)) : Pol Ψ N :=
  ∏ a ∈ S, ∏ b ∈ S.filter (fun b => a < b), (X (τ, a) - X (τ, b))

def fibreVandermondeProduct (j : ℕ) (cf : ℝ) : Pol Ψ N :=
  C cf * ∏ τ : Ψ, (blockVandermondePolynomial τ (Formalism.ShimuraLimitIdentity.top N j) * blockVandermondePolynomial τ (smallBlock N j))

def a0n (Ψ : Type) [Fintype Ψ] (N j : ℕ) : ℕ := Fintype.card Ψ * (j * (N - j))

end Alg

section AlgStmt

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

def FlagIntegralAnnihilatesPowerSums : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), Kills (degFlL Ψ N)

end AlgStmt

section Geo

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} {w : Dat D Lev}

structure ExtensionData (U : ShimU D G jC ng w) where

  Xb : U.Comp → G.Var

  PtX : U.Comp → Type

  bdX : ∀ c, PtX c → Prop

  htX : ∀ c, G.Adl (Xb c) → PtX c → ℝ

  degX : ∀ c, G.Adl (Xb c) → ℝ

  semiposX : ∀ c, G.Adl (Xb c) → Prop
  nefFibX : ∀ c, G.Adl (Xb c) → Prop
  ampleX : ∀ c, G.Adl (Xb c) → Prop

  muC : ℝ → ℝ → ℝ → ∀ c, G.Adl (Xb c)

  arLim : ℝ → U.Comp → ℝ

  degMu : U.Comp → ℝ

  meanU : U.Comp → ℝ

  fdeg : ℝ

section Props

variable (U : ShimU D G jC ng w) (X : ExtensionData U)

end Props

section Assembly

variable (U : ShimU D G jC ng w)


end Assembly

end Geo

end Formalism.L2.Geo
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.LatticeGeometry.PluckerHadamard.FlagIntegralKillsPowerSums =====
