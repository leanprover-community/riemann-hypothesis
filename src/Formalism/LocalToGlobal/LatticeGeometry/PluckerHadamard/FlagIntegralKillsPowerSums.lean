module

public import Formalism.WeightedDeltaMeans.LowerBoundLinearPower
public import Formalism.LocalToGlobal.LatticeGeometry.CompNe
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

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


variable (U : ShimU D G jC ng w) (X : ExtensionData U)



variable (U : ShimU D G jC ng w)



end Geo

end Formalism.L2.Geo
