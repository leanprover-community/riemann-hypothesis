module

public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.AlgebraicWeights.IsAlgWeight
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2.NG

section lvl

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

def ParaRT (s : SplitPlace L) (r : ℕ) (h : GL (Fin n) (s.v.adicCompletion L⁺)) : Prop :=
  h ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring ∧
    ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v (h.val a b) < 1

def UniRT (s : SplitPlace L) (r : ℕ) (h : GL (Fin n) (s.v.adicCompletion L⁺)) : Prop :=
  ParaRT s r h ∧ ∀ a b : Fin n, a.val < r → b.val < r →
    (b.val < a.val → Valued.v (h.val a b) < 1) ∧ (a = b → Valued.v (h.val a b - 1) < 1)

def detDD (s : SplitPlace L) (r : ℕ) (h : GL (Fin n) (s.v.adicCompletion L⁺)) : s.v.adicCompletion L⁺ :=
  (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => h.val a.1 b.1).det

def supDiag (s : SplitPlace L) (r : ℕ) (h : GL (Fin n) (s.v.adicCompletion L⁺)) : s.v.adicCompletion L⁺ :=
  ∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then h.val a b else 0

def IsProdLevel (J : Subgroup (GAf L n)) : Prop :=
  ∀ κ ∈ J, ∀ v, ∃ κ' ∈ J, TrivOutside (L := L) {v} κ' ∧
    (κ'.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (κ.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v)

structure LevelPara (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s : SplitPlace L) (r : ℕ)
    (ξ : (s.v.adicCompletion L⁺)ˣ →* ℂˣ) : Prop where
  mem : ∀ κ, TrivOutside (L := L) {s.v} κ → (κ ∈ J ↔ ParaRT s r (s.loc n κ))
  chr : ∀ κ (h : κ ∈ J), TrivOutside (L := L) {s.v} κ → ∀ u : (s.v.adicCompletion L⁺)ˣ,
    (u : s.v.adicCompletion L⁺) = detDD s r (s.loc n κ) → χ ⟨κ, h⟩ = ξ u

structure LevelUni (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s : SplitPlace L) (r : ℕ)
    (ψ₀ : AddChar (s.v.adicCompletion L⁺) ℂ) (ξ : (s.v.adicCompletion L⁺)ˣ →* ℂˣ) : Prop where
  mem : ∀ κ, TrivOutside (L := L) {s.v} κ → (κ ∈ J ↔ UniRT s r (s.loc n κ))
  chr : ∀ κ (h : κ ∈ J), TrivOutside (L := L) {s.v} κ → ∀ u : (s.v.adicCompletion L⁺)ˣ,
    (u : s.v.adicCompletion L⁺) = detDD s r (s.loc n κ) →
    ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) = ψ₀ (supDiag s r (s.loc n κ)) * ξ u

def IsCompAt (χ : Host.HChar L) (s : SplitPlace L) (ξ : (s.v.adicCompletion L⁺)ˣ →* ℂˣ) : Prop :=
  (∃ N : ℕ, ∀ u : (s.v.adicCompletion L⁺)ˣ,
    Valued.v ((u : s.v.adicCompletion L⁺) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) ∧
  ∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion L⁺) k) = χ.locK s.w k

def IsPsi0 (s : SplitPlace L) (ψ₀ : AddChar (s.v.adicCompletion L⁺) ℂ) : Prop :=
  (∀ x, Valued.v x < 1 → ψ₀ x = 1) ∧ ∃ x, Valued.v x ≤ 1 ∧ ψ₀ x ≠ 1

end lvl


open Formalism.BasicNotions in
def paramV (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ) : Multiset ℂ :=
  (Finset.univ.val.map fun i : Fin (R.k - 1) => ((h.v i : ℚ) : ℂ) - sh) +
  (Finset.univ.val.map fun i : Fin R.m => -((h.b i : ℚ) : ℂ) - sh) +
  ((Multiset.range R.t).map fun c : ℕ => -((h.e j : ℚ) : ℂ) - sh + ((R.t : ℂ) - 1 - 2 * c) / 2)

end Formalism.L2.NG
