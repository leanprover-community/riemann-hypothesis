module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance

open Formalism.L2.Col

section Defs

variable {E : Type} [Field E] [NumberField E]

theorem intAt_zero (P : HeightOneSpectrum (𝓞 E)) : IntAt P (0 : E) :=
  ⟨0, 1, one_notMem P, by simp⟩

theorem intAt_add {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨s' * r + s * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_mul, ← h, ← h']
  ring

theorem intAt_mul {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']
  ring

theorem intAt_neg {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h⟩ := ha
  exact ⟨-r, s, hs, by rw [map_neg, ← h]; ring⟩

theorem intAt_algebraMap (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E r) :=
  ⟨r, 1, one_notMem P, by simp⟩

def DegOneUnram (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  (qOf P).Prime ∧ ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2

def IsLatAt (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (abelian₂ : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  (∀ u : E, IntAt P u → ∀ v ∈ abelian₂, u • v ∈ abelian₂) ∧
    ∃ m : ℕ, (∀ v : Fin N → E, (∀ l, IntAt P (v l)) → ((qOf P : E) ^ m) • v ∈ abelian₂) ∧
      ∀ v ∈ abelian₂, ∀ l, IntAt P ((qOf P : E) ^ m * v l)

def depthSub (P : HeightOneSpectrum (𝓞 E)) (D : ℕ) : AddSubgroup E where
  carrier := {a | IntAt P ((qOf P : E) ^ D * a)}
  add_mem' := fun {a b} ha hb => by
    show IntAt P _
    rw [mul_add]
    exact intAt_add ha hb
  zero_mem' := by
    show IntAt P _
    rw [mul_zero]
    exact intAt_zero P
  neg_mem' := fun {a} ha => by
    show IntAt P _
    rw [mul_neg]
    exact intAt_neg ha

def unfoldAB {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (A B : ℕ) {n' c' n c : ℕ}
    (Psi : Loc.SF E K (n' + c') (n + c)) : Loc.SF E K n' n :=
  Loc.E1 psi (LocE.valsQ E (qOf P) A B) (((qOf P : K) ^ B)⁻¹) Psi

end Defs

end GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance
