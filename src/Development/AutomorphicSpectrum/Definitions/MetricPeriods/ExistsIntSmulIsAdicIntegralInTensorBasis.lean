module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.CompletePartialOrder
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

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open GlobalTheory.CompanionTheory.Ar

section Field

variable {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]


open Classical in
def eigComp (ρ : O →+* Module.End k V) (σ : O →+* k) (x : V) : V := by
  classical
  exact if h : ∃ p ∈ eigSp ρ σ, x - p ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ' then
    h.choose
  else
    0

def oSpan (ρ : O →+* Module.End k V) {r : ℕ} (v : Fin r → V) : AddSubgroup V :=
  AddSubgroup.closure {x | ∃ (a : O) (i : Fin r), x = ρ a (v i)}

def IsOFamily (ρ : O →+* Module.End k V) (I : AddSubgroup V) {r : ℕ} (v : Fin r → V) : Prop :=
  (∀ i, v i ∈ I) ∧ (∀ a : Fin r → O, ∑ i, ρ (a i) (v i) = 0 → a = 0) ∧ (oSpan ρ v).relIndex I ≠ 0

def logIdx {R : Type} [CommRing R] [Module R V] (F : Submodule R V) {ι : Type} (b : ι → V) : ℝ :=
  Real.log (((Submodule.span R (Set.range b)).toAddSubgroup.relIndex F.toAddSubgroup : ℕ) : ℝ) -
    Real.log ((F.toAddSubgroup.relIndex (Submodule.span R (Set.range b)).toAddSubgroup : ℕ) : ℝ)

end Field

variable {V O Ψ : Type} [AddCommGroup V] [Module ℂ V] [CommRing O] [Fintype Ψ]

def PhiNormSq (ρ : O →+* Module.End ℂ V) (hb : V → V → ℂ) (I : AddSubgroup V) (κ : ℝ) (σ : Ψ → (O →+* ℂ)) {m : ℕ}
    (b : Ψ → Fin m → V) (ν : ℝ) : Prop :=
  ∃ (r k : ℕ) (h : r + k = m) (v : Fin r → V) (q : Ψ → Fin k → V) (T : Ψ → Matrix (Fin m) (Fin m) ℂ),
    IsOFamily ρ I v ∧ (∀ τ c, q τ c ∈ eigSp ρ (σ τ)) ∧
    (∀ τ i, Fin.append (fun a => eigComp ρ (σ τ) (v a)) (q τ) i = ∑ j, T τ j (Fin.cast h i) • b τ j) ∧
    (∀ τ, (T τ).det ≠ 0) ∧
    ν = (((oSpan ρ v).relIndex I : ℕ) : ℝ) *
      ∏ τ, κ ^ r * (Matrix.of fun c c' => hb (q τ c) (q τ c')).det.re / ‖(T τ).det‖ ^ 2

end GlobalTheory.CompanionTheory.Ar.Cusp
