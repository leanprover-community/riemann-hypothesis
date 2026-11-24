module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
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

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

def flagStep (Ω : Type) [Field Ω] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : ℕ) : Submodule Ω E :=
  Submodule.span Ω (b₀ '' {k | (k : ℕ) < i})

namespace Lat

def IsFlagVBOn (L : Lat ξ E) (T : Set (Cpt ξ)) {r : ℕ} (b₀ : Fin r → E) : Prop :=
  ∀ p ∈ T, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ b : Fin r → E, (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧
    ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q

def gr (L : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) (i : Fin r) : Lat ξ Ω := fun p =>
  Submodule.span (regAt ξ p) {t | ∃ e ∈ L p, e - t • b₀ i ∈ flagStep Ω b₀ i}

def IsGenAt (Λ : Lat ξ Ω) (p : Cpt ξ) (t : Ω) : Prop := t ≠ 0 ∧ Λ p = Submodule.span (regAt ξ p) {t}

def tens {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) : Lat ξ Ω := fun p =>
  Submodule.span (regAt ξ p) {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i}

end Lat

def IsGenericFlag {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {E' : Type} [AddCommGroup E'] [Module Ω' E']
    (j : E →+ E') {S : Type} {r : S → ℕ} (V : S → Submodule Ω E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ) : Prop :=
  ∃ (c : ∀ σ, Fin (r σ) → E) (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω'),
    (∀ σ, LinearIndependent Ω (c σ) ∧ Submodule.span Ω (Set.range (c σ)) = V σ) ∧
    (∀ (a : Ω) e, j (a • e) = algebraMap Ω Ω' a • j e) ∧ (∀ σ, LinearIndependent Ω' fun k => j (c σ k)) ∧
    (∀ σ, LinearIndependent Ω' (b₀ σ)) ∧ (∀ σ k, u σ k k = 1) ∧ (∀ σ l k, l < k → u σ l k = 0) ∧
    (∀ σ i, flagStep Ω' (b₀ σ) i = flagStep Ω' (fun k => ∑ l, u σ l k • j (c σ l)) i) ∧
    AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧
    0 < d ∧ Module.finrank (IntermediateField.adjoin Ω
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω' = d

end GlobalTheory.CompanionTheory.Ar
