module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.KapLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def stdH (w : Pl E) {n : ℕ} (v v' : Fin n → w.adicCompletion E) : w.adicCompletion E :=
  ∑ k, v k * cj w (v' k)

def Bridge (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) : Prop :=
  (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧
    (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2

def Fits (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (Q : (w.adicCompletion E)[X]) (u : B.A) : Prop :=
  Algebra.adjoin K.E {u} = ⊤ ∧ aeval u (Q.map e.symm.toRingHom) = 0 ∧ Module.finrank K.E B.A = Q.natDegree ∧
    u * B.σ u = 1

def IsModel (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) : Prop :=
  ∃ ψ : B.A ≃+ (Fin n → w.adicCompletion E), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) ∧
    (∀ y, ψ (u * y) = γ.val *ᵥ ψ y) ∧ ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)

def congSet (w : Pl E) (n k : ℕ) : Set (GLw n w) :=
  {g | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
    WithZero.exp (-(k : ℤ))}

theorem cast_finsum {α : Type*} (f : α → ℚ) : ((∑ᶠ a, f a : ℚ) : ℂ) = ∑ᶠ a, (f a : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h' : ¬ (Function.support fun a => (f a : ℂ)).Finite := by
      simpa [Function.support] using h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h']
    simp

end GlobalTheory.KapLat
