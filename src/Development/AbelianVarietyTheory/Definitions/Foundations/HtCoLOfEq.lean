module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoIOfEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def HTCoL (A : ValuationSubring Ω) (c : Coef l) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : Prop :=
  ∃ (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω), (∀ i, ‖o i‖ ≤ 1 ∧ FixIc c (o i) ∧ ‖j (w i)‖ ≤ 1) ∧
    ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg m ((l : Qbar l) ^ c₀ * Z m s y) ((l : Qbar l) ^ c₀ * h * lamv l m s + ∑ i, o i * (j (s (w i)) - j (w i)))

theorem htCoL_of_eq (A : ValuationSubring Ω) (c : Coef l) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) (hZ : ∀ s, Z m s y = h * lamv l m s) : HTCoL A c j Z m c₀ y h :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun s _ _ => by simp [Cg, hZ, mul_assoc]⟩

end GlobalTheory.LambdaValuationPowers
