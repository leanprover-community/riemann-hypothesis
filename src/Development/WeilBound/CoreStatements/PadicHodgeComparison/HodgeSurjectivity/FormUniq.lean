module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

def OmRes : Prop := ∀ (K : Type) [Field K] (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (V V' : Z.Opens) (h : V' ≤ V)
  (k : inU q V' ≤ inU q V), ∃ φ : Sec q V →ₐ[K] Sec q V', (∀ g, φ g = rs h g) ∧
    (∀ (a : ℕ) (g₀ : Sec q V) (g : Fin a → Sec q V) c, IsForm q V g₀ g c →
      IsForm q V' (φ g₀) (fun j => φ (g j)) ((resU (G q a) k).pull a c)) ∧
    ∀ (a : ℕ) e e', IsOm q V a e → IsOm q V' a e' → ∀ ω, (resU (G q a) k).pull a (e ω) = e' (omMap φ a ω)

def FormUniq : Prop := ∀ (K : Type) [Field K] (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens),
  Nonempty (Lifts q V) ∧ ∀ (a : ℕ) (g₀ : Sec q V) (g : Fin a → Sec q V), ∃! c, IsForm q V g₀ g c

def TopRes : Prop := ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U Q : ObjectProperty C),
  (∀ T, U T) → ∀ n, Function.Bijective ((CH.Mor.restrict F U.ι).pullC n) ∧
    ∀ z, (CH.Mor.restrict F U.ι).pullC n z ∈ relS (U.ι ⋙ F) (fun T => Q T.obj) n ↔ z ∈ relS F Q n

end CrystallineSemistableComparison.Onto

end
