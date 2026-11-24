module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaIdealFamily_universal_property : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (u : TObj g ((n ^ j) ^ 2) J b Y.s), (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' u x) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → ∃! f : S ⟶ Y.MM, f ≫ Y.s = s' ∧ TMap t u f := by
  first | exact @GlobalTheory.FamRep.family_universal | exact GlobalTheory.FamRep.family_universal | (intros; apply GlobalTheory.FamRep.family_universal <;> assumption)
