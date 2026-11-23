module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKummerClassExplicitCocycle : Prop :=
  ∀ (q : ℕ) [NeZero q],
    (∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
      ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
        CohomologyClass.mk γ = kum q u ∧
        (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
        ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ),
          v ^ q = Units.map x.appTop.hom.toMonoidHom u →
          ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
      pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)) ∧
    ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
      kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0
