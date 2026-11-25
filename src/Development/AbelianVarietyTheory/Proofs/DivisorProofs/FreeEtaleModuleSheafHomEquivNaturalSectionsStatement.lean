module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafHomEquivNaturalSections
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
open GlobalTheory.EtC.FreeHom in

theorem _root_.GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections :
    ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R),
      (∀ s s' : (free R).obj P ⟶ G, (∀ U x, val s U x = val s' U x) → s = s') ∧
      (∀ φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U,
        (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)),
          φ V (P.map g.op x) = Sec.res g (φ U x)) →
        ∃ s : (free R).obj P ⟶ G, ∀ U x, val s U x = φ U x) ∧
      (∀ (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)),
        val s V (P.map g.op x) = Sec.res g (val s U x)) ∧
      (∀ (P' : PSh) (f : P' ⟶ P) (s : (free R).obj P ⟶ G) U x,
        val ((free R).map f ≫ s) U x = val s U (f.app (op U) x)) ∧
      (∀ (G' : Shv R) (ψ : G ⟶ G') (s : (free R).obj P ⟶ G) U x,
        val (s ≫ ψ) U x = Sec.map ψ (val s U x)) ∧
      ∀ (s s' : (free R).obj P ⟶ G) (m : ℤ) U x,
        val (s + s') U x = val s U x + val s' U x ∧
        val (m • s) U x = m • val s U x :=
  _root_.GlobalTheory.EtC.FreeHom.main
