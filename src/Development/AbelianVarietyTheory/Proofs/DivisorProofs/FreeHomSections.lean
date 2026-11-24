module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.free_hom_sections : ∀ (R : Type) [CommRing R] (P : _root_.GlobalTheory.EtC.PSh)
    (F : _root_.GlobalTheory.EtC.Shv R),
    (∀ a : ∀ U : Scheme.{0}, P.obj (op U) → _root_.GlobalTheory.EtC.Sec F U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) x,
        _root_.GlobalTheory.EtC.Sec.res g (a U x) = a V (P.map g.op x)) →
      ∃ φ : (_root_.GlobalTheory.EtC.free R).obj P ⟶ F, ∀ U x,
        _root_.GlobalTheory.EtC.Sec.map φ (_root_.GlobalTheory.EtC.freeGen R P U x) = a U x) ∧
    (∀ φ ψ : (_root_.GlobalTheory.EtC.free R).obj P ⟶ F,
      (∀ U x, _root_.GlobalTheory.EtC.Sec.map φ (_root_.GlobalTheory.EtC.freeGen R P U x) =
        _root_.GlobalTheory.EtC.Sec.map ψ (_root_.GlobalTheory.EtC.freeGen R P U x)) → φ = ψ) ∧
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) x,
      _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.freeGen R P U x) =
        _root_.GlobalTheory.EtC.freeGen R P V (P.map g.op x)) ∧
    ∀ (Q : _root_.GlobalTheory.EtC.PSh) (f : P ⟶ Q) U x,
      _root_.GlobalTheory.EtC.Sec.map ((_root_.GlobalTheory.EtC.free R).map f)
          (_root_.GlobalTheory.EtC.freeGen R P U x) =
        _root_.GlobalTheory.EtC.freeGen R Q U (f.app (op U) x) := by
  intro R _ P F
  exact ⟨fun a ha => _root_.GlobalTheory.EtC.CupSpec.free_exists P F a ha,
    fun φ ψ h => _root_.GlobalTheory.EtC.CupSpec.free_ext φ ψ h,
    fun V U g x => _root_.GlobalTheory.EtC.CupSpec.freeGen_res P g x,
    fun Q f U x => _root_.GlobalTheory.EtC.CupSpec.freeGen_map f U x⟩

end GlobalTheory.EtC
