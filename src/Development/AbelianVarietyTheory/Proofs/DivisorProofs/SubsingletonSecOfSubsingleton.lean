module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplitting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionMapAugmentationSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUnique
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma isEmpty_of_isUnit_zero (U : Scheme) (h : IsUnit (0 : Γ(U, ⊤))) : IsEmpty U := by
  constructor
  intro x
  have h01 : (0 : Γ(U, ⊤)) = 1 := isUnit_zero_iff.1 h
  have := congrArg (U.presheaf.germ ⊤ x trivial).hom h01
  rw [map_zero, map_one] at this
  exact zero_ne_one this

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma isEmpty_of_prim_zero (U : Scheme)
    (ζ : _root_.GlobalTheory.EtC.Prim 0 Γ(U, ⊤)) : IsEmpty U :=
  isEmpty_of_isUnit_zero U (by simpa using ζ.2.1)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma sec_eq_of_isEmpty' {R : Type} [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R) (U : Scheme)
    [IsEmpty U] (a b : _root_.GlobalTheory.EtC.Sec F U) : a = b :=
  (_root_.GlobalTheory.EtC.sec_ext_glue R F U).1 a b
    ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun _ _ h => h.elim⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.twPair_spec (q : ℕ) (i j : ℤ) :
    _root_.GlobalTheory.EtC.IsTwPair (_root_.GlobalTheory.EtC.twPair q i j) := by
  by_cases hq : q = 0
  · subst hq
    unfold _root_.GlobalTheory.EtC.IsTwPair
    intro U ζ
    haveI := isEmpty_of_prim_zero U ζ
    exact sec_eq_of_isEmpty' _ _ _ _
  · haveI : NeZero q := ⟨hq⟩
    exact (_root_.GlobalTheory.EtC.TwPairUniq.main q i j).1

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.kumT_spec (q : ℕ) : _root_.GlobalTheory.EtC.IsKum q (_root_.GlobalTheory.EtC.kumT q) := by
  by_cases hq : q = 0
  · subst hq
    unfold _root_.GlobalTheory.EtC.IsKum
    refine ⟨fun V U g v h => ?_, fun U ζ v w _ => ?_⟩
    · haveI := isEmpty_of_isUnit_zero U (by simpa using h)
      haveI : IsEmpty V := ⟨fun x => IsEmpty.false (g.base x)⟩
      exact sec_eq_of_isEmpty' _ _ _ _
    · haveI := isEmpty_of_prim_zero U ζ
      exact sec_eq_of_isEmpty' _ _ _ _
  · haveI : NeZero q := ⟨hq⟩
    exact _root_.GlobalTheory.EtC.KummerSplit.isKum_kumT q

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.restrMap_spec {S R : Type} [CommRing S] [CommRing R] (φ : R →+* S)
    (F : _root_.GlobalTheory.EtC.Shv S) (U : Scheme.{0}) (a : _root_.GlobalTheory.EtC.Sec F U) :
    (_root_.GlobalTheory.EtC.restrMap φ F).app U 0
        (_root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι S F) a) =
      _root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι R ((_root_.GlobalTheory.EtC.restr φ).obj F))
        (show _root_.GlobalTheory.EtC.Sec ((_root_.GlobalTheory.EtC.restr φ).obj F) U from a) :=
  _root_.GlobalTheory.EtC.restrMap_spec' R S φ F U a

end GlobalTheory.EtC

end
