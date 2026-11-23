module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKaehlerEqOfUniversalTangent
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.eq_of_universal_tangent_dualNumber : ∀ (R A k : Type) [CommRing R] [CommRing A] [Algebra R A] [Field k] (n d : ℕ)
    [Module.Free A (Ω[A⁄R])] [Module.Finite A (Ω[A⁄R])], Module.finrank A (Ω[A⁄R]) = n →
    ∀ (φ : A →+* k) (ψ : A →+* TrivSqZeroExt k (Fin d → k)),
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ →
    ψ.comp (algebraMap R A) = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (algebraMap R A)) →
    (∀ v : A →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
      v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) →
      ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ) → d = n := by
  first | exact @GlobalTheory.finrank_kaehler_eq_of_universal_tangent | exact GlobalTheory.finrank_kaehler_eq_of_universal_tangent | (intros; apply GlobalTheory.finrank_kaehler_eq_of_universal_tangent <;> assumption)
