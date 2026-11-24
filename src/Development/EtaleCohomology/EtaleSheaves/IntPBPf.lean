module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntPBPf

def IntHens : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] (φ : A →+* B), φ.IsIntegral →
  HenselianRing B ((IsLocalRing.maximalIdeal A).map φ)

def IntFib : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)), IsIntegralHom p →
  ∃ (B : Type) (_ : CommRing B) (φ : A →+* B), φ.IsIntegral ∧ ∀ (q : ℕ) (i : ℤ),
    Eqv _ (spMap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ))) (tw q i) →
    Eqv _ (sch.map (pullback.fst p (LateralTheory.E.t_E2Cut.cpt A))) (tw q i)

theorem IntPB_of (hH : IntHens) (hF : IntFib) : LateralTheory.E.t_E2Cut.IntPB := by
  intro hyp q i A _ _ hSH hq X p hp
  obtain ⟨hA, -⟩ := hSH
  obtain ⟨B, _, φ, hφ, hE⟩ := hF A p hp
  have : HenselianRing B ((IsLocalRing.maximalIdeal A).map φ) := hH A B φ hφ
  have hqB : IsUnit ((q : ℕ) : B) := by simpa using hq.map φ
  exact hE q i (hyp.e1 q B _ hqB i)

end LateralTheory.E.IntPBPf
