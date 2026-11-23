module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureZmodTorsorGenericFibreData
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.integralClosure_zmodTorsor_genericFibre_data : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [Nontrivial R] [Module.Flat A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    (∀ f : GlobalTheory.LocAcyc.GenFib A R, IsIntegral R f → ∃ r : R, algebraMap R (GlobalTheory.LocAcyc.GenFib A R) r = f) →
    ∀ (q : ℕ) [NeZero q] (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] D)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) D q act →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∃ (act' : Multiplicative (ZMod q) →* (GlobalTheory.KeyOriginNoeth.closure A R D ≃ₐ[R] GlobalTheory.KeyOriginNoeth.closure A R D))
      (T : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] R),
      (∀ c, algebraMap R _ (T c) = ∑ g, act' g c) ∧
      (∃ a : A, a ≠ 0 ∧ ∃ (n : ℕ) (x y : Fin n → GlobalTheory.KeyOriginNoeth.closure A R D),
        ∀ g, ∑ i, x i * act' g (y i) = if g = 1 then algebraMap R _ (algebraMap A R a) else 0) ∧
      GlobalTheory.GoodEtale.TorsionFreeOver A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Algebra.IsIntegral R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Nontrivial (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.ClosureData.closureData) | (exact GlobalTheory.ClosureData.closureData) | (intros; apply GlobalTheory.ClosureData.closureData  <;> assumption)
