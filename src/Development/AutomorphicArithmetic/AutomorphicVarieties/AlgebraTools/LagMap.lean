module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.lag_map :
    ∀ {R R' E E' ι : Type} [CommRing R] [CommRing R'] [Ring E] [Ring E'] [Algebra R E] [Algebra R' E'] [Fintype ι] [DecidableEq ι] (φ : R →+* R') (π : E →+* E') (a : ι → R) (P : E), (∀ c, π (algebraMap R E c) = algebraMap R' E' (φ c)) → (∀ i j, i ≠ j → IsUnit (a i - a j)) → ∀ i, π (lag a P i) = lag (fun j => φ (a j)) (π P) i := by
  intro R R' E E' ι _ _ _ _ _ _ _ _ φ π a P hc ha i
  have key : ∀ q : R[X], π (aeval P q) = aeval (π P) (q.map φ) := by
    intro q
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext hc
  have hsm : ∀ (c : R) (x : E), π (c • x) = φ c • π x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
  have h0 := (eq_lag_iff a P i (fun j hj => ha i j (Ne.symm hj)) (lag a P i)).1 rfl
  have h1 := congrArg π h0
  rw [hsm, key] at h1
  simp only [map_prod, Polynomial.map_prod, map_sub, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C] at h1
  rw [eq_lag_iff (fun j => φ (a j)) (π P) i (fun j hj => by
      rw [← map_sub]; exact (ha i j (Ne.symm hj)).map φ) (π (lag a P i))]
  exact h1
