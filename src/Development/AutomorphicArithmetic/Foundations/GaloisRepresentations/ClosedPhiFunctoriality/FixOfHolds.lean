module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem fix_aux {A S : Type} [CommSemiring A] [Semiring S] [Algebra A S] (φ : S →ₐ[A] S) (x y : ℕ) (c : S)
    (h : (φ ^ y) c = (φ ^ x) c) : (φ ^ ((x : ℤ) - y).natAbs) ((φ ^ y) c) = (φ ^ y) c := by
  rcases le_total x y with hxy | hxy
  · have e : ((x : ℤ) - y).natAbs = y - x := by omega
    rw [e, h, ← AlgHom.mul_apply, ← pow_add, Nat.sub_add_cancel hxy, h]
  · have e : ((x : ℤ) - y).natAbs = x - y := by omega
    rw [e, ← AlgHom.mul_apply, ← pow_add, Nat.sub_add_cancel hxy, h]

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.fixOf_holds :
    FixOf := by
  intro l _ E Ω _ _ _ _ _ w A h O _ _ _ Bw hj g c hc
  obtain ⟨a, b, hσ⟩ := g.2
  have hal : (alpha l g) = ((resDeg l w * a : ℕ) : ℤ) - ((resDeg l w * b : ℕ) : ℤ) := by
    rw [alpha, deg_eq hσ]; push_cast; ring
  obtain ⟨c', rfl⟩ := (Algebra.IsAlgebraic.algHom_bijective (frobUr l ^ (resDeg l w * b))).2 c
  have h1 := weilToGK_frobUr hj g hσ c'
  rw [mem_GK.mp (weilToGK Bw h g).2 _ hc] at h1
  rw [hal]
  exact fix_aux _ _ _ _ (Subtype.ext h1)
