module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealLeThickening
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

theorem _root_.GlobalTheory.T.homogeneous_ideal_le_thickening : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    ∀ (J : Ideal (MvPolynomial (Fin (N + 1)) R)), HomogIdeal J →
    (∀ e, J ≤ vanIdeal (i e ≫ thickι R I N e)) →
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ (PO R N).left) (b : ∀ e, Cs e ⟶ C'),
      IsClosedImmersion j ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst (PO R N).hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e := by
  exact @GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal
