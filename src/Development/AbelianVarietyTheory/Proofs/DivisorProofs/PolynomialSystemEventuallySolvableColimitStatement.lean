module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSystemEventuallySolvableColimit
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

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.polynomial_system_eventually_solvable_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (σ ι : Type) [Finite σ] [Finite ι] (p : ι → MvPolynomial σ (F.obj j)) (x : σ → c.pt),
    (∀ i, MvPolynomial.eval₂ (c.ι.app j).hom x (p i) = 0) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), ∃ y : σ → F.obj k,
      ∀ i, MvPolynomial.eval₂ (F.map (f₀ ≫ f)).hom y (p i) = 0 := by
  first | (exact @GlobalTheory.TorsorColim.poly_eventually_solvable) | (exact GlobalTheory.TorsorColim.poly_eventually_solvable) | (intros; apply GlobalTheory.TorsorColim.poly_eventually_solvable  <;> assumption)
