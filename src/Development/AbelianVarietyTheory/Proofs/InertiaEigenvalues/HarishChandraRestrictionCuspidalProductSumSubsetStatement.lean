module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionCuspidalProductSumSubset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraRestriction_cuspidal_product_sum_subsets : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (a b : ℕ), degL L = a + b → (∀ p ∈ L, IsCusp p.2) → ∀ x y, res a b (hcL L (a + b)) x y = ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ i ∈ I, (L.get i).1 = a), hcL ((I.sort (· ≤ ·)).map L.get) a x * hcL ((Iᶜ.sort (· ≤ ·)).map L.get) b y := by
  first | exact @GlobalTheory.GLq.ResCuspProd.main | exact GlobalTheory.GLq.ResCuspProd.main | (intros; apply GlobalTheory.GLq.ResCuspProd.main <;> assumption)
