module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimes
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

open CategoryTheory Polynomial

theorem _root_.GlobalTheory.T.cuspidal_label_polynomial_unique_all_primes : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCuspOf L P χ → GlobalTheory.GLq.IsCuspOf L P' χ → P = P' := by
  first | exact @GlobalTheory.GLq.isCuspOf_label_unique_allPrimes | exact GlobalTheory.GLq.isCuspOf_label_unique_allPrimes | (intros; apply GlobalTheory.GLq.isCuspOf_label_unique_allPrimes <;> assumption)
