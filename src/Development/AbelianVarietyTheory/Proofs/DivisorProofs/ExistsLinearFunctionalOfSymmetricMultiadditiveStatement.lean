module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalOfSymmetricMultiadditive
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (d : ℕ) (F : (Fin (d + 1) → HermLB p) → ℝ), (∀ L M, (∀ a, (L a).Isometric (M a)) → F L = F M) → (∀ L (e : Equiv.Perm (Fin (d + 1))), F (fun a => L (e a)) = F L) → (∀ (A B : HermLB p) (L : Fin d → HermLB p), F (Fin.cons (A.tens B) L) = F (Fin.cons A L) + F (Fin.cons B L)) → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, (∀ n : Fin (d + 1) → ι → ℤ, Φ (∏ a, lin fun i => (n a i : ℝ)) = F fun a => comb L (n a)) ∧ ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d + 1 → P.IsHomogeneous e → Φ P = 0 := by
  first | exact @GlobalTheory.MixHt.exists_linear_of_multiadditive | exact GlobalTheory.MixHt.exists_linear_of_multiadditive | (intros; apply GlobalTheory.MixHt.exists_linear_of_multiadditive <;> assumption)
