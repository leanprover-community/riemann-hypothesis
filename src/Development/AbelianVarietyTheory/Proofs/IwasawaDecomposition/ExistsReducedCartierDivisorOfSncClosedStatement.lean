module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosed
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j] (T : TopologicalSpace.Closeds X), ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → j (genericPoint Y) ∉ T → ∃ D : CartierDiv Y, D.Eff ∧ (∀ y, y ∈ D.supp ↔ j y ∈ T) ∧ ∀ (y : Y) (g : Y.functionFieldˣ), D.IsEqn y g → ∀ (f : Y.functionField) (n : ℕ), RegAt y f → RegAt y (f ^ n / g) → RegAt y (f / g) := by
  first | exact @GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv | exact GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv | (intros; apply GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv <;> assumption)
