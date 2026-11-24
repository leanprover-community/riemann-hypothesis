module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyDimensionBoundCocycles
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.cech_first_cohomology_dimension_bound_cocycles : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (s : Y ⟶ Sp K) (g : ℕ) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), Module.Finite K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) → Module.finrank K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) ≤ g → ∀ (e : Fin (g + 1) → ∀ i i' : κ, Γ(Y, D i ⊓ D i')), (∀ b i i' i'', resG Y (inf_le_left : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i') (e b i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i' ⊓ D i'') (e b i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i'') (e b i i'')) → ∃ c : Fin (g + 1) → K, c ≠ 0 ∧ ∃ h : ∀ i, Γ(Y, D i), ∀ i i', ∑ b, (s.appLE ⊤ (D i ⊓ D i') le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  first | exact @GlobalTheory.OrdCechDep.exists_comb_coboundary | exact GlobalTheory.OrdCechDep.exists_comb_coboundary | (intros; apply GlobalTheory.OrdCechDep.exists_comb_coboundary <;> assumption)
