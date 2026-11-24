module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1TrivialBundleRankBound
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

theorem _root_.GlobalTheory.T.abelian_cech_h1_trivial_bundle_rank_bound : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Module.Finite K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ∧ Module.finrank K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ≤ g := by
  first | exact @GlobalTheory.AbCoh.FDimField.cechLB_triv_finite_finrank_one_le | exact GlobalTheory.AbCoh.FDimField.cechLB_triv_finite_finrank_one_le | (intros; apply GlobalTheory.AbCoh.FDimField.cechLB_triv_finite_finrank_one_le <;> assumption)
