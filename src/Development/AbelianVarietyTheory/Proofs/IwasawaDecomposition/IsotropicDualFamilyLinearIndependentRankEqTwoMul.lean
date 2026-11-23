module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.familyIsotropicDual_linearIndependent_and_card : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  intro r d M e f hiso hdual hspan
  have hli : LinearIndependent ℝ (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have hb : ∀ k, g (Sum.inr k) = 0 := by
      intro k
      have h := congrArg (fun v => v ⬝ᵥ M *ᵥ e k) hg
      simpa [add_dotProduct, sum_dotProduct, smul_dotProduct, hiso, hdual] using h
    have ha : ∀ k, g (Sum.inl k) = 0 := by
      intro k
      have hg' : ∑ i, g (Sum.inl i) • e i = 0 := by simpa [hb] using hg
      have h := congrArg (fun v => f k ⬝ᵥ M *ᵥ v) hg'
      simpa [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, hdual] using h
    rintro (k | k)
    · exact ha k
    · exact hb k
  refine ⟨hli, ?_⟩
  have h1 := finrank_span_eq_card hli
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
  omega
