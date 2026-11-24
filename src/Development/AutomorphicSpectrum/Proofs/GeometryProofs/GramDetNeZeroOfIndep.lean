module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt


open scoped ComplexOrder in
theorem gramDet_ne_zero_of_linearIndependent :
    ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (f : Fin n → B.carrier), LinearIndependent (𝓞 L) f → B.gramDet σ f ≠ 0 := by
  intro L _ _ B σ n f hf
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec B.metric σ (f i)) =
      Matrix.of fun i j ↦ (B.metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f i) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f j) := by
    ext i j
    rfl
  have hp := (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hf)).det_pos
  rw [hG] at hp
  exact hp.ne'

end GlobalTheory.CompanionTheory.Ar.RootHt
