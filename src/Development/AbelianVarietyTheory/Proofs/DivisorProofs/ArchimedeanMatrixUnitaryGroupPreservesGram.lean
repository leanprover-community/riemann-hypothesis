module

public import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReindexUnitary
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ArchUnit

theorem gram_archM : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
    Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → ∀ g : GA D V, gram τ (-(V.gram)ᵀ) (archM V θ g) = (-(V.gram)ᵀ).map τ := by
  intro D V τ θ hθ g
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  have hu := GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram τ
    (fun x => IsCMField.complexEmbedding_complexConj D.host.E τ x) θ hθ g
  have hm : archM V θ g = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram θ g := rfl
  rw [hm]
  have h' := congrArg Matrix.transpose hu
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h'
  have hG : (-(V.gram)ᵀ).map τ = -(V.gram.map τ)ᵀ := by
    ext a b
    simp
  have hg : ∀ (G : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
    intro G x
    ext a b
    simp only [gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hg, hG, Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.mul_assoc]
  exact h'

end GlobalTheory.ArchUnit
