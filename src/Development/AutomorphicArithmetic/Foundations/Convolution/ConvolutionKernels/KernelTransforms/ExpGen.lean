module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGen
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

open Matrix GlobalTheory.CuspRep in
private theorem matEq_exp (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ)
    (X : Matrix (Fin n) (Fin n) (Cinf K)) :
    UpperTheory.V.Cm.matEq K n (NormedSpace.exp X) = NormedSpace.exp (UpperTheory.V.Cm.matEq K n X) := by
  letI : Algebra ℚ (ArchMatrix K n) := Algebra.compHom _ (algebraMap ℚ ℝ)
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp (𝔸 := Matrix (Fin n) (Fin n) (Cinf K)) (UpperTheory.V.Cm.matEq K n)
    (show Continuous (UpperTheory.V.Cm.matEq K n) from (UpperTheory.V.Cm.archEq K n).continuous) X

theorem UpperTheory.ConvolutionTheory.Tf.expGen :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ),
      Subgroup.closure (Set.range (isExpLieAlgebra K n).expG) = ⊤ := by
  intro K _ _ _ n
  rw [eq_top_iff]
  intro z _
  have key := UpperTheory.V.AlgRepEndIrreducible.expGen K n
    ((Subgroup.closure (Set.range (isExpLieAlgebra K n).expG)).toSubmonoid.comap
      (UpperTheory.V.Cm.grpEq K n).toMonoidHom) ?_ ((UpperTheory.V.Cm.grpEq K n).symm z)
  · simpa using key
  · intro X y hy
    refine Subgroup.subset_closure ⟨⟨UpperTheory.V.Cm.matEq K n X, Submodule.mem_top⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    change NormedSpace.exp (UpperTheory.V.Cm.matEq K n X) = UpperTheory.V.Cm.matEq K n y.val
    rw [hy, matEq_exp]
