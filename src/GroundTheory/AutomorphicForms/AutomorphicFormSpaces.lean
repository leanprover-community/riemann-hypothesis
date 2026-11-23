module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.LeftTranslate
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ArchSliceUAction
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Translation
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.SmoothKZ
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStructure
import GroundTheory.AutomorphicForms.ReductionMeasure
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

theorem archPart_infEmb (a : archGroup K n) : archPart (infEmb K n a) = a := by
  simp only [archPart, prodEquiv_infEmb, ContinuousMulEquiv.apply_symm_apply]

theorem archCompact_eq_image :
    (archCompact K n : Set (archGroup K n)) =
      archPart '' (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) := by
  ext a
  constructor
  · intro ha
    exact ⟨infEmb K n a, ha, archPart_infEmb a⟩
  · rintro ⟨k, hk, rfl⟩
    exact archPart_mem_archCompact hk


variable (K n) in
theorem isCompact_archCompact : IsCompact (archCompact K n : Set (archGroup K n)) := by
  rw [archCompact_eq_image]
  exact isCompact_maxCompact.image ((archEquiv K n).continuous.comp
    (continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous))

theorem unipMeasure_unipFundamentalDomain (r : ℕ) :
    unipMeasure K n r (unipFundamentalDomain K n r) = 1 := by
  rw [unipMeasure, unipFundamentalDomain, Measure.pi_pi]
  simp [GroundTheory.Global.adeleMeasure_fundamentalSet]

end AutomorphicForm

end

end GroundTheory.Automorphic
