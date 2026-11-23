module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFiniteDimensionalCompactTranslatesOfLevelT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsZFiniteOfCentreSpan
public import Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalSpanRangeOfColumnsMem
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

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.isAutomorphicForm_of_bdd_submodule :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → ∀ φ ∈ S, IsAutomorphicForm φ.1 := by
  intro K _ _ n S hS φ hφ
  obtain ⟨V, hV, hVφ⟩ := UpperTheory.exists_finiteDimensional_compact_translates_of_level_types K n S hS.level hS.types
  refine ⟨hS.left φ hφ, ⟨φ.2, ?_⟩, ?_, ?_, hS.growth φ hφ⟩
  · intro g
    obtain ⟨L, hL, hLφ⟩ := hS.level
    filter_upwards [hL.mem_nhds L.one_mem] with y hy
    exact hLφ φ hφ y hy g
  · exact UpperTheory.finiteDimensional_span_range_of_columns_mem (Reduction.maxCompact (K := K) (n := n)) _
      (fun k g => (φ : AdelicGLn.AdelicGL K n → ℂ) (g * k)) V hV (fun g => hVφ φ hφ g)
  · exact UpperTheory.isZFinite_of_centre_span K n φ (hS.mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hφ)).centre
