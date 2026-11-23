module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_haar_adelicVectors_bounds_pureTensors_slices : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) → ∀ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      ∃ μ : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        ∃ C c : ℝ≥0∞, C ≠ ⊤ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
          (∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μ ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) ∧
          ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
            ∀ y, c * ∫⁻ z, ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2 ≤ ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds | exact GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds | (intros; apply GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds <;> assumption)
