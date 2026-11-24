module

public import Formalism.LocalRingCardinality.DataCD
public import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarScaling.MapEqSelfOfIterate
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem haar_box_prod_finite_pos : ∀ (ι : Type) [Fintype ι] (p q : ι → ℕ) (m : ∀ i, Measure (UpqT (p i) (q i))), (∀ i, (m i).IsHaarMeasure) → ∃ B : ∀ i, Set (UpqT (p i) (q i)), (∀ i, MeasurableSet (B i)) ∧ ∏ i, m i (B i) ≠ 0 ∧ ∏ i, m i (B i) ≠ ⊤ := by
  intro ι _ p q m hm
  have hK : ∀ i, ∃ K : Set (UpqT (p i) (q i)), IsCompact K ∧ K ∈ nhds (1 : UpqT (p i) (q i)) :=
    fun i => exists_compact_mem_nhds 1
  choose K hKc hKn using hK
  refine ⟨fun i => interior (K i), fun i => isOpen_interior.measurableSet, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (isOpen_interior.measure_pos (m i) ⟨1, mem_interior_iff_mem_nhds.mpr (hKn i)⟩).ne'
  · apply ENNReal.prod_ne_top
    intro i _
    exact (lt_of_le_of_lt (measure_mono interior_subset) (hKc i).measure_lt_top).ne

end GlobalTheory
