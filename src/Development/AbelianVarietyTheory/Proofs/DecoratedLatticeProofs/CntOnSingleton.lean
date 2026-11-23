module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntClLeEncardMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountPrimitiveSublatticesOverGenus
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeProdReal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeSizeZ
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsRawMassAndGenusMass
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

theorem cntOn_singleton : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ c : ℝ, CntOn {c} := by
  intro hM c Cg cb Cu cT CT
  obtain ⟨C1a, hC1⟩ := GlobalTheory.Mass.PrimMeanRow.main 1 one_pos
  obtain ⟨c3, hC3⟩ := GlobalTheory.LoopC.PairMean.main Cg cb Cu cT CT c 1 3 (max C1a 0) (le_max_right _ _)
  obtain ⟨cH, -, hHH⟩ := GlobalTheory.GramHeight.height_bounds Cg cb Cu cT CT c 1
  obtain ⟨cS, hSW⟩ := GlobalTheory.LoopC.GenericMean.main Cg cb Cu cT CT c 1
  obtain ⟨c4, hC4⟩ := GlobalTheory.LoopC.Partner.partners_le Cg cb Cu cT CT c 1
  refine ⟨c3, cH, cS, c4, 1, fun C0 hC0 C' Cl _ hl D large₂ u => ?_⟩
  rw [Set.mem_singleton_iff] at hC0
  subst hC0
  refine ⟨fun C hC => ?_, ?_, ?_, ?_⟩
  · exact hC3 C hC _ _ u u _ _ hl (GlobalTheory.Mass.RowsRawMass.main _ u)
      (hC1 _ (le_max_left _ _) _ _ u u _ _ Cg cb Cu cT CT C0 1 hl)
  · exact hHH _ _ u u _ _ hl
  · exact hSW _ _ u u _ _ hl
      (GlobalTheory.Mass.PrimMeanCorankOne.main _ _ u u _ _ Cg cb Cu cT CT C0 1 (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hM _))
  · exact hC4 _ _ u u _ _ hl

end GlobalTheory.Core.Deg
