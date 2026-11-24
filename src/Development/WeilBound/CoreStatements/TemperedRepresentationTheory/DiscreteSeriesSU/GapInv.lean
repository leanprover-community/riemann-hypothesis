module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneFock
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsDerivedOnOfIsKMod
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

namespace PositivityTheory.DiscreteSeriesGap.GapInv

theorem dsUnique_dec : GlobalTheory.Dec.DSUnique := by
  intro n ε lam H _ _ σ H' _ _ σ' hlam hσ hσ'
  exact GlobalTheory.CompanionTheory.DSUniq.ds_unique
    CompanionTheory.D.LK.hMultAlg CompanionTheory.D.LK.hKModExists
    CompanionTheory.D.LK.hOrthCyc n ε lam H H' σ σ' hlam hσ hσ'

theorem lowKMultOne_dec : GlobalTheory.Dec.LowKMultOne := CompanionTheory.D.LK.low_K_type_multiplicity_one

end PositivityTheory.DiscreteSeriesGap.GapInv
