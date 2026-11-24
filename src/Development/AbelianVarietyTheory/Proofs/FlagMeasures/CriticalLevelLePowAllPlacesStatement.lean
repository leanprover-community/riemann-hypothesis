module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CriticalLevelLePowAllPlaces
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.criticalLevel_le_pow_allPlaces : Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ, Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m : ℝ)) := by
  first | exact @GlobalTheory.CritLevelUpper.tcrit_le_pow | exact GlobalTheory.CritLevelUpper.tcrit_le_pow | (intros; apply GlobalTheory.CritLevelUpper.tcrit_le_pow <;> assumption)
