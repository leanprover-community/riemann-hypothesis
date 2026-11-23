module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyConcreteRowDataOfFinitenessBundle
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.nonempty_concreteRowData_of_finitenessBundle : Formalism.L2.SG.Pf.WuDecayOfGap → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (S : Formalism.L2.SG.SpectralTiesReal.STies D), 29 ≤ C' → 29 ≤ Cl → FinX S.Y → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → Nonempty (Formalism.L2.SG.ThmSOwn.ConcK D) := by
  first | exact @GlobalTheory.Core.Diag.concK_of_finX | exact GlobalTheory.Core.Diag.concK_of_finX | (intros; apply GlobalTheory.Core.Diag.concK_of_finX <;> assumption)
