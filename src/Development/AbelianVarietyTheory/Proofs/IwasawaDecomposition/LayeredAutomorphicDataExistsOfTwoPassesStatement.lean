module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LayeredAutomorphicDataExistsOfTwoPasses
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.layeredAutomorphicData_exists_of_twoPasses : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) → ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' → RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  first | exact @GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes | exact GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes | (intros; apply GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes <;> assumption)
