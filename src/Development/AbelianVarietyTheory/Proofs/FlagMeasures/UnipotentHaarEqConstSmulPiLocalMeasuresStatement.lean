module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstSmulPiLocalMeasures
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

theorem _root_.GlobalTheory.T.unipotentHaar_eq_const_smul_pi_localMeasures : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (fun v => muNl C (X.pl v) v) := by
  first | exact @GlobalTheory.MuNPi.muN_eq_pi_muNl | exact GlobalTheory.MuNPi.muN_eq_pi_muNl | (intros; apply GlobalTheory.MuNPi.muN_eq_pi_muNl <;> assumption)
