module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedAdelicDataSaturatedOverFixedField
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.untwisted_adelic_data_saturated_over_fixed_field : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 → StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok) (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧ (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧ ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw | exact GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw | (intros; apply GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw <;> assumption)
