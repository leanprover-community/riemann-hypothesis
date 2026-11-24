module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedColumnLatticeIntegralFrameCoords
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport


theorem _root_.GlobalTheory.T.completedColumnLattice_integral_frameCoords : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) → ∀ i, ((Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.FrameTransport.hatL_colLat_coord_int | exact GlobalTheory.FrameTransport.hatL_colLat_coord_int | (intros; apply GlobalTheory.FrameTransport.hatL_colLat_coord_int <;> assumption)
