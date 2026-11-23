module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFrameChangeMemIntegralGLAtPlace
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.localFrameChange_mem_integralGL_at_place : ∀ (D : D7) (P : Pl D.host.E) (m n : ℕ) (U Y : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) (κ : Matrix (Fin n) (Fin n) (Formalism.IndefR.Datum.EAf D)) (c : Formalism.IndefR.Datum.EAf D), GlobalTheory.StdFrames.cpt P c = 1 → (HMul.hMul U κ : Matrix (Fin m) (Fin n) (Formalism.IndefR.Datum.EAf D)) = c • Y + (1 - c) • U → IsIntM U → IsIntM Y → IsUnit (topL n (redM P U)).det → IsUnit (topL n (redM P Y)).det → (∀ a b, GlobalTheory.StdFrames.cpt P (κ a b) ∈ P.adicCompletionIntegers D.host.E) ∧ Valued.v (GlobalTheory.StdFrames.cpt P κ.det) = 1 ∧ (topL n (redM P U) = 1 → topL n (redM P Y) = 1 → ∀ a b, Valued.v (GlobalTheory.StdFrames.cpt P ((κ - 1) a b)) < 1) := by
  first | exact @GlobalTheory.LocCore.kappa_integral_at | exact GlobalTheory.LocCore.kappa_integral_at | (intros; apply GlobalTheory.LocCore.kappa_integral_at <;> assumption)
