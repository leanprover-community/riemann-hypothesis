module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharApplyEqAdelicChar
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
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

theorem _root_.GlobalTheory.T.standardTraceAdelicAddChar_apply_eq_adelicChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : AF F, ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := by
  first | exact @GlobalTheory.StdCharEq.eq_adelicChar | exact GlobalTheory.StdCharEq.eq_adelicChar | (intros; apply GlobalTheory.StdCharEq.eq_adelicChar <;> assumption)
