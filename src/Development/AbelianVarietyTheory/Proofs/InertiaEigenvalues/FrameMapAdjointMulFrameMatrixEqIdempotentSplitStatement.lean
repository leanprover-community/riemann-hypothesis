module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointMulFrameMatrixEqIdempotentSplit
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

theorem _root_.GlobalTheory.T.frameMapAdjoint_mul_frameMatrix_eq_idempotent_split : ∀ (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D), cA D f = f → ∀ k : GA D W, SuppF W f k → ∀ x x' : WO V W, (∀ a b, f * x a b = f * x' a b) → (HMul.hMul (frMapAdj V W βV βW x') (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) = toEAf D f • (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) + (1 - toEAf D f) • frMapAdj V W βV βW x' := by
  first | exact @GlobalTheory.LocDisj.frMapAdj_mul_frame_eq | exact GlobalTheory.LocDisj.frMapAdj_mul_frame_eq | (intros; apply GlobalTheory.LocDisj.frMapAdj_mul_frame_eq <;> assumption)
