module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.NormScaleHaar
open Formalism.UG GlobalTheory.AdelicU

theorem ideleModule_norm (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule F (Units.map (Algebra.norm (AF F)) t) : ℝ)) = (absE F E t : ℝ) := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  have h := NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv t)
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Eq.trans ?_ h.symm)
  · rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow, coe_nnnorm]
    rfl
  · refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl

end GlobalTheory.NormScaleHaar
