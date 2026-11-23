module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdUpdateSelf
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

theorem mem_range_map_subtype_of_contr (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)]
    [∀ i, Module ℂ (K i)] (N : ∀ i, Submodule ℂ (K i)) (x : ⨂[ℂ] i, K i)
    (h : ∀ i (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i), (∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L) → L x ∈ N i) :
    x ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  first
  | exact @_root_.GlobalTheory.TensorContraction.mem_range_map
  | exact _root_.GlobalTheory.TensorContraction.mem_range_map
  | (apply _root_.GlobalTheory.TensorContraction.mem_range_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorContraction.mem_range_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorContraction.mem_range_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorContraction.mem_range_map ..)

end GlobalTheory.Chain.IoLift
