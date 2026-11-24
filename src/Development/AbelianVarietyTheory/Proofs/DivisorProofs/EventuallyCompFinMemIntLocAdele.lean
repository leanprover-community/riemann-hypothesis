module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_compFin_mem_intLoc_adele (z : AE F E) :
    ∀ᶠ v : Pl F in cofinite, compFin F E v z ∈ intLoc F E v := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v => by rw [map_zero]; exact zero_mem _
  | add y z hy hz =>
    filter_upwards [hy, hz] with v h h'
    rw [map_add]
    exact add_mem h h'
  | tmul a e =>
    filter_upwards [a.2.2, eventually_one_tmul_mem_intLoc (F := F) e] with v h h'
    have := mul_mem (tmul_mem_intLoc (a := evFin F v a) h (1 : 𝓞 E)) h'
    change evFin F v a ⊗ₜ[F] e ∈ _
    simpa using this


omit [NumberField E] in
theorem compFin_unitAt_self (v : Pl F) (l : (AE F E)ˣ) :
    compFin F E v (unitAt E v l : AE F E) = compFin F E v l := by
  change compFin F E v (eFin v • (l : AE F E) + (1 - eFin v) • 1) = _
  have h : evFin F v (eFin v) = 1 := GlobalTheory.LatVac.evFin_liftV v 1
  rw [map_add (f := _), compFin_smul, compFin_smul, map_sub, map_one, h, sub_self, zero_smul, one_smul, add_zero]

theorem eventually_unitAt_mem_unitsAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (l : (AE F E)ˣ) : ∀ᶠ v in cofinite, unitAt E v l ∈ unitsAt E v := by
  filter_upwards [eventually_compFin_mem_intLoc_adele (l : AE F E),
    eventually_compFin_mem_intLoc_adele ((l⁻¹ : (AE F E)ˣ) : AE F E)] with v h h'
  refine mem_unitsAt.2 ⟨unitAt_mem v l, ?_, ?_⟩
  · rwa [compFin_unitAt_self]
  · rwa [← map_inv, compFin_unitAt_self]

end GlobalTheory.ThK.ConeEuler

end
