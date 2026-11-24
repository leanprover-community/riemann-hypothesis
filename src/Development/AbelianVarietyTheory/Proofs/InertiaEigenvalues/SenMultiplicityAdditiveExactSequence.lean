module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem sen_eq_sen_pre_add_sen_push : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (N : Lats k n B.m), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, IsLat (N i) → CondC ((F.D B).γ i) (N i) → ∀ x, sen ((F.D B).γ i) (N i) x = sen ((F.D A).γ i) (F.pre A B f N i) x + sen ((F.D C).γ i) (F.push B C p N i) x := by
  intro k G _ _ l n _ _ _ R F A B C f p N hB hf hp hfi hps hex i hN hc x
  have hA : F.Obj A := F.obj_sub A B f hf hfi hB
  have hC : F.Obj C := F.obj_quot B C p hp hps hB
  exact GlobalTheory.PhiGam.SenAdd.main R ((F.D B).γ i) ((F.D A).γ i) ((F.D C).γ i) (F.map A B f i) (F.map B C p i)
    ((F.D B).γ_semi i) (F.map_inj A B f hA hB hf hfi i) (F.map_surj B C p hB hC hp hps i)
    (GlobalTheory.Models.DFun.map_exact_middle F A B C f p hB hf hp hfi hps hex i) (F.map_γ A B f hA hB hf i) (F.map_γ B C p hB hC hp i)
    (N i) hN hc x

end GlobalTheory.Models
