module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  apply _root_.GlobalTheory.SplitAdeleTrace.liftV_one_mul_comp <;> assumption

omit [NumberField E] in
theorem smul_eq_map (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • a =
      TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

theorem eq_zero_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (ha : GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = a) (h1 : piW t a = 0) (h2 : piW (t.comp σ) a = 0) : a = 0 := by
  have h0 : compFin F E v a = 0 :=
    split_ext h t (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  rw [← ha, smul_eq_map, h0, map_zero]

omit [NumberField E] in
theorem one_sub_smul {m n : Type} {v : Pl (F := F)} {u : Matrix m n (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evFin F v) u) :
    (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • u = 0 :=
  hu _ (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])

end GlobalTheory.SwapAtPlace
