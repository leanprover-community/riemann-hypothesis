module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JCScalar

theorem piTensor_zj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)) (t : kˣ) (c : Fin h → ℂ), (∀ i, Zl.ScalarBy (x i) t (c i)) → ∀ (j : Fin h) (v : PiTensorProduct ℂ (fun a => (x a).2.rep.V)), piTensor (fun a => (x a).rep) (Zl.JC.zj (fun a => (x a).1) t j) v = (∏ i ∈ Finset.univ.filter (· ≤ j), c i) • v := by
  intro k _ _ _ _ h x t c hc j v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    have hf : ∀ a, (x a).rep (Zl.JC.zj (fun a => (x a).1) t j a) (f a)
        = (if a ≤ j then c a else 1) • f a := by
      intro a
      by_cases ha : a ≤ j
      · simp only [Zl.JC.zj, if_pos ha]
        exact hc a (f a)
      · simp [Zl.JC.zj, if_neg ha]
    simp only [hf]
    rw [MultilinearMap.map_smul_univ, Finset.prod_filter]
    simp only [RingHom.id_apply]
  | add a b ha hb => rw [map_add (f := _), ha, hb, smul_add]

end GlobalTheory.CompanionTheory.JCScalar
