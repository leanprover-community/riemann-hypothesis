module

public import Formalism.RankGapBounds.TheoremALocOfLemmaA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open TensorProduct

namespace Formalism.RankGapBounds.FormsTensorLocalization

open Formalism.UG

theorem tensor_reduction_holds : TensorStep := by
  intro k _ ι _ A _ _ B l e hB y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [smul_comm]
    refine Submodule.smul_mem _ r ?_
    have h1 : l ^ (∑ i, e i) • PiTensorProduct.tprod k f =
        PiTensorProduct.tprod k (fun i => ((⟨l ^ e i • f i, hB i (f i)⟩ : B i) : A i)) := by
      show _ = PiTensorProduct.tprod k (fun i => l ^ e i • f i)
      rw [MultilinearMap.map_smul_univ]
      simp only [RingHom.id_apply, Finset.prod_pow_eq_pow_sum]
    rw [h1]
    exact ⟨PiTensorProduct.tprod k (fun i => (⟨l ^ e i • f i, hB i (f i)⟩ : B i)), by
      rw [PiTensorProduct.map_tprod]; rfl⟩
  | add x y hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy

end Formalism.RankGapBounds.FormsTensorLocalization
