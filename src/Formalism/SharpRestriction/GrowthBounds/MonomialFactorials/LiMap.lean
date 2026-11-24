module

public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

@[expose] public section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

theorem li_map {k L : Type*} [Field k] [Field L] (ι : k →+* L) {σ κ : Type*} (f : κ → MvPolynomial σ k)
    (hf : LinearIndependent k f) : LinearIndependent L (fun i => MvPolynomial.map ι (f i)) := by
  classical
  letI := ι.toAlgebra
  have hs : LinearIndepOn k id (Set.range f) := (linearIndepOn_id_range_iff hf.injective).2 hf
  let b := Module.Basis.extend hs
  let B := (Algebra.TensorProduct.basis L b).map
    (MvPolynomial.algebraTensorAlgEquiv k L).toLinearEquiv
  have hB : ∀ x, B x = MvPolynomial.map ι (x : MvPolynomial σ k) := by
    intro x
    simp only [B, b, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
      Module.Basis.coe_extend, AlgEquiv.toLinearEquiv_apply,
      MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rfl
  have hsub : Set.range f ⊆ hs.extend (Set.subset_univ _) := hs.subset_extend _
  have hinj : Function.Injective
      (fun i => (⟨f i, hsub (Set.mem_range_self i)⟩ : hs.extend (Set.subset_univ _))) := by
    intro i j hij
    exact hf.injective (congrArg Subtype.val hij)
  have := B.linearIndependent.comp _ hinj
  convert this using 1
  all_goals first
    | rfl
    | (funext i; simp only [Function.comp_apply, hB])

end Formalism.MainNotions.G.SymmetricFormBlocks
