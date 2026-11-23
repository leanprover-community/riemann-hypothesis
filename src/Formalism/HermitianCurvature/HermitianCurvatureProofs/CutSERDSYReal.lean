module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem spectral_Y_real : RDSYReal := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _
  classical
  let T : Finset ℝ := Finset.univ.biUnion fun τ : M.Ty P =>
    (Finset.Icc 1 (P.k - 1)).image fun i => -(M.rho P τ i)
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (T ∪ T.image (fun t => t - 1) ∪ T.image (fun t => t + 1))
  have hinv := hD.2.2.2.2.2.1
  have good : ∀ t : ℝ, t ∉ T → (t : ℂ) ∈ st.inv := by
    intro t ht
    rw [hinv]
    intro τ
    unfold M.xC
    rw [Finset.prod_ne_zero_iff]
    intro i hi h0
    apply ht
    refine Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, Finset.mem_image.2 ⟨i, hi, ?_⟩⟩
    have h1 : ((t + M.rho P τ i : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have h2 := Complex.ofReal_eq_zero.1 h1
    linarith
  refine ⟨(y : ℂ), by rw [Complex.star_def, Complex.conj_ofReal], ?_,
    good y fun h => hy (Finset.mem_union_left _ (Finset.mem_union_left _ h)), ?_⟩
  · have e : ((y : ℂ) - 1) = ((y - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    exact good (y - 1) fun h => hy (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y - 1, h, by ring⟩))
  · have e : ((y : ℂ) + 1) = ((y + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    exact good (y + 1) fun h => hy (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨y + 1, h, by ring⟩)))

end Formalism.FourierDecayAlt.P.CutSE
