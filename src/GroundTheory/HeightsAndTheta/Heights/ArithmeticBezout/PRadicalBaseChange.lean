module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsBaseChange
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ReducedTensorPerfect
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open TensorProduct

noncomputable section

theorem RadicalBaseChange.proof : RadicalBaseChange.Statement := by
  intro K L _ _ _ σ ι I hI
  let : Algebra K L := σ.toAlgebra
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have h1 : IsReduced (L ⊗[K] (MvPolynomial ι K ⧸ I)) :=
    isReduced_tensorProduct_of_perfectField K L _
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := K) L (MvPolynomial ι K) L I
  let e2 : L ⊗[K] MvPolynomial ι K ≃ₐ[L] MvPolynomial ι L := MvPolynomial.algebraTensorAlgEquiv K L
  have hmap : I.map (MvPolynomial.map σ) =
      (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L))).map
        (e2 : L ⊗[K] MvPolynomial ι K →+* MvPolynomial ι L) := by
    rw [← Ideal.map_coe (Algebra.TensorProduct.includeRight (R := K) (A := L)), Ideal.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul, RingHom.algebraMap_toAlgebra]
    · intro i
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let e3 := Ideal.quotientEquivAlg (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
    (I.map (MvPolynomial.map σ)) e2 hmap
  exact isReduced_of_injective (e1.toRingEquiv.trans e3.toRingEquiv).symm (RingEquiv.injective _)

end

end GroundTheory.Heights₂.Heights
