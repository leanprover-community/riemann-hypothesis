module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianCorrectionIsUnitAntidiagCorne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_skewHermitian_correction_isUnit_antidiag_corner : ∀ (O : Type) [CommRing O] (c : O →+* O), IsUnit (2 : O) →
    (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
      ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
        gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
        ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) →
    ∀ (n : ℕ) (JL : Matrix (Fin n) (Fin n) O) (G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    (∀ i j, c (JL j i) = JL i j) → IsUnit JL.det → G * G' = 1 →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) →
    ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * JL + JL * Z.map c = 0 ∧
      IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * Z).det := by
  first | exact @GlobalTheory.HermBlockChange.exists_unit_lower_block | exact GlobalTheory.HermBlockChange.exists_unit_lower_block | (intros; apply GlobalTheory.HermBlockChange.exists_unit_lower_block <;> assumption)
