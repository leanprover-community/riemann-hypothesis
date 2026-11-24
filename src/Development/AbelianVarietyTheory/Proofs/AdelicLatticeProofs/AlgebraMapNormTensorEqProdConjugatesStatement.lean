module

public import Mathlib.FieldTheory.Galois.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugates
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates : ∀ (F E K : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), algebraMap K (K ⊗[F] E) (Algebra.norm K y) = ∏ g : E ≃ₐ[F] E, Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y := by
  first | exact @GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates | exact GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates | (intros; apply GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates <;> assumption)
