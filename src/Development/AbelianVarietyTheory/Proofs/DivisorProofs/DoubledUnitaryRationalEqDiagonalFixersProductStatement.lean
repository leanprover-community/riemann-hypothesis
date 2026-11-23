module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryRationalEqDiagonalFixersProduct
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.doubledUnitary_rational_eq_diagonalFixers_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b : ℕ) (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ), (∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) → JB.det ≠ 0 → ∀ (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F g₀ → ∃ (p q p' : UG (cA σ) (dbl (incM F JB))) (p₀ q₀ p₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (t s t' : GL (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ((p : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F p₀ ∧ ((q : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F q₀ ∧ ((p' : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F p₀' ∧ ((p : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin b) = diagCols (Fin b) * (t : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧ ((q : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (-1) * (s : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧ ((p' : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin b) = diagCols (Fin b) * (t' : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧ g = p * q * p' := by
  first | exact @GlobalTheory.ThetaRatGen.gen | exact GlobalTheory.ThetaRatGen.gen | (intros; apply GlobalTheory.ThetaRatGen.gen <;> assumption)
