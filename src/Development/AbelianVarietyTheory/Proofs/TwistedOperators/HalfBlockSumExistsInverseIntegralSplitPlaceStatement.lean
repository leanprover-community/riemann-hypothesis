module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumExistsInverseIntegralSplitPlace
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
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b : GL (Fin d) (Fv F v)),
  (∀ a : AF F, π (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) →
  ∀ (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F)),
  G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) →
  ∀ X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  IsUnit (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂ +
    X * (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)).det →
  ∀ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), Y.map π = (b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) * ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∃ N : Matrix (Fin d) (Fin d) (Fv F v), N * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))).map π = 1 ∧ (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * N * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.Twist.halfBlockSum_inv_conj_integral | exact GlobalTheory.Twist.halfBlockSum_inv_conj_integral | (intros; apply GlobalTheory.Twist.halfBlockSum_inv_conj_integral <;> assumption)
