module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAtSplitPlaceLocalBases
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.unitary_at_splitPlace_localBases : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z, π₁ (cA σ z) = π₂ z) → ∀ g : GlobalTheory.DblVac.UD σ W,
  (Matrix.fromBlocks (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₁.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₂.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₁.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₂.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))))ᵀ *
    Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) *
    (Matrix.fromBlocks (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₁.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₂.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₁.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₂.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) =
  Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) := by
  first | exact @GlobalTheory.UnitFv.unitary_split | exact GlobalTheory.UnitFv.unitary_split | (intros; apply GlobalTheory.UnitFv.unitary_split <;> assumption)
