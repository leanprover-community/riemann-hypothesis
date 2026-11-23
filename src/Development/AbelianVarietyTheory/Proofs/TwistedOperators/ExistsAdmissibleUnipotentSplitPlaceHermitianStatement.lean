module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlaceHermitian
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

theorem _root_.GlobalTheory.T.exists_admissible_unipotent_at_split_place : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  first | exact @GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian | exact GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian | (intros; apply GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian <;> assumption)
