module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SetIntegralAddRight
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrIntRhoInv

@[expose] public section



section
open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.SplitLagrF
section aux
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end aux
theorem lagrInt_heis_dC_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f → ∀ v : WOF F E nS nT,
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT)
                     (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC F E nT * v) f) =
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ ν 𝓕 _ h𝓕 f hf u
  set g : WOF F E nS nT → ℂ := fun v => f (dC F E nT * v) with hg
  have h1 : ∀ v : WOF F E nS nT, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC F E nT * u) f
      (dC F E nT * v) = g (v + u) := by
    intro v
    simp only [hg, heisOF]
    rw [symplOHF_dC, AddChar.map_zero_eq_one, one_mul, Matrix.mul_add]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    show f (dC F E nT * ((ratWF γ : WOF F E nS nT) + v)) = f (dC F E nT * v)
    have hq := hf.quasi (GlobalTheory.LagrThetaInv.dC E nT * γ) (dC F E nT * v)
    rw [← dC_mul_ratWF, symplOHF_dC, neg_zero, AddChar.map_zero_eq_one, one_mul] at hq
    rw [Matrix.mul_add, hq]
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [h1]
  exact setIntegral_add_right ν 𝓕 h𝓕 g h2 u
end GlobalTheory.SplitLagrF
end
end
