module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def starLoc (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : R → ℂ) (dx : Measure (Fin n → Fin M → R ⊗[F] E))
    (Φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) (b : HermR R σ n) : ℂ :=
  ∫ X, Φ X * ψR (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * gramR R σ J X))) ∂dx

def psiFin (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (y : Af F) : ℂ := ψ (pairA F 0 y)

def hermInf (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) : HermR (Ainf F) σ n :=
  ⟨(b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)), by
    intro i j
    have h := congrArg (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (b.2 i j)
    simp only [Matrix.map_apply]
    rw [← h]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp⟩

def hermFin (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) : HermR (Af F) σ n :=
  ⟨(b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)), by
    intro i j
    have h := congrArg (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (b.2 i j)
    simp only [Matrix.map_apply]
    rw [← h]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ
