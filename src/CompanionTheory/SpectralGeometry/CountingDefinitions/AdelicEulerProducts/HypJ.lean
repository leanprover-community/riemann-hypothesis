module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal

def hypJ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K :=
  Matrix.of (Fin.cons (Fin.cons 0 (Fin.cons 1 (fun _ => 0)))
    (Fin.cons (Fin.cons 1 (Fin.cons 0 (fun _ => 0))) (fun i => Fin.cons 0 (Fin.cons 0 (A i)))))

def eOne (K : Type) [Zero K] [One K] (M : ℕ) : Fin 1 → Fin (M + 1) → K :=
  fun _ => Fin.cons 1 (fun _ => 0)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def box {d M n : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) (r : ℝ) : Set (Fin n → Fin M → AF F ⊗[F] E) :=
  {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r}

def IsFlow (τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ) : Prop :=
  Continuous τ ∧ ∃ θ : ℝ →+* Ainf F, Continuous θ ∧
    ∀ x : ℝ, ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      pairA F (θ (Real.exp x)) 1 ⊗ₜ[F] (1 : E)

def cntI (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin n → Fin M → E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, ∑' X : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ

end GlobalTheory.CompanionTheory.SW
