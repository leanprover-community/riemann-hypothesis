module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.SWMeasCAll
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

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

def BaseOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J →
  ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeasC σ J T hT

def IsomC : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E),
    J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ n : ℕ, ∀ (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeasC σ J' T hT → SWMeasC σ J T hT

def ScaleC : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, ∀ (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (g : GL (Fin n) E) (T' : Matrix (Fin n) (Fin n) E)
    (hT' : ∀ a b, σ (T' b a) = T' a b), T' = cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g →
    SWMeasC σ J T' hT' → SWMeasC σ J T hT

def StepC : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ t : F, t ≠ 0 →
    PositivityTheory.PfSWUS.HMass.IsAnisoH σ (blockOne (algebraMap F E t) J) →
  ∀ (T : Matrix (Fin M) (Fin M) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 →
  ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b),
    SWMeasC σ J T hT → SWMeasC σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT'

def NotRepC : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → 1 ≤ M →
    PositivityTheory.PfSWUS.HMass.IsAnisoH σ J → ∀ t : F, t ≠ 0 →
  ∀ (T : Matrix (Fin M) (Fin M) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 →
  ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b),
    (∀ x : Fin (M + 1) → E, hE σ J x x ≠ algebraMap F E t) →
    SWMeasC σ J (blockOne (algebraMap F E t) T) hT'

def MassCAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ (T : Matrix (Fin M) (Fin M) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 →
  ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)),
    (∀ v, IsStdV v (lam v)) →
  ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ M → Measure (Fin M → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsGramFib (Fv F v) σ J M (coordW (Fv F v) b (lam v) M M) (coordHerm (Fv F v) σ b (lam v) M) (m v)) →
    (∀ v, (cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v) < ⊤) ∧
      Summable fun v => |((cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v)).toReal - 1|

def MassOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ (lam : Measure (Fv F v)), IsStdV v lam → ∀ m,
      IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 1) (coordHerm (Fv F v) σ b lam 1) m →
      ∀ s : Fv F v, Valued.v s = 1 → (cfac E v : ℝ≥0∞) * m (hermScal (Fv F v) σ s) (latV b v) = 1

end PositivityTheory.SiegelWeilFormula.Densx

end
