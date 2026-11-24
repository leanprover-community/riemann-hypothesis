module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Filter GlobalTheory.LFun

section Defs

variable {K : Type} [Field K] [NumberField K]

def liftFam (c : Fam K) (m x : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) : Fam K :=
  twist c (x * m⁻¹) + segFam x t

def IsZetaCont (T : Set (HeightOneSpectrum (𝓞 K))) (Z : ℂ → ℂ) : Prop :=
  MeromorphicOn Z Set.univ ∧ ∀ s : ℂ, 1 < s.re → Z s = zetaOff T s

def HasSimplePole (Λ : ℂ → ℂ) (s₀ : ℂ) : Prop :=
  MeromorphicAt Λ s₀ ∧ meromorphicOrderAt Λ s₀ = ((-1 : ℤ) : WithTop ℤ) ∧
    ∃ ρ : ℂ, ρ ≠ 0 ∧ Tendsto (fun s => (s - s₀) * Λ s) (𝓝[≠] s₀) (𝓝 ρ)

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rhs (S : Set (HeightOneSpectrum (𝓞 F))) (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ)
    (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  LSTw S c m s * ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i)

def Hyp (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) : Prop :=
  S.Finite ∧ r + 5 ≤ t ∧
    ∀ w ∉ above E S, (c w).card = r ∧
      (∀ b ∈ c w, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧
      ‖(m w : ℂ)‖ = 1 ∧ ‖(x w : ℂ)‖ = 1 ∧ P w = liftFam c m x t w

def Concl (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) :
    Prop :=
  (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re →
    Converges (above E S) (twist P x⁻¹) s ∧
      (∀ i < t, Converges (above E S) (fun _ => {1}) (s + ((t : ℂ) - 1) / 2 - i)) ∧
      LSTw S P x s = rhs S c m t (zetaOff (above E S)) s) ∧
  ((∀ s : ℂ, ((r : ℝ) + 1) / 2 < s.re → Converges (above E S) (twist c m⁻¹) s ∧ LSTw S c m s ≠ 0) ∧
    DifferentiableOn ℂ (LSTw S c m) {s | ((r : ℝ) + 1) / 2 < s.re}) ∧
  (∃ Z, IsZetaCont (above E S) Z) ∧
  ∀ Z, IsZetaCont (above E S) Z →
    MeromorphicOn (rhs S c m t Z) {s | ((r : ℝ) + 1) / 2 < s.re} ∧
      ((r : ℝ) + 1) / 2 < ((1 + (t : ℂ)) / 2).re ∧
      (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re → rhs S c m t Z s = LSTw S P x s) ∧
      HasSimplePole (rhs S c m t Z) ((1 + (t : ℂ)) / 2)

def SimplePole : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ),
    Hyp S r t c P m x → Concl S r t c P m x

section Rep

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU

end Rep

theorem twist_liftFam (c : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ) :
    twist (liftFam c m x t) x⁻¹ = twist c m⁻¹ + segFam 1 t := by
  rw [liftFam, twist_add, twist_twist, twist_segFam, inv_mul_cancel_left, inv_mul_cancel]

end GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

end
