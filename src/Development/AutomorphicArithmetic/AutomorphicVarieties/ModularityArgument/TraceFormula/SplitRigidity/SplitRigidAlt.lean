module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.RgJS Formalism.L2.Host

namespace UpperTheory.V.Z.Tf.SR

def SplitRigid : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CG E n, π.IsUnitary →
  ∀ (J : Type) [Fintype J] (a : J → ℕ) (P : ∀ j, CG E (a j)), (∀ j, 1 ≤ a j) → (∀ j, (P j).IsUnitary) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      ∃ b : J → Multiset ℂˣ, (∀ j, (P j).HasSat w (b j)) ∧ π.HasSat w (∑ j, b j)) →
    ∃ j, (⟨a j, P j⟩ : Σ m, CG E m) = ⟨n, π⟩

def ShareBd : Prop := ForSys fun q X _ A => ∀ (x : X) (I : Set _) (M : ℕ) (z : Fin M → X) (c : _ → ℂ), 1 ≤ M → Function.Injective z →
  (∀ w, ‖c w‖ = 1) → (∀ w ∈ I, c w = 1) → (∀ (i : Fin M) w (k : ℕ), ∑ b, A (z i) w b ^ k = c w ^ (i.val * k) * ∑ a, A x w a ^ k) →
  ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    (∑' p : {p : _ × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1).re ≤ -Real.log (σ - 1) / M + C

def AbsShare : Prop := ForSys fun q X _ A => ∀ (x : X) (I : Set _) (J : Type) [Fintype J] (y : J → X) (M : ℕ) (C : ℝ),
  16 * (Fintype.card J + 1) ^ 2 ≤ M →
  (∀ σ : ℝ, 1 < σ → σ ≤ 2 → (∑' p : {p : _ × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1).re ≤ -Real.log (σ - 1) / M + C) →
  (∀ w ∉ I, ∀ k : ℕ, ∑ a, A x w a ^ k = ∑ j, ∑ b, A (y j) w b ^ k) → ∃ j, y j = x

def AntiTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ χ : HChar E,
  (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, χ.UnrAt w ∧ ‖((χ.val w : ℂˣ) : ℂ)‖ = 1 ∧ (¬ IsSplitAt w → χ.val w = 1)) ∧
  ∀ (n : ℕ) (π : CG E n), 1 ≤ n → π.IsUnitary →
    (∀ i : ℕ, (π.twist (χ ^ i)).IsUnitary) ∧ Function.Injective fun i : ℕ => π.twist (χ ^ i)

end UpperTheory.V.Z.Tf.SR

end
