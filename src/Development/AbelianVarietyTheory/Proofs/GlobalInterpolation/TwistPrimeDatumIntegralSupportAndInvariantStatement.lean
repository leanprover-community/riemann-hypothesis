module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistPrimeDatumIntegralSupportAndInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.twistPrimeDatum_integral_support_and_invariant : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n' → k₀ ≤ n → r ≤ n' + c' → r ≤ n + c → (∀ x, LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x ≠ 0 → IntHom P x) ∧ ∀ x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E), IntHom P y → LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • y) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  first | exact @GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd | exact GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd | (intros; apply GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd <;> assumption)
