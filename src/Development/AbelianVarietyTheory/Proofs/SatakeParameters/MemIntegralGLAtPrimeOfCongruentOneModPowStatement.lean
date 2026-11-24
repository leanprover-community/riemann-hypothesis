module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLAtPrimeOfCongruentOneModPow
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

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.mem_integralGLAtPrime_of_congruent_one_mod_pow : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) (g : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n),
  (∀ a b, Formalism.L2.Col.IntAt P (((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) →
  (∀ a b, Formalism.L2.Col.IntAt P (((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) →
  g ∈ Formalism.L2.Col.GLint E n P ∧ ∀ w ∈ Formalism.L2.Col.stdAt E n P, ((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ • (g w - w) ∈ Formalism.L2.Col.stdAt E n P := by
  first | exact @GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong | exact GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong | (intros; apply GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong <;> assumption)
