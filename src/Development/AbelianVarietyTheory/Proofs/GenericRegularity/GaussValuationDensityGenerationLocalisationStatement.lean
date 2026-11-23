module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GaussValuationDensityGenerationLocalisation
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
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

theorem _root_.GlobalTheory.T.gauss_valuation_density_generation_localisation : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (ψ : Kp X la N →+* U), (∀ a : Op X la N, v (ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ a)) ≤ 1) → v (ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ (unifO X la N))) < 1 → (∀ (f : B.KO →+* U), (∀ a, f a = ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) → ∀ p : MvPolynomial (Idx D j N) B.KO, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) → v (MvPolynomial.eval₂ f (fun q => ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N q))) p) = 1) ∧ (∀ (c : X.Ol la) (γ : WithZero (Multiplicative ℤ)), γ ≠ 0 → ∃ a : B.KO, v (ψ (algebraMap (X.Ol la) (Kp X la N) c) - ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) < γ) ∧ ∀ S : Subfield U, (∀ c : X.Ol la, ψ (algebraMap (X.Ol la) (Kp X la N) c) ∈ S) → (∀ q, ψ (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N q)) ∈ S) → ∀ c : Kp X la N, ψ c ∈ S := by
  first | exact @GlobalTheory.GaussVal.gauss_dense_gen | exact GlobalTheory.GaussVal.gauss_dense_gen | (intros; apply GlobalTheory.GaussVal.gauss_dense_gen <;> assumption)
