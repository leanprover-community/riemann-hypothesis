module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteIntegralLevelClosedSubgroupGL
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  first | exact @GlobalTheory.ClassFin.classFinite_integralLevel | exact GlobalTheory.ClassFin.classFinite_integralLevel | (intros; apply GlobalTheory.ClassFin.classFinite_integralLevel <;> assumption)
