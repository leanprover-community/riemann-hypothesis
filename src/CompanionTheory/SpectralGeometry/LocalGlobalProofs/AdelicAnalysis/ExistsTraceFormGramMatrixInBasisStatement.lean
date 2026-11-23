module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.exists_trace_form_gram_matrix_in_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2)) ∧ ∀ h : HA R σ J, ∀ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, (∀ p q, g p q = (Algebra.TensorProduct.basis R b).repr ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2) → gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ x : Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := by
  exact @GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord
