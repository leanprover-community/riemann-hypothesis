module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphTensorProductMeasure
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

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.coordinate_homeomorph_tensor_product_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ n : ℕ, ∃ e : (R × (Fin n → R ⊗[F] E) × HermR R σ n) ≃ₜ HermR R σ (n + 1), (∀ p, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 = p.1 ⊗ₜ[F] (1 : E)) ∧ (∀ p j, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 (Fin.succ j) = p.2.1 j) ∧ (∀ p i j, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (Fin.succ i) (Fin.succ j) = (p.2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j) ∧ (lam.prod ((Measure.pi fun _ => coordK R b lam).prod (coordHerm R σ b lam n))).map e = coordHerm R σ b lam (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermSplit.herm_split | exact GlobalTheory.CompanionTheory.SW.HermSplit.herm_split | (intros; apply GlobalTheory.CompanionTheory.SW.HermSplit.herm_split <;> assumption)
