module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjections
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

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_tuple_projections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), Continuous (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ Continuous (projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ (∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _)) ∧ (∀ v, IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) ∧ (∀ S, IsOpen (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ X : (Fin n → Fin M → Af F ⊗[F] E), ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v) ∧ (∀ X Y : (Fin n → Fin M → AF F ⊗[F] E), projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ (Y : (Fin n → Fin M → Ainf F ⊗[F] E)) (Z : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ᶠ v in Filter.cofinite, Z v ∈ latV b v) → ∃ X : (Fin n → Fin M → AF F ⊗[F] E), projInf X = Y ∧ ∀ v, projV v (projFin X) = Z v) ∧ Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
  exact @GlobalTheory.CompanionTheory.SW.MeasProj.proj_props
