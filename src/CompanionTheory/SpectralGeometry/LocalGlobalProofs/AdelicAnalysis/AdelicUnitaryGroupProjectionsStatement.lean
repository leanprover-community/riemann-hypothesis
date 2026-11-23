module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjections
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

theorem _root_.GlobalTheory.T.adelic_unitary_group_projections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (pinf : HA (AF F) σ J →* HA (Ainf F) σ J) (p : ∀ v : HeightOneSpectrum (𝓞 F), HA (AF F) σ J →* HA (Fv F v) σ J), (∀ (n : ℕ) (h : HA (AF F) σ J) (X : (Fin n → Fin M → AF F ⊗[F] E)), projInf (actW (AF F) σ J h X) = actW (Ainf F) σ J (pinf h) (projInf X) ∧ ∀ v, projV v (projFin (actW (AF F) σ J h X)) = actW (Fv F v) σ J (p v h) (projV v (projFin X))) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (h : HA (AF F) σ J), ∀ᶠ v in Filter.cofinite, ∀ (n : ℕ) (X : (Fin n → Fin M → Fv F v ⊗[F] E)), actW (Fv F v) σ J (p v h) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ginf : HA (Ainf F) σ J) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), ∃ h : HA (AF F) σ J, pinf h = ginf ∧ (∀ v ∈ S, p v h = g v) ∧ ∀ v, v ∉ S → p v h = 1 := by
  exact @GlobalTheory.CompanionTheory.SW.HProj.components
