module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualMeasureGlobalConstRankOnly
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_selfDualMeasure_global_const_rank_only : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ), ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ (ψ : AddChar (AF F) ℂ) (J : Matrix (Fin M) (Fin M) E), IsCharAF F ψ → IsHermND σ J → ∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F)) (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μi → SdR (Ainf F) (psiInf F ψ) νi → (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) → (∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) → ∃ (ri ti : ℝ≥0) (r t : HeightOneSpectrum (𝓞 F) → ℝ≥0), μi = ri • tupMeas s.lamI 1 M ∧ νi = ti • s.nuI ∧ (∀ v, μv v = r v • tupMeas (s.lamV v) 1 M) ∧ (∀ v, νv v = t v • s.nuV v) ∧ ri ≠ 0 ∧ ti ≠ 0 ∧ (∀ v, r v ≠ 0) ∧ (∀ v, t v ≠ 0) ∧ (Function.mulSupport fun v => r v / t v).Finite ∧ ri / ti * ∏ᶠ v, r v / t v = κ := by
  first | exact @GlobalTheory.GaugeSdMain.selfDual_const | exact GlobalTheory.GaugeSdMain.selfDual_const | (intros; apply GlobalTheory.GaugeSdMain.selfDual_const <;> assumption)
