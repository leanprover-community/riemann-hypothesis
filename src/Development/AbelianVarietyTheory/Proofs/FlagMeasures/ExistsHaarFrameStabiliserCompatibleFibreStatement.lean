module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarFrameStabiliserCompatibleFibre
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_haar_frameStabiliser_compatible_fibre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure ∧ ((fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT)) {y | ¬ ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y} = 0 ∧ ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∀ s : (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ y, (∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y) → s y • ratTup (Fv F v) (F0 P) = y) → ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Fv F v) σ J)) ∂μ0 ∂(fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT))) := by
  first | exact @GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser | exact GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser | (intros; apply GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser <;> assumption)
