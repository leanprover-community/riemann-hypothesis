module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarMeasureGramGL2ActionTensor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.haar_measure_gram_GL2_action_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (lam : Measure (R ⊗[F] E)) (ν : Measure R) (γ : GL (Fin 2) E), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ Φ : (R × (R ⊗[F] E) × R) ≃ₜ (R × (R ⊗[F] E) × R), (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ X : (Fin 2 → Fin M → R ⊗[F] E), gram3 R σ J (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R)) X) = Φ (gram3 R σ J X)) ∧ ν.prod (lam.prod ν) = (modu (R ⊗[F] E) (inclR R (γ : Matrix (Fin 2) (Fin 2) E).det) ^ 2) • (ν.prod (lam.prod ν)).map Φ := by
  first | exact @GlobalTheory.GaugeEx.HermMod.haar_measure_gram_GL2_action | exact GlobalTheory.GaugeEx.HermMod.haar_measure_gram_GL2_action | (intros; apply GlobalTheory.GaugeEx.HermMod.haar_measure_gram_GL2_action <;> assumption)
