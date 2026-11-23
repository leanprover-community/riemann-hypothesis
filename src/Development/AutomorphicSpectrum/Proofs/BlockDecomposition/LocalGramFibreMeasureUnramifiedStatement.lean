module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramified
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.local_gram_fibre_measure_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : HermR (Fv F v) σ n) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets → (∀ k, MeasurableSet (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k})).toReal / (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto | exact GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto <;> assumption)
