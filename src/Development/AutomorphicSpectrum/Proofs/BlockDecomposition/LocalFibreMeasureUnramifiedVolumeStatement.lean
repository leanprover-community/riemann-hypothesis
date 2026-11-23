module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedVolume
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_fibre_measure_unramified_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ (c : (HermR (Fv F v) σ n)) (A : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), IsCompact A → IsOpen A → ∀ Tt : ℕ → Set (Fin n → Fin M → (Fv F v ⊗[F] E)), Monotone Tt → (∀ j, IsCompact (Tt j) ∧ IsOpen (Tt j) ∧ Tt j ⊆ A ∧ Tt j ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X}) → A ∩ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ j, Tt j → ∀ ε : ℕ → ℝ≥0, Filter.Tendsto ε Filter.atTop (nhds 0) → (∀ (j : ℕ) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) ((A \ Tt j) ∩ gramIn (Fv F v) σ J Y) ≤ ε j * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y) → mv c A ≠ ⊤ ∧ ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : (HermR (Fv F v) σ n)) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : (HermR (Fv F v) σ n))).smallSets → (∀ k, MeasurableSet (A ∩ gramNear (Fv F v) σ J c (U k)) ∧ (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (A ∩ gramNear (Fv F v) σ J c (U k)) ≠ ⊤) ∧ Filter.Tendsto (fun k => ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (A ∩ gramNear (Fv F v) σ J c (U k))).toReal / ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  exact @GlobalTheory.CompanionTheory.AvgFree.Lim.avg_tendsto_free
