module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE

@[expose] public section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section
namespace GlobalTheory.WeilDatumF

theorem fst_symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h : y.map (infPartF F E) = 0 ∨ z.map (infPartF F E) = 0) : fstA F (symplOF σ JS JT ξ₀ y z) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.OrientedHeis.map_trace_hO_zero (fstA F) σ (incAF F E ξ₀) (fun a b => incAF F E (JS⁻¹ a b))
    (fun c d => incAF F E (JT c d)) y z h

theorem snd_symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h : y.map (finPartF F E) = 0 ∨ z.map (finPartF F E) = 0) : sndA F (symplOF σ JS JT ξ₀ y z) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.OrientedHeis.map_trace_hO_zero (sndA F) σ (incAF F E ξ₀) (fun a b => incAF F E (JS⁻¹ a b))
    (fun c d => incAF F E (JT c d)) y z h

theorem symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h1 : y.map (infPartF F E) = 0 ∨ z.map (infPartF F E) = 0)
    (h2 : y.map (finPartF F E) = 0 ∨ z.map (finPartF F E) = 0) : symplOF σ JS JT ξ₀ y z = 0 :=
  Prod.ext (fst_symplOF_eq_zero σ JS JT ξ₀ y z h1) (snd_symplOF_eq_zero σ JS JT ξ₀ y z h2)

theorem symplOHF_fin_real_orth (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u x : WOF F E nS nT) :
      u.map (infPartF F E) = 0 → x.map (finPartF F E) = 0 → symplOHF σ JS JT ξ₀ u x = 0 ∧ symplOHF σ JS JT ξ₀ x u = 0 := by
  intro hu hx
  have e1 := symplOF_eq_zero σ JS JT ξ₀ u x (Or.inl hu) (Or.inr hx)
  have e2 := symplOF_eq_zero σ JS JT ξ₀ x u (Or.inr hu) (Or.inl hx)
  unfold symplOHF
  rw [e1, e2, mul_zero]
  exact ⟨rfl, rfl⟩

end GlobalTheory.WeilDatumF
