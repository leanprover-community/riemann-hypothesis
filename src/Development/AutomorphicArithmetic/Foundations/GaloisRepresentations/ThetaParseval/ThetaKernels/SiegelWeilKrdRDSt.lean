module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
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



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
def EpsEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    (d.A.IsHerm σ d.B d.r d.s ∧ ε = -1 ∨ d.A.IsSkew σ d.B d.r d.s ∧ ε = 1)
def FrEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  (d.A.IsHerm σ d.B d.r d.s → ∃ (fr : InfinitePlace F → GL (Fin d.m) ℂ) (sg : InfinitePlace F → ℤˣ),
    ∀ w, (1 : ℂ) • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1) ∧
  (d.A.IsSkew σ d.B d.r d.s → ∃ (fr : InfinitePlace F → GL (Fin d.m) ℂ) (sg : InfinitePlace F → ℤˣ),
    ∀ w, Complex.I • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1)
def IotaEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  ∀ (ε : ℤˣ) (ζ : ℂ), d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 →
    (ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) →
    ∃ ι : InfinitePlace F → (GR d.n →* d.G), (∀ w, Continuous (ι w)) ∧
      (∀ w y, dZ d.n ζ * d.cw w (inFrame d.b (ι w y)) = mR y * dZ d.n ζ) ∧
      (∀ w w' y, w' ≠ w → d.cw w' (inFrame d.b (ι w y)) = 1) ∧
      ∀ w y, finOne F • inFrame d.b (ι w y) = finOne F • (1 : Matrix _ _ (AE F E))
theorem rdEx_of_k (h1 : _root_.PositivityTheory.SiegelWeilFormula.Krd.EpsEx_k) (h2 : _root_.PositivityTheory.SiegelWeilFormula.Krd.FrEx_k) (h3 : _root_.PositivityTheory.SiegelWeilFormula.Krd.IotaEx_k) : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ε, hε, hs⟩ := h1 F E σ d
  rcases hs with ⟨hA, rfl⟩ | ⟨hA, rfl⟩
  · obtain ⟨fr, sg, hfr⟩ := (h2 F E σ d).1 hA
    obtain ⟨ι, hc, ha, ho, hf⟩ := h3 F E σ d (-1) 1 hε (Or.inl ⟨rfl, rfl⟩)
    exact ⟨⟨-1, 1, fr, sg, ι, hε, Or.inl ⟨rfl, rfl⟩, hfr, hc, ha, ho, hf⟩⟩
  · obtain ⟨fr, sg, hfr⟩ := (h2 F E σ d).2 hA
    obtain ⟨ι, hc, ha, ho, hf⟩ := h3 F E σ d 1 Complex.I hε (Or.inr ⟨rfl, rfl⟩)
    exact ⟨⟨1, Complex.I, fr, sg, ι, hε, Or.inr ⟨rfl, rfl⟩, hfr, hc, ha, ho, hf⟩⟩
end PositivityTheory.SiegelWeilFormula.Krd
end
end
