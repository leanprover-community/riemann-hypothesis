module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceLocalLatticeBasisHyperbolicPlane
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

@[expose] public section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

theorem _root_.GlobalTheory.T.exists_splitPlace_localLatticeBasis_hyperbolicPlane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v) (n₁ : ℕ) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E) (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ),
    i₀ < i₁ → i₁ < n₁ + 2 →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    (∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0) →
    PrimAt (GlobalTheory.AdelicU.splitPrime τ) L x → PrimAt (GlobalTheory.AdelicU.splitPrime τ) L y → GlobalTheory.AdelicU.IsSplitBasis τ (lowLat ι L) β₁ →
    ∃ β : GL (Fin (n₁ + 2)) (Fv F v), GlobalTheory.AdelicU.IsSplitBasis τ L β ∧ ∀ i : Fin (n₁ + 2),
      (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧ (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧
      ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j := by
  first | exact @GlobalTheory.PlaneSkewBasis.exists_isSplitBasis_plane_of_indep | exact GlobalTheory.PlaneSkewBasis.exists_isSplitBasis_plane_of_indep | (intros; apply GlobalTheory.PlaneSkewBasis.exists_isSplitBasis_plane_of_indep <;> assumption)
