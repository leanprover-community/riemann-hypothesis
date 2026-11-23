module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpace
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

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.exists_hyperbolicPlane_split_hermitianLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  first | exact @GlobalTheory.KTowerPlane.exists_hyperbolic_split | exact GlobalTheory.KTowerPlane.exists_hyperbolic_split | (intros; apply GlobalTheory.KTowerPlane.exists_hyperbolic_split <;> assumption)
