module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGraph
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameGraph

variable {κ : Type} {D : ℕ}

theorem linForm_projMat [Fintype κ] (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem graphIdeal_isPrime {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) [P.IsPrime] (g : (Σ k, ι₂ k) → MRing ι) : (graphIdeal P g).IsPrime :=
  RingHom.ker_isPrime _

variable {Ω : Type} [Field Ω]

theorem frame_ne_zero {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hF : IsProjFrame x e) (k : Fin (D + 1)) :
    x (e k) ≠ 0 := by
  intro h
  have hX : (X k : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker]
    simp [coneMap, h]
  rw [hF.free, Ideal.mem_bot] at hX
  exact X_ne_zero k hX

theorem genFibre_x'_ne_zero {x : Ix κ → Ω} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    [Fintype κ] {g : (Σ k, ι₂ k) → MRing (GlobalTheory κ)}
    (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := ι₂)) (graphIdeal (coordIdeal ℤ x) g)) (j : κ) (hj : x ⟨(), j⟩ ≠ 0) :
    G.x' ⟨Sum.inl (), j⟩ ≠ 0 := by
  intro h
  have h1 : (X ⟨Sum.inl (), j⟩ : MRing (Sum.elim (GlobalTheory κ) ι₂)) ∈ graphIdeal (coordIdeal ℤ x) g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    simpa using h
  rw [graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at h1
  have h2 : (X ⟨(), j⟩ : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact MvPolynomial.C_eq_zero.1 h1
  rw [coordIdeal, RingHom.mem_ker] at h2
  simp [coneMap] at h2
  exact hj h2

def fibreChart {K₂ : Type} {ι₂ : K₂ → Type} (j : κ) :
    (k : FibreBlock (Sum.inr : K₂ → Unit ⊕ K₂)) → fibreIdx (Sum.elim (GlobalTheory κ) ι₂) Sum.inr k
  | ⟨Sum.inl _, _⟩ => j
  | ⟨Sum.inr k, h⟩ => absurd ⟨k, rfl⟩ h

theorem isChart_fibreChart {x : Ix κ → Ω} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    [Fintype κ] {g : (Σ k, ι₂ k) → MRing (GlobalTheory κ)}
    (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := ι₂)) (graphIdeal (coordIdeal ℤ x) g)) (j : κ) (hj : x ⟨(), j⟩ ≠ 0) :
    IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) (fibreChart (ι₂ := ι₂) j) := by
  rintro ⟨(u | k), h⟩
  · cases u
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact genFibre_x'_ne_zero G j hj
  · exact absurd ⟨k, rfl⟩ h

end ProjFrameGraph

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
