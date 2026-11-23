module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCornerSeparableCharpolyOfIsInternalStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepresentationDensityOfIsInternalConstituentStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem exists_mem_span_corner_separable {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ}
    (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (h : AbsIrrDistinct (matRep σ)) (hba : b * a = 1)
    (hab : a * b ∈ Submodule.span K (Set.range σ)) :
    ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  obtain ⟨ι, _, _, Vs, hs, hint, -, hspan, hdist⟩ := h
  have hstab : ∀ j, ∀ M ∈ Submodule.span K (Set.range σ), ∀ v ∈ Vs j, M.mulVec v ∈ Vs j := by
    intro j M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hs j g v hv
    | zero => intro v _; simp
    | add x y _ _ hx hy =>
      intro v hv
      rw [Matrix.add_mulVec]
      exact (Vs j).add_mem (hx v hv) (hy v hv)
    | smul c x _ hx =>
      intro v hv
      rw [show (c • x).mulVec v = c • x.mulVec v by
        ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]]
      exact (Vs j).smul_mem c (hx v hv)
  obtain ⟨m, hm, hsep⟩ := GlobalTheory.T.exists_corner_separable_charpoly_of_isInternal ι Vs a b hint hba (fun j => hstab j _ hab)
  refine ⟨m, ?_, hsep⟩
  have hlin := GlobalTheory.T.span_representation_density_of_isInternal_constituents (matRep σ) ι Vs hs hint hspan hdist (Matrix.toLin' m)
    (fun j v hv => by simpa [Matrix.toLin'_apply] using hm j v hv)
  have hfun : (⇑(matRep σ)) = ⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) ∘ ⇑σ := rfl
  rw [hfun, Set.range_comp] at hlin
  have hle : Submodule.span K (⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) '' Set.range ⇑σ) ≤
      (Submodule.span K (Set.range σ)).map
        (Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨M, hM, rfl⟩
    exact ⟨M, Submodule.subset_span hM, rfl⟩
  obtain ⟨y, hy, hye⟩ := hle hlin
  have hym : y = m := Matrix.toLin'.injective hye
  rwa [hym] at hy

end GlobalTheory.SpanRing
