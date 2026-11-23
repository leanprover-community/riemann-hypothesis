module

public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

theorem GlobalTheory.rowSide_iota_maps_fixedColumns_onto_of_matrices : ∀ (D : D7) (μ : D.what₂.Tup) (n nV dQ d : ℕ) (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] (RowSide.sharp D).Amb μ) (E : Matrix (Fin n) (Fin n) D.what₂.LL) (V : Matrix (Fin n) (Fin nV) D.what₂.LL) (Pq : Matrix (Fin dQ) (Fin nV) D.what₂.LL) (ι : Matrix (Fin d) (Fin dQ) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (RowSide.sharp D).RR.V), (∀ x, (RowSide.sharp D).eOp μ (jA x) = jA (E.mulVec x)) → (∀ F, E.mulVec (V.mulVec F) = V.mulVec F) → Function.Surjective Pq.mulVec → Function.Surjective ι.mulVec → (∀ F, (RowSide.sharp D).iota μ (jA (V.mulVec F)) = (RowSide.sharp D).jEE (eRR (ι.mulVec (Pq.mulVec F)))) → (D.what₂.V0 μ).map (D.what₂.iota μ) = ⊤ := by
  intro D μ n nV dQ d jA E V Pq ι eRR hE hV hP hι hio
  have hi : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
    unfold RowSide.iota Rows.Data.iota
    rw [PrimeDegreeVariant.sharp_downTo]
    rfl
  have hV0 : (RowSide.sharp D).V0 μ = D.what₂.V0 μ := rfl
  rw [eq_top_iff, ← (RowSide.sharp D).jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hy⟩ := hι (eRR.symm ((RowSide.sharp D).RR.b i))
  obtain ⟨F, hF⟩ := hP y
  have h1 := hio F
  rw [hF, hy, LinearEquiv.apply_symm_apply, hi] at h1
  refine ⟨jA (V.mulVec F), ?_, h1⟩
  rw [← hV0]
  exact ⟨jA (V.mulVec F), by rw [hE, hV]⟩
