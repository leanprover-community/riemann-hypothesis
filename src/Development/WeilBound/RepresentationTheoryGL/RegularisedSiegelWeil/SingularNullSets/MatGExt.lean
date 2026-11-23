module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeylStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

open GlobalTheory.CompanionTheory.JacobiMaps GlobalTheory.StdUnn.Model

namespace PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

variable {D : D7} {n : ℕ}

theorem matG_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem matG_ext {g h : G D n} (e : mat g = mat h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem matG_inv {g : G D n} {M : Mx D (n + n) (n + n)} (h : mat g * M = 1) : mat g⁻¹ = M := by
  have e : mat g⁻¹ * mat g = 1 := by
    rw [← matG_mul, inv_mul_cancel]; rfl
  calc mat g⁻¹ = mat g⁻¹ * (mat g * M) := by rw [h, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]

theorem adjM_mul {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) : adj (x * y) = adj y * adj x := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adjM_one {a : ℕ} : adj (1 : Mx D a a) = 1 := by
  simp only [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

namespace PositivityTheory.Rg.Rsw.L


open UnitaryGroupMatrix in
theorem geng : GenG := by
  intro D n A _ h1 hA
  let S : Subgroup (G D n) :=
    { carrier := {g | (∀ x ∈ A, g * x ∈ A) ∧ ∀ x ∈ A, g⁻¹ * x ∈ A}
      mul_mem' := fun {g h} hg hh =>
        ⟨fun x hx => by rw [mul_assoc]; exact hg.1 _ (hh.1 x hx),
         fun x hx => by rw [mul_inv_rev, mul_assoc]; exact hh.2 _ (hg.2 x hx)⟩
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      inv_mem' := fun {g} hg => ⟨hg.2, fun x hx => by rw [inv_inv]; exact hg.1 x hx⟩ }
  have hS : S = ⊤ := by
    refine GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl D n S ?_ ?_ ?_
    · intro g a hg
      refine ⟨hA g (Or.inr (Or.inl ⟨a, hg⟩)), hA g⁻¹ (Or.inr (Or.inl ⟨a⁻¹, ?_⟩))⟩
      rw [inv_inv]
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp only [mul_zero, zero_mul, add_zero, zero_add]
      rw [← adjM_mul, a.mul_inv, adjM_one, block_matrix_one]
    · intro g b hg
      refine ⟨hA g (Or.inl ⟨b, hg⟩), hA g⁻¹ (Or.inl ⟨-b, ?_⟩)⟩
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp [block_matrix_one]
    · intro g hg
      have e : g⁻¹ = g * (g * g) := by
        apply matG_ext
        rw [matG_inv (M := blk4 0 (-1) 1 0), matG_mul, matG_mul, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
        · simp
        · rw [hg, submatrix_fromBlocks_mul]; simp [block_matrix_one]
      have hw := hA g (Or.inr (Or.inr hg))
      refine ⟨hw, fun x hx => ?_⟩
      rw [e, mul_assoc, mul_assoc]
      exact hw _ (hw _ (hw x hx))
  ext g
  simp only [Set.mem_univ, iff_true]
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  simpa using hg.1 1 h1

end PositivityTheory.Rg.Rsw.L

end
