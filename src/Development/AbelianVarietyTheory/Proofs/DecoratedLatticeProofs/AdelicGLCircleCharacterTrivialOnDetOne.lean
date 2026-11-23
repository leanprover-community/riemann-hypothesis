module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StableRangeOneAdelesCmFieldStatement
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
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem glChar_transvection {R : Type} [CommRing R] (h2 : IsUnit (2 : R)) {n : ℕ}
    (α : GL (Fin n) R →* Circle) (i j : Fin n) (hij : i ≠ j) (t : R)
    (u : GL (Fin n) R) (hu : u.1 = Matrix.transvection i j t) : α u = 1 := by
  obtain ⟨w, hw⟩ := h2
  let f : Fin n → R := Function.update 1 i 2
  let g : Fin n → R := Function.update 1 i (↑w⁻¹ : R)
  have hfg : ∀ k, f k * g k = 1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [f, g, ← hw]
    · simp [f, g, hk]
  have hgf : ∀ k, g k * f k = 1 := fun k => by rw [mul_comm]; exact hfg k
  let d : GL (Fin n) R :=
    ⟨Matrix.diagonal f, Matrix.diagonal g,
      by rw [Matrix.diagonal_mul_diagonal]; simp [hfg],
      by rw [Matrix.diagonal_mul_diagonal]; simp [hgf]⟩
  have hcomm : d * u = u * u * d := by
    apply Units.ext
    have hfi : f i = 2 := by simp [f]
    have hfj : f j = 1 := by simp [f, hij.symm]
    change Matrix.diagonal f * u.1 = u.1 * u.1 * Matrix.diagonal f
    rw [hu, Matrix.transvection_mul_transvection_same _ _ hij]
    ext a b
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    clear_value f g d
    clear hfg hgf
    split_ifs <;> subst_vars <;> simp_all <;> ring
  have h := congrArg α hcomm
  simp only [map_mul] at h
  have h' : α d * α u = α d * (α u * α u) := by rw [h]; exact mul_comm _ _ |>.trans (by rfl)
  have h'' := mul_left_cancel h'
  exact (mul_eq_left.mp h''.symm)

theorem glChar_eq_one_of_det_eq_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle),
    Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  intro D n α _ a ha
  have h2 : IsUnit (2 : AE D) := by
    have h := (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map (algebraMap D.host.F (AE D))
    rwa [map_ofNat] at h
  have := GlobalTheory.T.special_linear_generated_by_transvections (AE D) (GlobalTheory.T.stableRangeOne_adeles_cmField D) n α.ker
    (fun i j hij t u hu => MonoidHom.mem_ker.mpr (glChar_transvection h2 α i j hij t u hu)) a ha
  exact MonoidHom.mem_ker.mp this

end GlobalTheory
