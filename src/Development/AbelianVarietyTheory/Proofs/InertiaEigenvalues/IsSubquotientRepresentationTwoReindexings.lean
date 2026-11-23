module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
public import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
public import Mathlib.Basic.PEquiv

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem reix_eq_conj (R : Type) [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) : ∃ w : GL n R, ∀ g : GL m R, reix R φ g * w = w * reix R φ' g := by
  let e : n ≃ n := φ'.symm.trans φ
  have h1 : ((e.symm.toPEquiv.toMatrix : Matrix n n R) * e.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  have h2 : ((e.toPEquiv.toMatrix : Matrix n n R) * e.symm.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  let w : GL n R := ⟨e.symm.toPEquiv.toMatrix, e.toPEquiv.toMatrix, h1, h2⟩
  refine ⟨w, fun g => ?_⟩
  have key : (reix R φ g).val = w.val * (reix R φ' g).val * w⁻¹.val := by
    change _ = e.symm.toPEquiv.toMatrix * _ * e.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [val_reix, e]
  apply Units.ext
  rw [Units.val_mul, key, mul_assoc, Units.inv_mul, mul_one, Units.val_mul]

theorem subquotient_reix (R : Type) [CommRing R] (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n R) V) :
    IsSubquotient (σ.comp (reix R φ) : Representation ℂ (GL m R) V) (σ.comp (reix R φ') : Representation ℂ (GL m R) V) := by
  obtain ⟨w, hw⟩ := reix_eq_conj R φ φ'
  refine IsSubquotient.of_surjective ⟨σ w, fun g => ?_⟩ fun v => ⟨σ w⁻¹ v, ?_⟩
  · change σ w * σ (reix R φ' g) = σ (reix R φ g) * σ w
    rw [← map_mul, ← map_mul, hw]
  · change σ w (σ w⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end GlobalTheory.LevelType
