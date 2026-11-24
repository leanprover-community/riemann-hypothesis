module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace Formalism.MainNotions.N.K.SplitLatticeDiagonal

section Conv

variable {K : Type} [Field K] (a b n : ℕ) (hn : n = a + b)

def splitL : (Fin n → K) ≃ₗ[K] ((Fin a → K) × (Fin b → K)) where
  toFun u := (fun j => u ⟨j, by omega⟩, fun j => u ⟨a + j, by omega⟩)
  invFun p := fun k => if h : (k : ℕ) < a then p.1 ⟨k, h⟩ else p.2 ⟨k - a, by omega⟩
  map_add' u v := by ext <;> simp
  map_smul' c u := by ext <;> simp
  left_inv u := by
    funext k
    by_cases h : (k : ℕ) < a
    · simp [h]
    · simp only [h, dite_false]
      congr 1
      exact Fin.ext (by simp; omega)
  right_inv p := by
    ext j
    · simp
    · simp

theorem splitL_diag (c : K) (u : Fin n → K) (k : Fin n) :
    (splitL a b n hn).symm ((splitL a b n hn u).1, c • (splitL a b n hn u).2) k =
      (if (k : ℕ) < a then 1 else c) * u k := by
  by_cases h : (k : ℕ) < a
  · show (if h' : (k : ℕ) < a then u ⟨k, by omega⟩ else c * u ⟨a + (k - a), by omega⟩) = _
    simp [h]
  · show (if h' : (k : ℕ) < a then u ⟨k, by omega⟩ else c * u ⟨a + (k - a), by omega⟩) = _
    simp only [h, dite_false, if_false]
    congr 2
    exact Fin.ext (by simp; omega)

end Conv

theorem admG5_of_adm51_admG5 {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (hπ : π ∈ D.nd.Z i)
    (h51 : LargeLevelLemmas.adm51 i r ρ π) (h5 : EmbeddingTypes.admG5 i r ρ π) : TruncatedSeriesCountingIdentities.admG5 i r := by
  classical
  obtain ⟨S, hS⟩ := h51 hπ
  have G := h5 hπ S hS
  intro w hw
  obtain ⟨hT, ha, hb, -⟩ := G w hw
  refine ⟨fun hc x => ?_, fun hk _ hT' => ?_⟩
  · obtain ⟨hprod, e, he⟩ := ha hc x
    refine ⟨fun γ hγ => by simpa [rO, chi1] using hprod γ hγ, ?_⟩
    let sp : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)) :=
      splitL D.R.r D.R.t D.R.nV rfl
    let ψ : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i) := e.trans sp.symm
    let Pm : GL (Fin D.R.nV) (KK D.nd i) :=
      ⟨LinearMap.toMatrix' (ψ.symm : (Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] _),
        LinearMap.toMatrix' (ψ : (Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] _),
        by rw [← LinearMap.toMatrix'_comp]; simp,
        by rw [← LinearMap.toMatrix'_comp]; simp⟩
    refine ⟨Pm, fun γ hγ => ?_⟩
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    have hM : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r x) γ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        mapM (toK D.nd i) (rO D.nd i r x) γ := rfl
    have h1 : ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        LinearMap.toMatrix' (ψ : (Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] _) := rfl
    have h2 : ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        LinearMap.toMatrix' (ψ.symm : (Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] _) := rfl
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply,
      LinearMap.comp_apply, hM, h1, h2, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply, Matrix.toLin'_apply]
    have key' := he γ hγ (e.symm (sp u))
    rw [LinearEquiv.apply_symm_apply] at key'
    change sp.symm (e ((mapM (toK D.nd i) (rO D.nd i r x) γ).mulVec (e.symm (sp u)))) = _
    rw [key']
    funext k
    rw [Matrix.mulVec_diagonal]
    exact splitL_diag D.R.r D.R.t D.R.nV rfl _ u k
  · obtain ⟨P, hP, hU⟩ := hb hk
    refine ⟨P, hU, fun x γ hγ => ?_⟩
    simpa [rO, chi1, evT] using hP x γ hγ

end Formalism.MainNotions.N.K.SplitLatticeDiagonal

end
