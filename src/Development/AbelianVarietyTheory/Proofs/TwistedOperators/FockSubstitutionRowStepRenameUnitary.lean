module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem fockSubAll_rename_unitary {D : D7} {m n a b : ℕ} (ha : n = a) (hb : m = b)
    (u : UG D.what₂.Tau a) (v : UG D.what₂.Tau b) (Q : MvPolynomial (FVar D m n) ℂ) :
    MvPolynomial.rename (fun x : FVar D m n => (x.1, Fin.cast hb x.2.1, Fin.cast ha x.2.2))
      (fockSubAll (fun _ => n) (fun _ => m)
        (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast ha) (Fin.cast ha))
        (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast hb) (Fin.cast hb)) Q) =
      linSub (homMat a b (u, v))
        (MvPolynomial.rename (fun x : FVar D m n => (x.1, Fin.cast hb x.2.1, Fin.cast ha x.2.2)) Q) := by
  subst ha hb
  have hinv : ∀ τ, ((u τ : Matrix (Fin n) (Fin n) ℂ))⁻¹ = star (u τ : Matrix (Fin n) (Fin n) ℂ) :=
    fun τ => Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 (u τ).2)
  have hc : ∀ k : ℕ, (Fin.cast (rfl : k = k)) = id := fun k => by funext i; rfl
  rw [hc, hc]
  have hid : (fun x : FVar D m n => (x.1, (id x.2.1 : Fin m), (id x.2.2 : Fin n))) = id := rfl
  rw [hid, MvPolynomial.rename_id, AlgHom.id_apply, AlgHom.id_apply]
  have hs : ∀ k (M : Matrix (Fin k) (Fin k) ℂ), M.submatrix id id = M := fun _ _ => rfl
  simp only [hs]
  show _ = (MvPolynomial.aeval (R := ℂ) fun p : D.what₂.Tau × (Fin m × Fin n) => ∑ j, MvPolynomial.C ((homMat n m (u, v)) p.1 j p.2) *
    (MvPolynomial.X (p.1, j) : MvPolynomial (D.what₂.Tau × (Fin m × Fin n)) ℂ)) Q
  refine DFunLike.congr_fun ?_ Q
  refine MvPolynomial.algHom_ext fun y => ?_
  obtain ⟨τ, p, q⟩ := y
  simp only [fockSubAll, MvPolynomial.aeval_X, hinv, homMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Fin.is_lt, iff_self, if_true, Matrix.transpose_apply, Matrix.star_apply]

theorem trCol_fockSubAll_unitary : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR j)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR (j + 1)))
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank),
    GlobalTheory.RowReal.trCol G j (GlobalTheory.RowReal.fockSubAll (fun _ => (G.V (.top j)).rank) (fun _ => (G.V (.top (j + 1))).rank)
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le)))
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trCol G j Q) := by
  intro D T L sc G j u v Q
  exact fockSubAll_rename_unitary _ _ u v Q

end GlobalTheory.RowReal
