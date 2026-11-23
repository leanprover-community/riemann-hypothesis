module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
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

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem isNm_ue_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ h : HA (AF F) σ J, IsNm σ (ue (AF F) σ J h) 1 := by
  intro F E _ _ _ _ _ σ _ J hJ h
  have hg : cT (sigR (AF F) σ) ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) * JR (AF F) J *
      ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) = JR (AF F) J := h.2
  have hx : ((ue (AF F) σ J h : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) 0 0 := by
    simp only [ue, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  have he := congrFun (congrFun hg 0) 0
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, cT, JR, Matrix.transpose_apply,
    Matrix.map_apply, Fin.default_eq_zero, Fin.isValue] at he
  have hj : J 0 0 ≠ 0 := by
    have := hJ.2
    rwa [Matrix.det_fin_one] at this
  have hu : IsUnit (inclR (F := F) (AF F) (J 0 0)) := (IsUnit.mk0 _ hj).map (inclR (F := F) (AF F))
  show ((1 : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E) = sigR (AF F) σ _ * _
  rw [hx, Units.val_one, ← Algebra.TensorProduct.one_def]
  apply hu.mul_left_cancel
  rw [mul_one]
  exact he.symm.trans (by ring)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
