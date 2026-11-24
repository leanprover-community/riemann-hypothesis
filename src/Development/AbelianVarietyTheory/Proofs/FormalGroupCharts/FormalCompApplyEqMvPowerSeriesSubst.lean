module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ChartInv

variable {k : Type} [CommRing k] {d : ℕ}

theorem formalComp_apply_eq_mvPowerSeries_subst (φ ψ : Pt k 1 d) (i : Fin d) :
    comp1 φ ψ i = (φ i).subst (fun p : Fin 1 × Fin d => ψ p.2) := by
  unfold comp1 ev
  congr 1
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  rfl

theorem linearPart_eq_submatrix (φ : Pt k 1 d) :
    GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2) =
      (dLin φ).submatrix (Equiv.uniqueProd (Fin d) (Fin 1)) (Equiv.uniqueProd (Fin d) (Fin 1)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  obtain rfl : b = 0 := Subsingleton.elim _ _
  rfl

theorem exists_isInvPair :
    ∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) →
      IsUnit (dLin φ).det → ∃ φi : Pt k 1 d, IsInvPair φ φi := by
  intro k _ d φ h0 hdet
  have hu : ∀ p : Fin 1 × Fin d, constantCoeff ((fun p : Fin 1 × Fin d => φ p.2) p) = 0 :=
    fun p => h0 p.2
  have hA : IsUnit (GlobalTheory.FormalInv.linearPart (fun p : Fin 1 × Fin d => φ p.2)) := by
    rw [Matrix.isUnit_iff_isUnit_det, linearPart_eq_submatrix, Matrix.det_submatrix_equiv_self]
    exact hdet
  obtain ⟨v, hv, h1, h2⟩ := (GlobalTheory.FormalInv.exists_substInv_iff hu).2 hA
  have hvv : (fun p : Fin 1 × Fin d => v (0, p.2)) = v := by
    funext ⟨a, j⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  refine ⟨fun i => v (0, i), h0, fun i => hv _, ?_, ?_⟩
  · funext i
    rw [formalComp_apply_eq_mvPowerSeries_subst, hvv]
    exact h1 (0, i)
  · funext i
    rw [formalComp_apply_eq_mvPowerSeries_subst]
    exact h2 (0, i)

end GlobalTheory.ChartInv
