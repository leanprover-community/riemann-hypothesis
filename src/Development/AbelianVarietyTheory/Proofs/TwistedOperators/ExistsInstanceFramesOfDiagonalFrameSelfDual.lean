module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
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
import Mathlib.RingTheory.PiTensorProduct
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
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem frames_of_diagonalising_frame : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  intro D V A Λ h
  obtain ⟨hlat, hdual⟩ := h
  have hspan : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    exact (Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ ⟨hlat, hdual⟩).span_eq_top
  have hf : ∀ v, IsUnit (A.fr ((Formalism.L2.Host.tauPl D).symm v)) := fun v => A.fr_unit _
  refine ⟨{ ε := fun v => A.ε ((Formalism.L2.Host.tauPl D).symm v)
            P := fun v => (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹
            unit := fun v => (Matrix.isUnit_nonsing_inv_iff).2 (hf v)
            spec := ?_
            Λ := Λ
            Λ_fg := hlat.fg
            Λ_span := hspan
            Λ_dual := ?_ }, rfl, fun τ => ?_⟩
  · intro v
    set τ := (Formalism.L2.Host.tauPl D).symm v
    have hg : V.gram.map (Formalism.IndefR.Eqv.UI.phiV D v) = (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
      rw [A.fr_gram τ]; rfl
    have hd : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hf v)
    have hdH : IsUnit ((A.fr τ)ᴴ).det := by
      rw [Matrix.det_conjTranspose]; exact hd.star
    rw [hg, Matrix.conjTranspose_nonsing_inv]
    calc ((A.fr τ)ᴴ)⁻¹ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ) * (A.fr τ)⁻¹
        = (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (A.ε τ) := by
          rw [Matrix.nonsing_inv_mul _ hdH, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · intro x
    rw [hdual x]
    refine forall₂_congr fun y _ => ?_
    unfold Formalism.UG.hform
    simp only [RingHom.mem_range, starRingEnd_apply]
  · simp

end GlobalTheory
