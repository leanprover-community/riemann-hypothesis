module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.muCharacter_det_level_eq_local_tame_product : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    MuLaw t u μ dtU → ∀ i, i < D.R.m → ∀ j (hj : j ≤ D.R.m) (β : (St j hj).Ch) (κ : ((St j hj).K β).lev.U) (e : SB t μ → t.X.E),
      (∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE (e P)) - 1))) →
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) i P (e P)) = 1 ∧
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) = t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P (e P))) := by
  first | exact @GlobalTheory.LevMuDet.muOf_det_lev | exact GlobalTheory.LevMuDet.muOf_det_lev | (intros; apply GlobalTheory.LevMuDet.muOf_det_lev <;> assumption)
