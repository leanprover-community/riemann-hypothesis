module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem norm_dict : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (w : Fin V.rank → D.host.E), ∏ v, Real.sqrt (∑ i, ‖(Formalism.MainNotions.S.uMat (x.1 v)⁻¹ *ᵥ (((Formalism.IndefR.Eqv.UI.instV fr).P v)⁻¹ *ᵥ fun j => (Formalism.IndefR.Eqv.UI.instV fr).φ v (w j))) i‖ ^ 2) = ∏ τ, nrm θ A (Formalism.IndefR.Eqv.UI.brg fr x) τ w := by
  intro D θ hθ V A fr hP x w
  symm
  refine Fintype.prod_equiv (Formalism.L2.Host.tauPl D) _ _ fun τ => ?_
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  unfold nrm eu GlobalTheory.SepPer.cmp
  rw [← map_inv (Formalism.IndefR.Eqv.UI.brg fr) x, (GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr).2.1 x⁻¹ τ _ rfl, hP τ]
  have key : ∀ (U Q : Matrix (Fin V.rank) (Fin V.rank) ℂ) (y : Fin V.rank → ℂ),
      A.fr τ *ᵥ (((A.fr τ)⁻¹ * U * Q) *ᵥ y) = U *ᵥ (Q *ᵥ y) := fun U Q y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  erw [key]
  have hP' : (Formalism.IndefR.Eqv.UI.instV fr).P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := hP τ
  have hφ : (Formalism.IndefR.Eqv.UI.instV fr).φ (Formalism.L2.Host.tauPl D τ) = tauE D τ := by
    show Formalism.IndefR.Eqv.UI.phiV D _ = _
    simp only [Formalism.IndefR.Eqv.UI.phiV, Equiv.symm_apply_apply]
  erw [hP', hφ]
  rfl

end GlobalTheory.NormDict
