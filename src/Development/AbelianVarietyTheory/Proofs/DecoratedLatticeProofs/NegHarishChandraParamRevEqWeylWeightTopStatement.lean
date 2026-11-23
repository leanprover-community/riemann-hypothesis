module

public import Formalism.LocalToGlobal.HermitianForms.LastCoordinateUniformizerVectorSpansOrthogonalLi
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHarishChandraParamRevEqWeylWeightTop
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.neg_harishChandraParam_rev_eq_weylWeight_top : ∀ (D : D7) (u : D.what₂.Word) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), (∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) → ∀ τ (i : Fin D.sp.X'.rank), -M.lam τ (Fin.rev i) = (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℝ) + ((rhoVec D.sp.X'.rank i : ℚ) : ℝ) := by
  first | exact @GlobalTheory.Core.Rk.TopParam.neg_lam_rev_eq | exact GlobalTheory.Core.Rk.TopParam.neg_lam_rev_eq | (intros; apply GlobalTheory.Core.Rk.TopParam.neg_lam_rev_eq <;> assumption)
