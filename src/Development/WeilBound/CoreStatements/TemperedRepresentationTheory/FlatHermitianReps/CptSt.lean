module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.IrredSt
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

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace MainStatements.Flath2

theorem cptSt : CptSt := by
  intro hCT D V μ _ _ H _ _ _ π hπ hm f hf
  have c := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  rw [GlobalTheory.AutMult.mCusp_eq_Rcusp, Ne, GlobalTheory.AutMult.multIn_eq_zero_iff] at hm
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hρ := GlobalTheory.Cusp.isUnitaryRep_Rcusp V μ
  have hb0 : GlobalTheory.AutMult.be T T ≠ 0 := fun e => by
    have h := GlobalTheory.AutMult.be_self_pos hπ hρ hT hT0
    rw [e] at h
    simp at h
  have key : ∀ x, T.adjoint (T x) = GlobalTheory.AutMult.be T T • x := fun x =>
    ext_inner_left ℂ fun y => by
      rw [ContinuousLinearMap.adjoint_inner_right, inner_smul_right (𝕜 := ℂ) (E := H)]
      exact GlobalTheory.AutMult.inner_eq_be hπ hρ hT hT x y
  have hcomm : T ∘L repOp π μ f = GlobalTheory.Cusp.RcuspOp V μ f ∘L T :=
    hπ.unitary.comp_repOp hρ c.1 c.2 T hT.2
  have hR : IsCompactOperator (GlobalTheory.Cusp.RcuspOp V μ f) :=
    GlobalTheory.DiscreteSum.isCompactOperator_of_isHilbertSchmidt (hCT D V μ f hf).isHilbertSchmidt
  have hv : ∀ v, T (repOp π μ f v) = GlobalTheory.Cusp.RcuspOp V μ f (T v) := fun v =>
    DFunLike.congr_fun hcomm v
  have e : ⇑(repOp π μ f) =
      (GlobalTheory.AutMult.be T T)⁻¹ • (⇑T.adjoint ∘ (⇑(GlobalTheory.Cusp.RcuspOp V μ f) ∘ ⇑T)) := funext fun v => by
    show repOp π μ f v = (GlobalTheory.AutMult.be T T)⁻¹ • T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v))
    have k : T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v)) = GlobalTheory.AutMult.be T T • repOp π μ f v :=
      (congrArg T.adjoint (hv v)).symm.trans (key (repOp π μ f v))
    calc repOp π μ f v = (GlobalTheory.AutMult.be T T)⁻¹ • (GlobalTheory.AutMult.be T T • repOp π μ f v) :=
          (inv_smul_smul₀ hb0 _).symm
      _ = (GlobalTheory.AutMult.be T T)⁻¹ • T.adjoint (GlobalTheory.Cusp.RcuspOp V μ f (T v)) := congrArg _ k.symm
  rw [e]
  exact ((hR.comp_clm T).clm_comp T.adjoint).smul (GlobalTheory.AutMult.be T T)⁻¹

end MainStatements.Flath2
