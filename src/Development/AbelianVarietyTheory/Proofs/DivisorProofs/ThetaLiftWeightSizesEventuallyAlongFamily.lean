module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BTLeFiveQuarters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventually
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow

theorem weightSizes_along : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x →
    ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx1 hx i j => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, hw1, hsum⟩ := h0 x hx hx1 i
  have SZ := Fm.sizes x hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := SZ
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'.le (by linarith)
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have hwj : ∀ τ, wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    intro τ
    unfold wj
    rw [dite_eq_left (by omega)]
    rfl
  have hwin : ∀ τ, 0 < wj D (j.1 + 1) τ ∧ wj D (j.1 + 1) τ ≤ 2 * L.sc.b := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have := L.win_thick (j.1 + 1) (by omega) (by omega) τ h1
      constructor <;> linarith [this.1, this.2]
    by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have a := L.win_top (j.1 + 1) (by omega) (by omega) τ ⟨t, ht⟩ e.symm
      have a3 := L.bT_ge ⟨t, ht⟩
      have a4 := GlobalTheory.Ggeo.bT_le_five_quarters P ⟨t, ht⟩
      constructor <;> linarith [a.1, a.2]
    · have a := L.win_thin (j.1 + 1) (by omega) (by omega) τ ⟨(D.eTau τ).2, h2, h1⟩
      constructor <;> linarith [a.1, a.2]
  refine ⟨fun τ => ⟨?_, ?_, fun l => ?_, fun l => ?_⟩, fun l => (hG l l).1⟩
  · rw [← hwj]; exact (hwin τ).1
  · rw [← hwj]; exact (hwin τ).2
  · have := L.cloud_v τ l
    exact ⟨this.1, by linarith [this.2]⟩
  · have := L.be_close τ l j
    push_cast at this
    linarith

end GlobalTheory.LowRow
