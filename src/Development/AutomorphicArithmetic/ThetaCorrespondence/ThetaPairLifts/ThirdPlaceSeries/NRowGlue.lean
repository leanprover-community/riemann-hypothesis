module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConstStatement
public import Development.AutomorphicArithmetic.ResidueCharacters.NumCost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
variable {D : D7}
end UpperTheory.N
theorem UpperTheory.N.starSF_of_rowC_alt (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) : _root_.UpperTheory.N.RowCAlt A B → _root_.UpperTheory.N.StarSelfDualCondition := by
  intro h eps Fm
  obtain ⟨x0, h0⟩ := h Fm
  obtain ⟨C0, x1, hC0, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  refine ⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1),
    fun x hxx hx i HW F Cm X C₂ hS k hTw hs h2 π hπ => ?_⟩
  have h3 : 3 ≤ x := (le_max_left _ _).trans hxx
  have hb := h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hs h2 π hπ
  obtain ⟨-, -, -, hn, ht, -⟩ := hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i
  have hlog : 1 ≤ Real.log (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hc : UpperTheory.N.costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤
      midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1) :=
    UpperTheory.N.Num.cost_le (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hs le_rfl
  unfold Bd at hb ⊢
  linarith
end
end
