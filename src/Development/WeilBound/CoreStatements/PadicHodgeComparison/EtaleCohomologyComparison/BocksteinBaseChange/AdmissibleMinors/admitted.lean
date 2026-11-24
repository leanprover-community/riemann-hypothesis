module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.AdmAbs
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison

theorem adm : ComparisonAdmissible := by
  intro l _ K R G P S hR M hG n hInj hSpan a b
  obtain ⟨r, w, hw, hsp⟩ := hSpan
  have hcσ : ∀ (g : K.fixingSubgroup) (j : Fin a) (φ : Module.Dual K (HdR M.q n)),
      R.σ g (P.c M n (b j) φ) = ∑ k, (M.mat n b g).map R.q k j * P.c M n (b k) φ := by
    intro g j φ
    rw [← P.equi M n hG g (b j) φ]
    have hact : M.act n g (b j) = ∑ k, M.mat n b g k j • b k := by
      conv_lhs => rw [← Matrix.toLin_toMatrix b b (M.act n g)]
      exact Matrix.toLin_self b b _ j

    rw [hact, map_sum, AddMonoidHom.finsetSum_apply]
    simp only [P.lin, Matrix.map_apply]
  exact AdmAbs.admissible_of_absolute (fun g => R.σ g) S hR.stab hR.frac (fun g => (M.mat n b g).map R.q)
    (fun g i j => hR.q_mem _)
    (fun x hx hx0 h => hR.eig x hx hx0 fun g =>
      ⟨(M.mat n b g).det, by rw [h g, RingHom.map_det, RingHom.mapMatrix_apply]⟩)
    (fun j φ => P.c M n (b j) φ) hcσ (fun z h => hInj b z h) w (fun i x g => hw i x g)
    (fun j => hsp (b j))

end CrystallineSemistableComparison
