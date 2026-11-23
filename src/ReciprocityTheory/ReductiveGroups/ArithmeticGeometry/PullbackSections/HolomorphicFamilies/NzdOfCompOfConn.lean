module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

theorem nzdOfComp_of_conn
    (hc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), IsPreconnected X.dom) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.NZDOfCompSt := by
  intro D T h j hj w F σ hσ hne w' G hFG
  have hFc : (F : T.R j) ∈ T.C j w := cutR_le T.C j w F.2
  have hGc : (G : T.R j) ∈ T.C j w' := cutR_le T.C j w' G.2
  have hmem : (F : T.R j) * (G : T.R j) ∈ cutR T.C j (WeightAlgebra.wadd w w') := by
    rw [cutR_eq T.C hj]; exact h.toLawsCore.mul j hj w w' _ hFc _ hGc
  have hval : (F : T.R j) * (G : T.R j) = 0 := by
    have h1 : incG deg (cutR T.C j) w F * incG deg (cutR T.C j) w' G = 0 := hFG
    rw [incG_mul deg (cutR T.C j) (deg_wadd w w') F G hmem] at h1
    have h2 := incG_inj deg (cutR T.C j) _ (h1.trans (map_zero _).symm)
    exact congrArg Subtype.val h2
  have hU := h.unf j hj σ hσ
  have hrd : rdU (T.U j σ) (F : T.R j) * rdU (T.U j σ) (G : T.R j) = 0 := by
    rw [← rdU_mul, hval, map_zero]
  have hFs := fun k => (hU.2.2.2.2.1 _ _ (dom_wtA w) _ (cusp_le_sec _ _ _ _ _ hFc) k).1
  have hGs := fun k => (hU.2.2.2.2.1 _ _ (dom_wtA w') _ (cusp_le_sec _ _ _ _ _ hGc) k).1
  have hG0 : ∀ k, ∀ y ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) (G : T.R j) k y = 0 := by
    intro k
    obtain ⟨x0, hx0, hx0ne⟩ := hne k
    exact eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom _) (hc _ _ _) (hFs k) (hGs k)
      (fun y _ => congrFun (congrFun hrd k) y) hx0 hx0ne
  have hsup : supN (T.U j σ).X (laU (T.U j σ) (wtA w') w'.n) (rdU (T.U j σ) (G : T.R j)) = 0 := by
    unfold supN supE
    have h0 : ∀ p : FPt (T.U j σ).X, ENNReal.ofReal (((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA w') w'.n p.1)
        (rdU (T.U j σ) (G : T.R j) p.1) p.2) = 0 := by
      intro p
      unfold Data.pnorm
      rw [hG0 p.1 p.2 p.2.2]
      simp
    simp [h0]
  exact Subtype.ext (h.supDef j hj _ _ (dom_wtA w') σ hσ _ hGc hsup)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
