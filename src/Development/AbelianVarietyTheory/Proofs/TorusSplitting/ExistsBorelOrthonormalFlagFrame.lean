module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem exists_unit_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ (∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1) ∧ X.la1 (rmul x b) = X.la1 x ∧ (∀ th, I2.phiFD X th (rmul x b) = I2.phiFD X th x) ∧ ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P → X.pnorm la P x = ‖P (rmul x b)‖ := by
  intro E _ _ _ r X x hx
  have hb := FrameDegreeData.bOf_mem X hx
  have ho := FrameDegreeData.ortho_bOf X hx
  have hd : ∀ τ i, ‖dmin X.Gm (rmul x (FrameDegreeData.bOf X x)) τ i‖ = 1 := by
    intro τ i
    unfold dmin
    rw [ho τ, FrameDegreeData.lminor_diagonal, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Complex.norm_real]
    rcases FrameDegreeData.sgn_sq X.p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) j : Fin r) with h | h <;>
      rw [h] <;> simp
  have hl : X.la1 (rmul x (FrameDegreeData.bOf X x)) = X.la1 x := by
    unfold Data.la1
    rw [ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimumSq_rightBorel X hx hb]
  refine ⟨_, hb, OrthogonalFrameDomain.rmul_mem_dom X hx hb, hd, hl, fun th => ?_, fun la P hP => ?_⟩
  · unfold I2.phiFD
    rw [hl]
  · rw [← FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx _ hb]
    unfold Data.pnorm
    simp only [norm_div, hd, div_one, Real.one_rpow, Finset.prod_const_one, _root_.mul_one]

end GlobalTheory.EtaAn
