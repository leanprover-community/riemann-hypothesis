module

public import Development.EtaleCohomology.EtaleSheaves.LeafCurveCut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
import Development.EtaleCohomology.EtaleTrace.LDblPf
public import Development.EtaleCohomology.EtaleTrace.LocalSplitting.Cover2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.Cb.curve_mayer_vietoris_of_degree_zero :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.E4.CurveCut.LeafMV := by
  intro _ _ R _ F X U V hUV n
  obtain ⟨d, hd, -⟩ := mayerVietoris R F
  have hc := LateralTheory.EtaleTrace.LSplitPf.Sch.cover2 R U V hUV
  haveI : PreservesLimitsOfShape WalkingCospan sch := by
    unfold sch; infer_instance
  have P := (isPullback_opens_inf U V).map sch
  refine ⟨(d _ _ hc n).comp (pull R P.isoPullback.inv F n), fun x => ?_⟩
  rw [(hd _ _ hc n).2.2 x]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨pull R P.isoPullback.hom F n c, ?_⟩
    rw [AddMonoidHom.comp_apply, ← pull_comp, Iso.inv_hom_id, pull_id]
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
