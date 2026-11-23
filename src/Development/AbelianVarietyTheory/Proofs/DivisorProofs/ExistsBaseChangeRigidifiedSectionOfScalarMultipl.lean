module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt

@[expose] public section

noncomputable section

namespace GlobalTheory.KeySwapSec

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open ReciprocityTheory.ChartRestriction.G.H1

theorem exists_isFibreOf_of_isMul (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR R ⟶ G))
    (x : KeyIn R') (hL : L.IsLB) (hx : IsFibreOf x G L rig θ w f) (θ₀ : L.Sec) (b : R) (hb : IsMul (X := G) θ b θ₀) :
    ∃ (th₀ : x.P.L.Sec) (hth₀ : ∀ s : Sp R', ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th₀),
      (∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i) ∧
      IsFibreOf ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, x.v, x.basis⟩ G L rig θ₀ w f := by
  obtain ⟨φ, he, e, hg, F, hp, hgen, hr, hs, hF, hFe, hv⟩ := hx
  obtain ⟨th₀, h₀⟩ := sec_pull_down ((isGen_iff e).1 hgen) hL x.P.isLB θ₀
  have h₁ := (KeyCancel.appLE_eq_iff_stalk e θ x.th).1 hs
  have hm : ∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i := by
    refine (sec_eq_iff _ _ _ _).2 fun k y hk => ?_
    obtain ⟨j, hj⟩ := exists_chart hL (φ y)
    have e₁ := h₁ _ (𝟙 _) y j k hj hk
    have e₀ := h₀ _ (𝟙 _) y j k hj hk
    rw [hb j, gs_mul (𝟙 _ ≫ φ) y _ hj, gs_constFn _ _ (𝟙 _ ≫ φ) y hj, e₀, Category.id_comp, hp.1.w, cst_comp,
      mul_left_comm] at e₁
    exact ((Units.mul_right_inj _).1 e₁).symm
  refine ⟨th₀, fun s => ?_, hm, φ, he, e, hg, F, hp, hgen, hr, (KeyCancel.appLE_eq_iff_stalk e θ₀ th₀).2 h₀, hF, hFe, hv⟩
  obtain ⟨z, hz, hne⟩ := x.th_ne s
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hne
  refine ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩⟩
  rw [hm k, Scheme.basicOpen_mul] at hk
  exact hk.2

end GlobalTheory.KeySwapSec
