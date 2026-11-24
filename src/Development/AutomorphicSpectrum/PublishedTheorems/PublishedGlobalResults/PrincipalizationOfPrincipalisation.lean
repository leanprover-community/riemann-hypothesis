module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem exists_closed_in_prod {K : Type} [Field K] {M : ℕ} {X' : Scheme.{0}} (h : X' ⟶ PSpace K M)
    (hp : IsProjOver (h ≫ PSpace.str K M)) :
    ∃ (r : ℕ) (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)),
      IsClosedImmersion j ∧ h = j ≫ pullback.fst _ _ := by
  obtain ⟨r, e, he, hc⟩ := hp
  have hs : IsSeparated (PSpace.str K M) := by
    unfold PSpace.str
    infer_instance
  refine ⟨r, pullback.lift h e hc.symm, ?_, (pullback.lift_fst _ _ _).symm⟩
  have h1 : IsClosedImmersion (pullback.lift h e hc.symm ≫ pullback.snd (PSpace.str K M) (PSpace.str K r)) := by
    rw [pullback.lift_snd]; exact he
  exact IsClosedImmersion.of_comp _ (pullback.snd (PSpace.str K M) (PSpace.str K r))

theorem dense_compl_of_snc {Y : Scheme.{0}} (T : TopologicalSpace.Closeds Y)
    (h : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T)) : Dense (T : Set Y)ᶜ := by
  rw [← interior_eq_empty_iff_dense_compl, Set.eq_empty_iff_forall_notMem]
  intro y hyT
  obtain ⟨hreg, U, hy, n, f, J, hrsp, hI⟩ := h y
  have hdom : IsDomain (Y.presheaf.stalk y) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  obtain ⟨V, hV, hyV, e⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show y ∈ U.1 ⊓ ⟨interior (T : Set Y), isOpen_interior⟩ from ⟨hy, hyT⟩)
  have hVU : V ≤ U.1 := e.trans inf_le_left
  have hnil : IsNilpotent (Y.presheaf.map (homOfLE hVU).op (∏ i ∈ J, f i)) := by
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hV.isCompact, Scheme.basicOpen_res, eq_bot_iff]
    rintro z ⟨hzV, hz⟩
    have h1 : z ∈ (Scheme.IdealSheafData.vanishingIdeal T).support := by
      rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact interior_subset (e hzV).2
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (hVU hzV), hI, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton] at h1
    exact (h1 hz).elim
  have h2 := (hnil.map (Y.presheaf.germ V y hyV).hom).eq_zero
  rw [TopCat.Presheaf.germ_res_apply, map_prod] at h2
  exact Finset.prod_ne_zero_iff.2 (fun i _ => (prime_of_regular_params _ hrsp.1 hrsp.2 i).ne_zero) h2

end GlobalTheory.CompanionTheory.Hypotheses₂
