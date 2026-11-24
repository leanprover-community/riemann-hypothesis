module

public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ConePairing
import GroundTheory.ProfiniteCohomology.FilteredHomology
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupCone
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.TateCohomology.HerbrandAbstract

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

universe u

section Abstract

variable {k : Type u} [CommRing k] {K L K' L' N N' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L}
  {f' : K' ⟶ L'} (μL : LeibnizPairing L N' L') (ρ : N ⟶ N') (μK : LeibnizPairing K N K')
  (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
    (f'.f n).hom (μK.μ h x z) = μL.μ h ((f.f r).hom x) ((ρ.f s).hom z))

theorem LeibnizPairing.exists_coconeLeft_homology_eq_homologyδ {p s m : ℕ} (h : p + 1 + s = m + 1)
    (X : (mappingCoconeNat f).cycles (p + 1)) (e : N.cycles s) (q : K'.X m)
    (hq : (K'.d m (m + 1)).hom q = μK.μ h (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 ((N.iCycles s).hom e)) :
    ∃ w : L'.cycles m, (L'.iCycles m).hom w =
        μL.μ (show p + s = m by omega) (show L.X p from (((mappingCoconeNat f).iCycles (p + 1)).hom X).2)
          ((ρ.f s).hom ((N.iCycles s).hom e)) - (f'.f m).hom q ∧
      (LeibnizPairing.coconeLeft μL ρ μK hc).homology h (((mappingCoconeNat f).homologyπ (p + 1)).hom X)
          ((N.homologyπ s).hom e) =
        (mappingCoconeNat.homologyδ f' m).hom ((L'.homologyπ m).hom w) := by
  set x := (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 with hx
  set y : L.X p := (((mappingCoconeNat f).iCycles (p + 1)).hom X).2 with hy
  have hX : ((mappingCoconeNat f).d (p + 1) (p + 1 + 1)).hom
      ((x, y) : K.X (p + 1) × shiftNegOneX L (p + 1)) = 0 :=
    iCycles_d_apply (mappingCoconeNat f) (p + 1) (p + 1 + 1) X
  rw [mappingCoconeNat_d_hom_apply' f (p + 1) x y] at hX
  have hdy : (L.d p (p + 1)).hom y = (f.f (p + 1)).hom x := by
    have h2 := congrArg Prod.snd hX
    rw [shiftNegOneD_succ_apply, shiftNegOneSucc_apply] at h2
    exact (add_neg_eq_zero.1 h2).symm
  have hd : (L'.d m (m + 1)).hom (μL.μ (show p + s = m by omega) y ((ρ.f s).hom ((N.iCycles s).hom e)) -
      (f'.f m).hom q) = 0 := by
    rw [map_sub, μL.leibniz, hdy, hom_apply_hom_apply_eq_of_comp_eq (ρ.comm s (s + 1)),
      iCycles_d_apply, map_zero, map_zero, smul_zero, add_zero, ← hc h x,
      hom_apply_hom_apply_eq_of_comp_eq (f'.comm m (m + 1)), hq, sub_self]
  refine ⟨L'.cyclesMk _ (m + 1) (by simp) hd, L'.i_cyclesMk _ _ _ _, ?_⟩
  exact LeibnizPairing.coconeLeft_homology_eq_homologyδ μL ρ μK hc h X e q _ hq (L'.i_cyclesMk _ _ _ _)

end Abstract

end GroundTheory.ProfCoh
