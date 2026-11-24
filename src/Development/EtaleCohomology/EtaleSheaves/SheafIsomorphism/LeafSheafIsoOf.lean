module

public import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShIsoPf.Sh
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

def LeafSecRep : Prop := ∀ (B : Scheme.{0}) (q : ℕ), ∃ e : ∀ (F : SShv B q) (U : B.Etale),
    ((H0 B q).obj ((OU B q).obj U) ⟶ F) ≃ ToType (F.obj.obj (op U)),
  (∀ (F G : SShv B q) (g : F ⟶ G) (U : B.Etale) (t : (H0 B q).obj ((OU B q).obj U) ⟶ F),
    e G U (t ≫ g) = g.hom.app (op U) (e F U t)) ∧
  (∀ (F : SShv B q) (U U' : B.Etale) (a : U' ⟶ U) (t : (H0 B q).obj ((OU B q).obj U) ⟶ F),
    e F U' ((H0 B q).map ((OU B q).map a) ≫ t) = F.obj.map a.op (e F U t)) ∧
  (∀ (F : SShv B q) (U : B.Etale) (t t' : (H0 B q).obj ((OU B q).obj U) ⟶ F), e F U (t - t') = e F U t - e F U t')

theorem LeafSheafIso_of (hR : LeafSecRep) : LeafSheafIso := by
  intro B q F G g hinj hsurj
  obtain ⟨e, hg, hres, hsub⟩ := hR B q
  have h0 : ∀ (F : SShv B q) U, e F U 0 = 0 := fun F U => by simpa using hsub F U 0 0
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  refine (Sheaf.isLocallyBijective_iff_isIso g).1 ⟨⟨fun {X} x y hxy => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · let t := (e F X.unop).symm x - (e F X.unop).symm y
    have ht : t ≫ g = 0 := by
      apply (e G X.unop).injective
      rw [hg, hsub, h0, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      simpa [sub_eq_zero] using hxy
    obtain ⟨S, hS, hP⟩ := hinj X.unop t ht
    refine (EtTop B).superset_covering ?_ hS
    intro U' a ha
    have := congrArg (e F U') (hP U' a ha)
    rw [hres, h0, hsub, Equiv.apply_symm_apply, Equiv.apply_symm_apply, map_sub, sub_eq_zero] at this
    exact this
  · obtain ⟨S, hS, hP⟩ := hsurj U ((e G U).symm s)
    refine (EtTop B).superset_covering ?_ hS
    intro U' a ha
    obtain ⟨t, ht⟩ := hP U' a ha
    refine ⟨e F U' t, ?_⟩
    rw [← hg, ← ht, hres, Equiv.apply_symm_apply]

end LateralTheory.E.LeafShIsoPf.Sh
