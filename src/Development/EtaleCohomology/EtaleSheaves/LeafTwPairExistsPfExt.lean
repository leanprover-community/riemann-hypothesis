module

public import Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPf
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairExistsPf

variable (q : ℕ) (k : ℤ)

instance resKInj : (res (ZMod q) (tw q k)).IsKInjective := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem ext_homotopy {S T L : Cx (ZMod q)} (ε : S ⟶ T) [QuasiIso ε] (a : S ⟶ L) [L.IsKInjective] :
    ∃ u : T ⟶ L, Nonempty (Homotopy (ε ≫ u) a) := by
  let _ := HasDerivedCategory.standard (Shv (ZMod q))
  let Φ := DerivedCategory.quotientCompQhIso (Shv (ZMod q))
  obtain ⟨g, hg⟩ := (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj T) L).2
    (Φ.hom.app T ≫ inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map a ≫ Φ.inv.app L)
  obtain ⟨u, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨u, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj S) L).1
  have nat : ∀ {X Y : Cx (ZMod q)} (f : X ⟶ Y), DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) =
      Φ.hom.app X ≫ DerivedCategory.Q.map f ≫ Φ.inv.app Y := by
    intro X Y f
    have := Φ.hom.naturality f
    simp only [Functor.comp_map] at this
    rw [← Category.assoc, ← this]
    simp
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (ε ≫ u)) = _
  rw [Functor.map_comp, Functor.map_comp, hg, nat ε, nat a]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id_assoc]

theorem leafTwResExt : LeafTwResExt := by
  intro q _ k T e ⟨_, ε, hε, he⟩
  obtain ⟨u, ⟨H⟩⟩ := ext_homotopy q (ε := ε) (a := resAug (tw q k))
  refine ⟨u, fun U ζ => ?_⟩
  have h0 : ε.f 0 ≫ u.f 0 = (resAug (tw q k)).f 0 := by
    have hc := H.comm 0
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hc
    have z1 : IsZero ((sgl (tw q k)).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
    have z2 : IsZero ((res (ZMod q) (tw q k)).X (-1)) := by
      unfold res InjectiveResolution.cochainComplex
      exact HomologicalComplex.isZero_extend_X _ _ _ (by
        intro n hn
        change ((n : ℕ) : ℤ) = -1 at hn
        omega)
    have e1 : H.hom 1 0 = 0 := z1.eq_of_src _ _
    have e2 : H.hom 0 (-1) = 0 := z2.eq_of_tgt _ _
    rw [e1, e2] at hc
    simpa using hc
  rw [← he U ζ, map_map, map_map, h0]
  rfl

theorem LeafTwPairExists_of' (h1 : LeafTwTensEx) (h2 : LeafTwTensRes) : LateralTheory.E.CupProductRingLaws.LeafTwPairExists :=
  LeafTwPairExists_of h1 h2 leafTwResExt

end LateralTheory.E.LeafTwPairExistsPf
