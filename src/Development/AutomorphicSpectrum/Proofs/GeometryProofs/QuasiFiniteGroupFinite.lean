module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.finite_of_qfGroup : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T), Finite T := by
  intro R _ _ T _ Γ
  have hqf : LocallyQuasiFinite Γ.G.hom := Γ.quasiFinite
  have hqc : QuasiCompact Γ.G.hom := Γ.quasiCompact
  let F := pullback Γ.G.hom (genPt R).hom
  let g : F ⟶ Spec (CommRingCat.of (FractionRing R)) := pullback.snd Γ.G.hom (genPt R).hom
  have hK : ∀ u v : Spec (CommRingCat.of (FractionRing R)), u = v := fun u v =>
    Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) u v
  let b : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  have hgqf : LocallyQuasiFinite g := inferInstance
  have hgqc : QuasiCompact g := inferInstance
  have huniv : g ⁻¹' {b} = Set.univ := by
    ext x; simp [hK (g x) b]
  have hfin : Finite F := by
    have h := g.finite_preimage_singleton b
    rw [huniv] at h
    exact Set.finite_univ_iff.mp h
  have hw : ∀ t, (Γ.pt t).left ≫ Γ.G.hom = 𝟙 _ ≫ (genPt R).hom := fun t => by
    rw [Category.id_comp]; exact Over.w (Γ.pt t)
  let f : T → F := fun t => (pullback.lift _ _ (hw t)) b
  refine Finite.of_injective f ?_
  intro s t hst
  have h := congrArg (pullback.fst Γ.G.hom (genPt R).hom) hst
  simp only [f] at h
  simp only [← Scheme.Hom.comp_apply, pullback.lift_fst] at h
  exact Γ.pt_inj s t b b h

end GlobalTheory.CompanionTheory.Ar.BT
