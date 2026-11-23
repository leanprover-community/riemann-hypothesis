module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTan

theorem range_spMap_fst_eq (B M : Type) [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) = Set.univ := by
  refine Set.eq_univ_of_forall fun y ↦ ⟨spMap (TrivSqZeroExt.inlHom B M) y, ?_⟩
  change PrimeSpectrum.comap _ (PrimeSpectrum.comap _ y) = y
  apply PrimeSpectrum.ext
  ext x
  change (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) ∈ y.asIdeal ↔ x ∈ y.asIdeal
  have hm : (TrivSqZeroExt.inr x.snd : TrivSqZeroExt B M) ∈ y.asIdeal :=
    y.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact y.asIdeal.zero_mem)
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm
  constructor
  · intro h; rw [hx]; exact y.asIdeal.add_mem h hm
  · intro h
    have e : (TrivSqZeroExt.inl x.fst : TrivSqZeroExt B M) = x - TrivSqZeroExt.inr x.snd := by
      rw [eq_sub_iff_add_eq]; exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x
    rw [e]; exact y.asIdeal.sub_mem h hm

theorem exists_unique_ringHom_of_sqZero (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (U : X.affineOpens) (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (ρ : Sec s U.1 →+* B) (z : Sp (TrivSqZeroExt B M) ⟶ X)
    (hz : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap ρ ≫ affPt s U) :
    ∃! c : Sec s U.1 →+* TrivSqZeroExt B M, spMap c ≫ affPt s U = z ∧ ∀ b, (c b).fst = ρ b := by
  have hr : Set.range z ⊆ Set.range (affPt s U) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ : y ∈ Set.range (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) := by
      rw [range_spMap_fst_eq]; trivial
    refine ⟨spMap ρ x, ?_⟩
    change (spMap ρ ≫ affPt s U) x = (spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z) x
    rw [hz]
  haveI : IsOpenImmersion (affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
  set g := IsOpenImmersion.lift (affPt s U) z hr with hg
  have hgf : g ≫ affPt s U = z := IsOpenImmersion.lift_fac _ _ _
  have hsp : ∀ c c' : Sec s U.1 →+* TrivSqZeroExt B M,
      spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c' := fun c c' h ↦ by
    have h' := (cancel_mono (affPt s U)).1 h
    have := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom this
  have hsp' : ∀ c c' : Sec s U.1 →+* B,
      spMap c ≫ affPt s U = spMap c' ≫ affPt s U → c = c' := fun c c' h ↦ by
    have h' := (cancel_mono (affPt s U)).1 h
    have := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom this
  set c₀ : Sec s U.1 →+* TrivSqZeroExt B M := (Spec.preimage g).hom with hc₀
  have hc : spMap c₀ = g := Spec.map_preimage g
  have h₁ : spMap c₀ ≫ affPt s U = z := by rw [hc, hgf]
  refine ⟨c₀, ⟨h₁, ?_⟩, fun c hc' ↦ hsp _ _ (hc'.1.trans h₁.symm)⟩
  have e : spMap ((TrivSqZeroExt.fstHom B B M).toRingHom.comp c₀) ≫ affPt s U =
      spMap ρ ≫ affPt s U := by
    rw [← hz, ← h₁, ← Category.assoc, ← Spec.map_comp]; rfl
  intro b
  exact congrArg (fun f : Sec s U.1 →+* B ↦ f b) (hsp' _ _ e)

end GlobalTheory.AbTan
