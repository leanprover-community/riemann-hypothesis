module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem range_jK_fromSpecStalk_subset_of_dense_range {U S : Scheme.{0}} [GlobalTheory.IsNormalScheme S]
    [IsLocallyNoetherian S] (j : U ⟶ S) [IsOpenImmersion j] (hj : Dense (Set.range j)) (s : S) :
    Set.range (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) ⊆
      Set.range j := by
  rintro _ ⟨x, rfl⟩
  have hZ : irreducibleComponent s ∈ irreducibleComponents S :=
    irreducibleComponent_mem_irreducibleComponents s
  have hZo : IsOpen (irreducibleComponent s) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hZ
  obtain ⟨_, hu, ⟨u, rfl⟩⟩ := hj.inter_open_nonempty _ hZo ⟨s, mem_irreducibleComponent⟩
  have hg := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hZ)
  have hgs : hZ.1.genericPoint ⤳ s := hg.specializes mem_irreducibleComponent
  have hgr : hZ.1.genericPoint ∈ Set.range (S.fromSpecStalk s) := by
    rw [Scheme.range_fromSpecStalk]; exact hgs
  obtain ⟨p, hp⟩ := hgr
  have hxp : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s)) x ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes (R := S.presheaf.stalk s) _ _).mp ?_
    show Ideal.comap _ x.asIdeal ≤ p.asIdeal
    have hx0 : x.asIdeal = ⊥ :=
      @Ideal.eq_bot_of_prime (FractionRing (S.presheaf.stalk s)) _ x.asIdeal x.isPrime
    intro a ha
    rw [Ideal.mem_comap, hx0, Ideal.mem_bot] at ha
    have ha0 : a = 0 :=
      IsFractionRing.injective (S.presheaf.stalk s) (FractionRing (S.presheaf.stalk s))
        (by simpa using ha)
    rw [ha0]
    exact Ideal.zero_mem _
  have h1 : (ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s) x ⤳
      hZ.1.genericPoint := by
    rw [Scheme.Hom.comp_apply, ← hp]
    exact hxp.map (S.fromSpecStalk s).continuous
  have h2 : hZ.1.genericPoint ⤳ j u := hg.specializes hu
  exact (h1.trans h2).mem_open j.isOpenEmbedding.isOpen_range ⟨u, rfl⟩

end GlobalTheory
