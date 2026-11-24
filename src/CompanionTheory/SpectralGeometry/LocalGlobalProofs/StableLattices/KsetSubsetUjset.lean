module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.DSKType

open CompanionTheory.D.DSIC PI.UpqRep

theorem kset_subset_ujset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨h1, h2⟩ := hg
  have h3 : gᴴ * g = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.1 h1)
  show inUJ ε g
  unfold inUJ
  rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]

theorem typeOfHW (hL : LowSpan) (hS : StabLink) (hW : WtLink) : TypeOfHW := by
  intro n ε H _ _ σ S E hσ hM μ x hx0 hfin hhw
  obtain ⟨S₀, hfd, hxS, hst⟩ := hfin
  have hinj : Function.Injective S.subtype := S.injective_subtype
  have := hfd
  have hU : FiniteDimensional ℂ (S₀.comap S.subtype) := by
    refine FiniteDimensional.of_injective
      (LinearMap.codRestrict S₀ (S.subtype ∘ₗ (S₀.comap S.subtype).subtype) (fun y => y.2)) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : S₀ => (y : H)) hab
  have hUst : KStab ε E (S₀.comap S.subtype) := by
    refine (hS n ε H σ S E hσ hM _ hU).2 ?_
    rintro g hg _ ⟨v, hv, rfl⟩
    exact ⟨⟨σ g v, hM.stab g (kset_subset_ujset hg) v v.2⟩, hst g hg v hv, rfl⟩
  have hrel : KRel ε E := fun a b c d _ _ => hM.gl a b c d
  have hun : KUnit ε E := by
    intro a b hab y z
    have := hM.unit a b y z
    simpa [Formalism.REAL.sgn, hab] using this
  obtain ⟨L, hLU, hxL, hLst, hirr, hdom, -⟩ := hL n ε S E μ x _ hrel hun hx0 hhw hU hUst hxS
  have hLfd : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLU
  refine ⟨L.map S.subtype, inferInstance, (hS n ε H σ S E hσ hM L hLfd).1 hLst, ?_, ?_, ?_⟩
  · intro S' hle hS'
    have hle' : S'.comap S.subtype ≤ L := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hle hy
      rwa [← hinj hzy]
    have hmap : (S'.comap S.subtype).map S.subtype = S' := by
      apply Submodule.map_comap_eq_of_le
      exact hle.trans LinearMap.map_le_range
    have hst' : KStab ε E (S'.comap S.subtype) := by
      refine (hS n ε H σ S E hσ hM _ (Submodule.finiteDimensional_of_le hle')).2 ?_
      rwa [hmap]
    rcases hirr _ hle' hst' with h | h
    · left; rw [← hmap, h, Submodule.map_bot]
    · right; rw [← hmap, h]
  · exact ⟨x, ⟨x, hxL, rfl⟩, fun h => hx0 (Subtype.ext h), (hW n ε H σ S E hσ hM μ x).1 hhw.1⟩
  · rintro ν _ ⟨v, hv, rfl⟩ hv0 hwt
    exact hdom ν v hv (fun h => hv0 (by rw [h]; rfl)) ((hW n ε H σ S E hσ hM ν v).2 hwt)

end GlobalTheory.CompanionTheory.DSKType
