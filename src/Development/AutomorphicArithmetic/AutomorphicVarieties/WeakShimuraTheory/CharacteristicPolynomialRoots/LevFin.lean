module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem ine_dies {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {S : Set (HeightOneSpectrum (𝓞 k))} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hv : v ∉ S)
    (hA : IsPlaceOver A v) {t : G k Ω} (ht : t ∈ Ine (F := k) A) : toGS Ω S t = 1 := by
  refine (QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, ht⟩

private theorem fiber_fin {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
    (v : HeightOneSpectrum (𝓞 k)) : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 k) = v}.Finite := by
  have hne : v.asIdeal.map (algebraMap (𝓞 k) (𝓞 L)) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 L))]
    exact v.ne_bot
  refine (Ideal.finite_factors hne).subset fun w hw => ?_
  have hw' : w.under (𝓞 k) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hw']
  exact le_rfl

theorem UpperTheory.V.Ws.Pu.levFin :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev), ∃ Z : Set (HeightOneSpectrum (𝓞 L)), Z.Finite ∧ ∀ w ∉ Z, ((l : ℕ) : 𝓞 L) ∉ w.asIdeal ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ g ∈ Ine (F := L) A, V.pr g = 1 := by
  intro l _ L Ω _ _ _ _ _ _ s V
  refine ⟨(fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 (W.Lp L))) ⁻¹' V.S',
    V.fin.preimage' fun v _ => fiber_fin v, fun w hw => ⟨fun hl => hw (V.sub (Or.inl ?_)), fun A hA g hg => ?_⟩⟩
  · show algebraMap (𝓞 (W.Lp L)) (𝓞 L) _ ∈ w.asIdeal
    rwa [map_natCast]
  · have hv : IsPlaceOver A (w.under (𝓞 (W.Lp L))) := fun x => hA (algebraMap (𝓞 (W.Lp L)) (𝓞 L) x)
    have hg' : W.resP L Ω g ∈ Ine (F := W.Lp L) A := hg
    have hw' : w.under (𝓞 (W.Lp L)) ∉ V.S' := hw
    exact Subtype.ext (ine_dies hw' hv hg')
