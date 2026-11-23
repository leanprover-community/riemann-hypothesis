module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem card_bot' {R N : Type} [Ring R] [AddCommGroup N] [Module R N] :
    Nat.card (⊥ : Submodule R N) = 1 := by
  exact Nat.card_unique

theorem UpperTheory.V.Fr.st_count :
    GlobalFiniteness → GreenbergWiles → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContainsAbove S l → ContAction ρ → ∀ μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* (ZMod (l ^ 1))ˣ, μ.comp (toGS Ω _) = cycMod ℚ Ω l 1 → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ σ : G ℚ Ω, IsCC σ → (∀ m, ρ (toGS Ω _ σ) m = m → m = 0) → H0 (twDual μ ρ) = ⊥ → ∀ v₀ : S, (∀ v, v ≠ v₀ → H0 (ρ.comp (locFam S Av v)) = ⊥) → Nat.card (H0 (ρ.comp (locFam S Av v₀))) < Nat.card (H1 (ρ.comp (locFam S Av v₀))) → ∃ z ∈ Z1 ρ, z ∉ B1 ρ ∧ ∀ v, v ≠ v₀ → ∃ m, ∀ g ∈ Dec (F := ℚ) (Av v), z (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := by
  intro hGF hGW Ω _ _ _ l _ hl2 M _ _ _ _ _ S ρ hS hρ μ hμ Av hAv σ hσ hfix hdual v₀ hloc hlt
  classical
  have hH0 : H0 ρ = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    change m ∈ ρ.invariants at hm
    exact (Submodule.mem_bot _).2 (hfix m ((Representation.mem_invariants ρ m).1 hm _))
  obtain ⟨L, hL⟩ : ∃ L : LocCond ρ (locFam S Av), ∀ v, L v = if v = v₀ then ⊤ else ⊥ :=
    ⟨fun v => if v = v₀ then ⊤ else ⊥, fun _ => rfl⟩
  have hcc : ∀ w : InfinitePlace ℚ, w.IsReal → IsCCAt w ((fun _ => σ) w) := by
    intro w _
    obtain ⟨j, hj⟩ := hσ
    exact ⟨j, hj, Subsingleton.elim _ _⟩
  have hgw := hGW ℚ Ω l 1 M S ρ one_pos hl2 hS hρ μ hμ Av hAv (fun _ => σ) hcc L
  obtain ⟨_, hfin1, _, _⟩ := hGF ℚ Ω l 1 M S ρ one_pos hS hρ
  have e1 : Nat.card (H0 (twDual μ ρ)) = 1 := by
    rw [hdual]
    exact card_bot'
  have e2 : ∏ v, Nat.card (H0 (ρ.comp (locFam S Av v))) = Nat.card (H0 (ρ.comp (locFam S Av v₀))) := by
    refine Finset.prod_eq_single v₀ (fun v _ hv => ?_) (fun h => absurd (Finset.mem_univ _) h)
    rw [hloc v hv]
    exact card_bot'
  have e3 : archH0Card S ρ (fun _ => σ) = 1 := by
    unfold archH0Card
    rw [InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ), pow_zero, mul_one]
    apply Finset.prod_eq_one
    intro w _
    exact Nat.card_eq_one_iff_unique.2
      ⟨⟨fun a b => Subtype.ext ((hfix _ a.2).trans (hfix _ b.2).symm)⟩, ⟨⟨0, map_zero _⟩⟩⟩
  have e4 : Nat.card (H0 ρ) = 1 := by
    rw [hH0]
    exact card_bot'
  have e5 : ∏ v, Nat.card (L v) = Nat.card (H1 (ρ.comp (locFam S Av v₀))) := by
    rw [Finset.prod_eq_single v₀ (fun v _ hv => by rw [hL, if_neg hv]; exact card_bot')
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [hL, if_pos rfl]
    exact Nat.card_congr Submodule.topEquiv.toEquiv
  rw [e1, e2, e3, e4, e5] at hgw
  have hapos : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have hcpos : 0 < Nat.card (H0 (ρ.comp (locFam S Av v₀))) := Nat.card_pos
  have key : ∀ a b c d : ℕ, a * 1 * c * 1 = b * 1 * d → c < d → 0 < a → 0 < c → 1 < a := by
    intro a b c d h hcd ha hc
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp at h
      omega
    · by_contra hle
      have ha1 : a = 1 := by omega
      subst ha1
      nlinarith
  have h2 := key _ _ _ _ hgw hlt hapos hcpos
  haveI := Finite.one_lt_card_iff_nontrivial.1 h2
  obtain ⟨x, hx⟩ := exists_ne (0 : Sel ρ (locFam S Av) (continuous_locFam S Av) L)
  obtain ⟨z', hz'⟩ := Submodule.Quotient.mk_surjective _ x.1
  refine ⟨z'.1, z'.2, ?_, ?_⟩
  · intro hz
    apply hx
    apply Subtype.ext
    rw [Submodule.coe_zero, ← hz']
    exact (Submodule.Quotient.mk_eq_zero _).2 hz
  · intro v hv
    have hm := (mem_Sel ρ (locFam S Av) (continuous_locFam S Av) L x.1).1 x.2 v
    rw [hL, if_neg hv, Submodule.mem_bot, ← hz'] at hm
    simp only [resH1, Submodule.mapQ_apply] at hm
    obtain ⟨m, hm'⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hm)
    exact ⟨m, fun g hg => hm' ⟨g, hg⟩⟩
