module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem adjoin_int_le_chartQ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {κ : Type} (x : κ → Ω) (c : κ) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : a ∈ chartQ x c := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap r => simpa using intCast_mem (chartQ x c) r
  | add a b _ _ ha hb => exact (chartQ x c).add_mem ha hb
  | mul a b _ _ ha hb => exact (chartQ x c).mul_mem ha hb

theorem exists_prime_of_chart {Ω : Type} [Field Ω] [Algebra ℚ Ω] {X : Scheme.{0}}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω} {c : κ} (hξ : IsCptGen ξ) {p : Cpt ξ}
    (hle : ∀ s ∈ chartQ x c, s ∈ regAt ξ p)
    (hdict : ∀ a ∈ regAt ξ p, ∃ s ∈ chartQ x c, unitAt ξ p s ∧ s * a ∈ chartQ x c) :
    ∃ I : Ideal (chartQ x c), I.IsPrime ∧ (∀ s : chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (chartQ x c) I (regAt ξ p) := by
  haveI hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hξ p).1
  have hmem : ∀ s : chartQ x c, (s : Ω) ∈ regAt ξ p := fun s => hle _ s.2
  let f : chartQ x c →+* regAt ξ p :=
    ((chartQ x c).val : chartQ x c →+* Ω).codRestrict (regAt ξ p) hmem
  have hI : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hu : ∀ s : chartQ x c,
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  refine ⟨_, hI, hu, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨s, hs, hus, hsa⟩ := hdict a ha
    exact ⟨⟨s, hs⟩, (hu ⟨s, hs⟩).2 hus, hsa⟩
  · rintro ⟨s, hs, hsa⟩
    have hus := (hu s).1 hs
    have e : a = ((s : Ω) * a) * (s : Ω)⁻¹ := by
      field_simp [hus.1]
    rw [e]
    exact (regAt ξ p).mul_mem (hle _ hsa) hus.2.2

theorem exists_prime_chartQ : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → ∀ p : Cpt ξ, Char0 ξ p → InChart ξ x c p → ∃ I : Ideal (Mdl.chartQ x c), I.IsPrime ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) := by
  intro Ω _ _ X ξ κ x c hT p hp hc
  refine exists_prime_of_chart hT.gen (fun s hs => chartQ_le hp hc hs) fun a ha => ?_
  obtain ⟨s, hs, hus, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x hT c p hc a).1 ha
  exact ⟨s, adjoin_int_le_chartQ x c hs, hus, adjoin_int_le_chartQ x c hsa⟩

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
