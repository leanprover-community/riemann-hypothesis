module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.ZH.ThetaSys

theorem supI_closedPoint_eq : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω),
    M.HasDiv S.th → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z)
    (emb : Ω →+* FractionRing V), (∀ (U : M.Z.Opens) (f : Γ(M.Z, U)), ξ (IsLocalRing.closedPoint V) ∈ U →
      emb (valF M.pt U f) = algebraMap V (FractionRing V) (valR ξ U f)) →
    S.supI M (ξ (IsLocalRing.closedPoint V)) =
      {a | S.th a ≠ 0 ∧ ∀ b, ∃ v : V, emb (S.th b) = algebraMap V (FractionRing V) v * emb (S.th a)} := by
  intro o Ω _ _ _ S M hD V _ _ _ ξ emb hemb
  set z := ξ (IsLocalRing.closedPoint V) with hzdef
  have hs : ξ (IsLocalRing.closedPoint V) ⤳ z := specializes_rfl
  have key : ∀ (x : Ω) (hx : x ∈ M.O z), emb x = algebraMap V (FractionRing V) (RatModel.valLoc ξ z hs ⟨x, hx⟩) := by
    intro x hx
    obtain ⟨U, f, hz, rfl⟩ := hx
    rw [RatModel.valLoc_valF ξ hs hz f]
    exact hemb U f hz
  ext a
  simp only [supI, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨ha, fun b => ⟨RatModel.valLoc ξ z hs ⟨_, hb b⟩, ?_⟩⟩
    rw [← key _ (hb b), ← map_mul, div_mul_cancel₀ _ ha]
  · rintro ⟨ha, hc⟩
    obtain ⟨x₀, hx₀⟩ := hD z
    obtain ⟨v, hv⟩ := hc x₀
    have hea : emb (S.th a) ≠ 0 := (map_ne_zero emb).2 ha
    have hw := key _ (hx₀.2 a)
    have hunit : IsUnit (RatModel.valLoc ξ z hs ⟨_, hx₀.2 a⟩) := by
      refine IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_)
      have hv0 : algebraMap V (FractionRing V) v ≠ 0 := by
        intro h0
        exact (map_ne_zero emb).2 hx₀.1 (by rw [hv, h0, zero_mul])
      rw [map_mul, map_one, ← hw, map_div₀, hv]
      field_simp
    have hu : IsUnit (⟨S.th a / S.th x₀, hx₀.2 a⟩ : M.O z) :=
      (RatModel.isUnit_valLoc_iff ξ hzdef.symm _).1 hunit
    exact (hx₀.div_iff_isUnit a).2 hu

end GlobalTheory.ZH.ThetaSys
