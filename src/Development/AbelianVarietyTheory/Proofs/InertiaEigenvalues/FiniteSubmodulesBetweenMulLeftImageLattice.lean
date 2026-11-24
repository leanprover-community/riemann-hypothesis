module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem finite_quot_span_of_ne_zero (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have h1 : Ideal.span {c} = IsLocalRing.maximalIdeal O ^ n := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow, hu,
      Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [h1]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

theorem finite_between_mulLat (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L)
    (c : K.O) (hc : c ≠ 0) :
    {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by
  haveI := finite_quot_span_of_ne_zero K.O c hc
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1
  have hfg : (⊤ : Submodule K.O L).FG := Module.Finite.fg_top
  set S : Submodule K.O L := Ideal.span {c} • (⊤ : Submodule K.O L) with hS
  haveI : Finite (L ⧸ S) := Submodule.finite_quotient_smul _ hfg
  haveI : Finite (Submodule K.O (L ⧸ S)) :=
    Finite.of_injective (fun P : Submodule K.O (L ⧸ S) => (P : Set (L ⧸ S))) SetLike.coe_injective
  let f : Submodule K.O B.A → Submodule K.O (L ⧸ S) := fun M => (M.comap L.subtype).map S.mkQ
  have hSle : ∀ M : Submodule K.O B.A, mulLat K.O (algebraMap K.O B.A c) L ≤ M → S ≤ M.comap L.subtype := by
    intro M hM
    rw [hS, Submodule.smul_le]
    intro r hr x _
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have hx : algebraMap K.O B.A c * (x : B.A) ∈ M := hM ⟨x, x.2, rfl⟩
    have : ((a * c) • x : L) = (a • (algebraMap K.O B.A c * (x : B.A)) : B.A) := by
      rw [Submodule.coe_smul, ← Algebra.smul_def, smul_smul]
    rw [Submodule.mem_comap, Submodule.subtype_apply, this]
    exact M.smul_mem a hx
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M₁ h₁ M₂ h₂ heq
  have e1 : M₁.comap L.subtype = M₂.comap L.subtype := by
    have := congrArg (Submodule.comap S.mkQ) heq
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.2 (hSle M₁ h₁.1), sup_eq_right.2 (hSle M₂ h₂.1)] at this
  have e2 := congrArg (Submodule.map L.subtype) e1
  rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 h₁.2,
    inf_eq_right.2 h₂.2] at e2

end GlobalTheory.UnitLemma
