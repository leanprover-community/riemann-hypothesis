module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZIsometric
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

section

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ}

theorem toZ_tens_isometric (L M : HermLB p) (hLM : ∀ τ, (wZ (L.tens M) t τ).IsCInf)
    (hL : ∀ τ, (wZ L t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf) :
    (toZ (L.tens M) t hLM).Isometric ((toZ L t hL).tens (toZ M t hM)) :=
  HermLB.isometric_of_eqOn fun _ _ _ _ => rfl

noncomputable def toZClass (t : X ⟶ Sp ℤ) (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf) :
    HermLB.IsomClass p →+ HermLB.IsomClass t :=
  AddMonoidHom.mk' (M := HermLB.IsomClass p) (G := HermLB.IsomClass t)
    (Quotient.map (sa := HermLB.isometrySetoid p) (sb := HermLB.isometrySetoid t)
      (fun L => toZ L t (H L)) fun L M h => toZ_isometric k X p t L M (H L) (H M) h)
    (by
      rintro ⟨L⟩ ⟨M⟩
      exact HermLB.icls_eq_iff.2 (toZ_tens_isometric L M (H _) (H _) (H _)))

theorem toZClass_icls (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf) (L : HermLB p) :
    toZClass t H L.icls = (toZ L t (H L)).icls := rfl

end

theorem toZ_pow_comb : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ)
    (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf),
    (∀ (L : HermLB p) (m : ℕ), (toZ (L.pow m) t (H _)).Isometric ((toZ L t (H _)).pow m)) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ),
      (toZ (ArInt.comb L n) t (H _)).Isometric (ArInt.comb (fun i => toZ (L i) t (H _)) n) := by
  intro k _ X p t H
  refine ⟨fun L m => HermLB.icls_eq_iff.1 ?_, fun ι _ L n => HermLB.icls_eq_iff.1 ?_⟩
  · rw [← toZClass_icls H, HermLB.icls_pow, HermLB.icls_pow, map_nsmul, toZClass_icls H]

  · rw [← toZClass_icls H, ArInt.icls_comb, ArInt.icls_comb, map_sum]
    simp only [map_zsmul, toZClass_icls H]

end GlobalTheory.CompanionTheory.Ar.BaseZ
