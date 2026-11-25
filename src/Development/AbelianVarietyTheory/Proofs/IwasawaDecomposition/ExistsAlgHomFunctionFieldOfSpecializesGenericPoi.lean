module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

noncomputable section

namespace GlobalTheory.FlagBundle

theorem exists_algHom_of_specializes_genericPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] [Algebra F K] (q : Sp K ⟶ Y.X),
      q (IsLocalRing.closedPoint K) ⤳ genericPoint Y.X → q ≫ Y.str = spMap (algebraMap F K) →
        ∃ ψ : Y.Fn →ₐ[F] K, q = spMap ψ.toRingHom ≫ (ratOf Y).pt := by
  intro F _ Y K _ _ q h hq
  let ψ₀ : Y.Fn →+* K := (Y.X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := .of K) q).hom
  have e : spMap ψ₀ ≫ (ratOf Y).pt = q := by
    change Spec.map (CommRingCat.ofHom ψ₀) ≫ Y.X.fromSpecStalk (genericPoint Y.X) = q
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo q
  have hc : ψ₀.comp (algebraMap F Y.Fn) = algebraMap F K := by
    have h1 : spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap (algebraMap F K) := by
      have hs := (ratOf Y).pt_s
      calc spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap ψ₀ ≫ spMap (algebraMap F Y.Fn) := by
            change Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap F Y.Fn))) = _
            rw [CommRingCat.ofHom_comp, Spec.map_comp]
        _ = spMap ψ₀ ≫ ((ratOf Y).pt ≫ (ratOf Y).s) := by rw [hs]
        _ = (spMap ψ₀ ≫ (ratOf Y).pt) ≫ (ratOf Y).s := (Category.assoc _ _ _).symm
        _ = q ≫ Y.str := by
            change (spMap ψ₀ ≫ (ratOf Y).pt) ≫ Y.str = q ≫ Y.str
            rw [e]
            rfl
        _ = spMap (algebraMap F K) := hq
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  refine ⟨{ ψ₀ with commutes' := fun a => congrArg (fun g : F →+* K => g a) hc }, ?_⟩
  exact e.symm

end GlobalTheory.FlagBundle
