module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory

theorem encard_fibre_eq_encard_ringHom : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), IsAffineOpen U →
    IsAffineOpen (π ⁻¹ᵁ U) → ∀ (σ : k →+* ℂ) (y : GlobalTheory.CxPts p σ) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ U),
    (GlobalTheory.Points.PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard =
      {ψ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ | ψ.comp (π.app U).hom = GlobalTheory.CxPts.evHom hy}.encard := by
  intro k _ X Y p q π hπ U hU hV σ y hy
  have hmem : ∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z = y →
      z ∈ CxPts.ptsIn q σ (π ⁻¹ᵁ U) := by
    intro z hz
    have : PtsOver.map π hπ (spMap σ) z ∈ CxPts.ptsIn p σ U := hz ▸ hy
    exact this
  have hcomp : ∀ (z : CxPts q σ) (hz : PtsOver.map π hπ (spMap σ) z = y) (f : Γ(X, U)),
      CxPts.evHom (hmem z hz) ((π.app U).hom f) = CxPts.evHom hy f := by
    intro z hz f
    rw [← CxPts.ev_eq, ← CxPts.ev_eq, CxPts.ev_app π hπ U f z, hz]
  apply Set.encard_congr
  refine Equiv.ofBijective (fun z => ⟨CxPts.evHom (hmem z.1 z.2), RingHom.ext (hcomp z.1 z.2)⟩)
    ⟨?_, ?_⟩
  · rintro ⟨z, hz⟩ ⟨w, hw⟩ h
    have h' : CxPts.evHom (hmem z hz) = CxPts.evHom (hmem w hw) := congrArg Subtype.val h
    refine Subtype.ext (Subtype.ext (ext_of_valR hV (hmem z hz) (hmem w hw) fun f => ?_))
    rw [valR_eq _ _ (hmem z hz), valR_eq _ _ (hmem w hw)]
    exact congrArg (fun φ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ => φ f) h'
  · rintro ⟨ψ, hψ⟩
    have hψ' : ∀ f, ψ ((π.app U).hom f) = CxPts.evHom hy f := fun f => by
      rw [← RingHom.comp_apply, hψ]
    have h₀ : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ⁻¹ᵁ (π ⁻¹ᵁ U) :=
      le_preimage_specMap_fromSpec hV (CommRingCat.ofHom ψ)
    have hv : valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) h₀ =
        CommRingCat.ofHom ψ :=
      valMap_specMap_fromSpec hV (CommRingCat.ofHom ψ) h₀
    have e : (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ≫ π = y.1 := by
      refine ext_of_valR hU h₀ hy fun f => ?_
      rw [valR_comp, valR_eq _ _ h₀, hv, valR_eq _ _ hy]
      exact hψ' f
    let z : CxPts q σ := ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, by
      rw [← hπ, ← Category.assoc, e, y.2]⟩
    have hz : PtsOver.map π hπ (spMap σ) z = y := Subtype.ext e
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    change (valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) (hmem z hz)).hom = ψ
    rw [hv]
    rfl

end GlobalTheory
