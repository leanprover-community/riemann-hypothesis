module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftFormallySmoothSquareZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRangeOfIdempotentAlgHomStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Obs

theorem retractLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.Smooth R B'] (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀] (i : B₀ →ₐ[R₀] B₀') (r : B₀' →ₐ[R₀] B₀), (∀ x, r (i x) = x) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ B₀ _ _ i r hri
  obtain ⟨e, he, hpe⟩ := GlobalTheory.T.exists_idempotent_lift_formallySmooth_squareZero R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' (i.comp r) (fun x ↦ by simp [hri])
  have hmem : ∀ x ∈ I.map (algebraMap R B'), e.rangeRestrict x ∈ I.map (algebraMap R e.range) := by
    intro x hx
    have hle : I.map (algebraMap R B') ≤ (I.map (algebraMap R e.range)).comap (e.rangeRestrict : B' →+* e.range) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro y hy
      simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      rw [AlgHom.commutes]
      exact Ideal.mem_map_of_mem _ hy
    exact hle hx
  refine ⟨e.range, inferInstance, inferInstance,
    ((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B'), ?_, ?_, ?_, GlobalTheory.T.smooth_range_of_idempotent_algHom R B' e he⟩
  · intro c b
    show r (p' ((c • b : e.range) : B')) = π c • r (p' (b : B'))
    rw [Subalgebra.coe_smul, hs' c (b : B'), map_smul]
  · intro y
    obtain ⟨b, hb⟩ := hp' (i y)
    refine ⟨⟨e b, e.mem_range_self b⟩, ?_⟩
    show r (p' (e b)) = y
    rw [hpe, hb]
    simp [hri]
  · intro b
    constructor
    · intro h
      change r (p' (b : B')) = 0 at h
      obtain ⟨c, hc⟩ := b.2
      change e c = (b : B') at hc
      have hfix : e (b : B') = b := by rw [← hc, he]
      have h0 : p' (b : B') = 0 := by
        rw [← hfix, hpe]
        simp [h]
      have hb : e.rangeRestrict (b : B') = b := Subtype.ext hfix
      rw [← hb]
      exact hmem _ ((hker' _).mp h0)
    · intro h
      have hle : I.map (algebraMap R e.range) ≤ RingHom.ker (((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B')) := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        have hx0 : π x = 0 := by rw [← RingHom.mem_ker, hk]; exact hx
        show r (p' (algebraMap R B' x)) = 0
        rw [hs'.map_algebraMap, hx0, map_zero, map_zero]
      exact hle h

end GlobalTheory.Obs
