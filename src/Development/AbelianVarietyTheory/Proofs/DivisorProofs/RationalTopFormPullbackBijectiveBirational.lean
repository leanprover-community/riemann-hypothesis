module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

noncomputable section

namespace GlobalTheory.TopForm

theorem bijective_formMap_of_bijective {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    {α : k →+* A} {β : k →+* B} (D : ℕ) (ρ : A →+* B) (h : ρ.comp α = β)
    (hρ : Function.Bijective ρ) : Function.Bijective (TopForm.formMap D ρ h) := by
  let e : A ≃+* B := RingEquiv.ofBijective ρ hρ
  let σ : B →+* A := e.symm.toRingHom
  have e1 : σ.comp ρ = RingHom.id A := RingHom.ext fun a => e.symm_apply_apply a
  have e2 : ρ.comp σ = RingHom.id B := RingHom.ext fun b => e.apply_symm_apply b
  have h' : σ.comp β = α := by
    rw [← h, ← RingHom.comp_assoc, e1, RingHom.id_comp]
  refine Function.bijective_iff_has_inverse.mpr ⟨TopForm.formMap D σ h', fun x => ?_, fun y => ?_⟩
  · rw [formMap_formMap ρ σ (RingHom.id A) e1 h h' (RingHom.id_comp α)]
    exact formMap_of_eq_id _ rfl _ x
  · rw [formMap_formMap σ ρ (RingHom.id B) e2 h' h (RingHom.id_comp β)]
    exact formMap_of_eq_id _ rfl _ y

end GlobalTheory.TopForm

namespace GlobalTheory.EtaleKlt

theorem ratPull_bijective_of_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ n : ℕ,
      Function.Bijective (EtaleKlt.ratPull p s n) := by
  intro k _ X Y _ _ p s _ hs n
  exact TopForm.bijective_formMap_of_bijective n _ (functionFieldMap_comp_constFn p s) hs

end GlobalTheory.EtaleKlt
