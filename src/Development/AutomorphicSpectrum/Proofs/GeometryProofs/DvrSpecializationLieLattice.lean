module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem fibAt_lat_eq_stdLat : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Em : Type) [AddCommGroup Em] [Module Ω Em]
    (M : LieModel G ξ Em) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (x : Sp K ⟶ X) (z : Sp V ⟶ X) (h₁ : genPt ξ ⤳ centre x) (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K) (g : ℕ)
    (ℓ : Fin g → Em) (MX : LieModel G x (Fin g → K)) (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z) (Fin g → K)),
    spMap (algebraMap V K) ≫ z = x → (∀ e, (MC.pt e).left = (MX.pt e).left) → IsCptGen ξ →
    regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ →
    (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) →
    M.lat.IsFrameAt ℓ ⟨_, h₂⟩ →
    (∀ w : Fin g → regAt ξ ⟨_, h₁⟩, M.ValAt x (comb ℓ w) (MX.pt (fun i => ψ (w i)))) →
    M.fibAt M.lat z MC = stdLat V K g := by
  intro X G _ Ω _ ξ Em _ _ M V K _ _ _ _ _ _ x z h₁ h₂ ψ g ℓ MX MC hx hpt hξ hle hint hfr hval
  subst hx
  have hMC : ∀ e, MC.pt e = MX.pt e := fun e => Over.OverMorphism.ext (hpt e)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨h, e, he, hv⟩
    have he' : e ∈ M.lat ⟨_, h₂⟩ := he
    rw [hfr.2] at he'
    obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    have hc : comb ℓ (fun i => (⟨(r i : Ω), hle (r i).2⟩ : regAt ξ ⟨_, h₁⟩)) = ∑ i, r i • ℓ i := rfl
    have h3 := hval (fun i => ⟨(r i : Ω), hle (r i).2⟩)
    rw [hc] at h3
    have e1 := LieModel.ValAt.unique hξ hv h3
    rw [hMC] at e1
    have e2 := MX.inj e1
    intro i
    rw [e2]
    exact hint _ _ (r i).2
  · intro w hw
    have hw' : ∀ i, w i ∈ (algebraMap V K).range := hw
    choose v hv using hw'
    have hsum : w = ∑ i, v i • (Pi.single i 1 : Fin g → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hv]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h₂, ℓ i, ?_, ?_⟩)
    · rw [hfr.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    · have h3 := hval (Pi.single i 1)
      have hc : comb ℓ (Pi.single i 1 : Fin g → regAt ξ ⟨_, h₁⟩) = ℓ i := by
        unfold comb
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      have hs : (fun j => ψ ((Pi.single i 1 : Fin g → regAt ξ ⟨_, h₁⟩) j)) = (Pi.single i 1 : Fin g → K) := by
        ext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [hc, hs] at h3
      rw [hMC]
      exact h3

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
