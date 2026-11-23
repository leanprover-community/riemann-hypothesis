module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionTransportPullbackIsoStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem Trait.exists_expBy_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
      (F₀ : IntFam (maximalIdeal R) D.toPre k), ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀ := by
  intro R _ _ _ hR D C k hk W _ _ _ T F₀
  have := hR.2
  have hW := T.cdvr
  have := hW.1
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have cW : CharZero W := charZero_of_injective_ringHom T.inj
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  obtain ⟨F', hF'⟩ := GlobalTheory.Mum.exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc k F₀
  obtain ⟨σ', hσ'⟩ := GlobalTheory.Mum.IntFam.exists_expandsAt W ⟨bW, cW⟩ T.D' T.A T.G T.U hGs k hk F'
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lineBundlePowSection_transport_pullbackIso C.P.L.L T.U.LG.L T.β T.ℓ C.P.L.isLB T.U.LG.isLB T.ℓ_gen k σ'
  refine ⟨σ, σ', F'.f, fun Z r z J J' hJ hJ' => ?_, hF', hσ'⟩
  have h1 : scal T.G.hom (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  rw [hσ Z r z J J' hJ hJ', h1, gs_eq r z ⊤ (by trivial), map_one, map_one, _root_.one_mul]

end GlobalTheory.Mum
