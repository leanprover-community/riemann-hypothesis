module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryExtendingIsotropicShearStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicShearOfAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionOppositeCongrModStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOppositeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerModEqOrthogonalRangeShearAddNsmulStatement
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

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.LowFilt.exists_isometry_kerIs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ g : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ a, (∃ e, y (g a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ _ _ y n N hn hNn hC Z Z' h hrk hN hon
  have hN0 : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  have hinj := GlobalTheory.T.injective_mod_of_surjective_mod_opposite D y n hn Z Z' h hrk hon
  obtain ⟨σ, hσZ', hσid, hσy, hσN⟩ := GlobalTheory.T.exists_linear_section_opposite_congr_mod D y n N hn hNn Z Z' h hN hon
  obtain ⟨w, hw⟩ := exists_adjoint D σ
  obtain ⟨t, ht, hiso, hdvd⟩ := GlobalTheory.T.exists_isotropic_shear_of_adjoint D y n N hn hNn hC Z Z' h σ w hσZ' hσid hσy hσN hw hinj
  have ht' : ∀ z : Z, t z - z ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hze⟩ := ht z
    rw [hze, add_sub_cancel_left]
    exact (perp D Z').nsmul_mem he N
  have hker := GlobalTheory.T.ker_mod_eq_orthogonal_range_shear_add_nsmul D y n hn Z Z' h hon t ht' hiso hdvd
  obtain ⟨g, hg, hgN, hgt⟩ := GlobalTheory.T.exists_isometry_extending_isotropic_shear D N hN0 Z Z' h t ht hiso
  refine ⟨equivOfIsometry D g hg, hg, hgN, fun a => ?_⟩
  simp only [equivOfIsometry_apply]
  rw [hker (g a)]
  constructor
  · rintro ⟨b, hb, e, he⟩
    set G := equivOfIsometry D g hg
    have hG : ∀ x, G x = g x := fun x => rfl
    refine ⟨G.symm b, fun z hz => ?_, G.symm e, ?_⟩
    · have := hb (t ⟨z, hz⟩) ⟨⟨z, hz⟩, rfl⟩
      rw [← hgt ⟨z, hz⟩, ← G.apply_symm_apply b, hG, hg] at this
      exact this
    · apply G.injective
      rw [map_add (f := _), map_nsmul, G.apply_symm_apply, G.apply_symm_apply, hG, he]
  · rintro ⟨b, hb, e, rfl⟩
    refine ⟨g b, ?_, g e, by rw [map_add (f := _), map_nsmul]⟩
    rintro _ ⟨z, rfl⟩
    rw [← hgt z, hg]
    exact hb z z.2
