module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

private lemma relDim_eq_of_ringHom {R S : Type} [CommRing R] [CommRing S] [Nontrivial S] (f : R →+* S)
    {m n : ℕ} (hm : f.IsStandardSmoothOfRelativeDimension m)
    (hn : f.IsStandardSmoothOfRelativeDimension n) : m = n := by
  letI := f.toAlgebra
  have e₁ : Module.rank S Ω[S⁄R] = m :=
    @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ m hm
  have e₂ : Module.rank S Ω[S⁄R] = n :=
    @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ n hn
  exact_mod_cast e₁.symm.trans e₂

private lemma exists_nontrivial_away {S : Type} [CommRing S] [Nontrivial S] (s : Set S)
    (hs : Ideal.span s = ⊤) : ∃ t ∈ s, Nontrivial (Localization.Away t) := by
  by_contra hne
  push_neg at hne
  have hsub : s ⊆ nilradical S := by
    intro t ht
    haveI : Subsingleton (Localization.Away t) := hne t ht
    have h0 : algebraMap S (Localization.Away t) 1 = algebraMap S (Localization.Away t) 0 :=
      Subsingleton.elim _ _
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) _).1 h0
    obtain ⟨k, rfl⟩ := hc
    exact ⟨k, by simpa using hc'⟩
  have hle := Ideal.span_le.2 hsub
  rw [hs, top_le_iff] at hle
  have h1 : (1 : S) ∈ nilradical S := hle ▸ Submodule.mem_top
  obtain ⟨k, hk⟩ := h1
  simp at hk

private lemma relDim_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {m n : ℕ} (hm : SmoothOfRelativeDimension m f)
    (hn : SmoothOfRelativeDimension n f) (x : X) : m = n := by
  obtain ⟨U, hU, V, hV, hx, e, hmU⟩ := hm.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, hst⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨t, ht, hnt⟩ := exists_nontrivial_away s hs
  have hm' := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).2
    (Localization.Away t) t _ hmU
  exact relDim_eq_of_ringHom _ hm' (hst t ht)

theorem dimUniq_of : DimUniq := by
  intro Z s d d' hd hd' hZ
  obtain ⟨z⟩ := hZ
  exact relDim_eq s hd hd' z

end UpperTheory.Gal.FixZ
