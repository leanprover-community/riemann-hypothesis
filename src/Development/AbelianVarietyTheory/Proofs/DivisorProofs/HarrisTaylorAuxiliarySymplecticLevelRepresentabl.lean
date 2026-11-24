module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilledStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRepresentableSiegelBaseChaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoethStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiProjectiveOfFiniteOverCyclotomicAwayPullbStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem harrisTaylorModuli_symplecticLevel_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SDRep (Module.finrank ℤ D.La / 2) M e → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M := by
  intro p _ D R _ _ b N M e hN hNp hM hMo hMp hep _ hdual hSD
  obtain ⟨X, s, u, hku, -, hqs, huniv⟩ := hSD
  have hMR : IsUnit ((M : ℕ) : R) := b.unit M hMp
  have hqP : IsQProjOver (𝟙 _ ≫ pullback.snd (s ≫ spMap (Int.castRingHom (cycAway M)))
      (spMap (Int.castRingHom R))) :=
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs _ (𝟙 _) inferInstance
  rw [Category.id_comp] at hqP
  have hLN := GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian R _ _ hqP
  obtain ⟨Z, π, v, lev, hlev, hfin, hfwd, hback⟩ :=
    GlobalTheory.T.harrisTaylor_structures_representable_siegel_baseChange p D R b N (Module.finrank ℤ D.La / 2) M e hN hNp hM hMo hMp hep X s u hku hLN
  refine ⟨Z, π ≫ pullback.snd _ _, π ≫ pullback.fst _ _ ≫ s, v, lev, hlev,
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs Z π hfin, ?_⟩
  intro S t t₁ o l hl
  have heS : IsUnit ((e : ℕ) : Γ(S, ⊤)) := by
    have h := (b.unit e hep).map ((t.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using h
  obtain ⟨f₀, ⟨hf₀s, hf₀pb⟩, hf₀u⟩ :=
    huniv S t₁ (o.toSieg hl) heS (GlobalTheory.T.harrisTaylor_siegelObject_polarisationKernel_killed p D R b N S t o _ M t₁ l hl e hep hdual)
  obtain ⟨g, ⟨hg₁, hg₂, hgm⟩, hgu⟩ := hback S f₀ t t₁ o l hl hf₀pb
  refine ⟨g, ⟨hg₂, ?_, hgm⟩, ?_⟩
  · rw [← hf₀s, ← hg₁]
    simp only [Category.assoc]
  · rintro g' ⟨hg's, hg's₁, hg'm⟩
    have hfst : g' ≫ π ≫ pullback.fst _ _ = f₀ :=
      hf₀u _ ⟨by simpa only [Category.assoc] using hg's₁, hfwd S g' t t₁ o l hl hg'm⟩
    exact hgu g' ⟨hfst, hg's, hg'm⟩

end GlobalTheory.UPel.HT
