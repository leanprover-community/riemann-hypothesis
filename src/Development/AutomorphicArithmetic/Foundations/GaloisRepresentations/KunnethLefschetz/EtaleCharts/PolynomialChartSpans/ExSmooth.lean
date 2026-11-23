module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpChart2
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpOff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CoordEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DChartEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem stdSmooth_of_bijective {A B σ : Type} [CommRing A] [CommRing B] [Fintype σ] {d : ℕ}
    (hd : Fintype.card σ = d) (φ : A →+* B) (y : σ → B)
    (hb : Function.Bijective (MvPolynomial.eval₂Hom φ y)) :
    φ.IsStandardSmoothOfRelativeDimension d := by
  have h0 : (algebraMap A (MvPolynomial (Fin d) A)).IsStandardSmoothOfRelativeDimension d :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := d)).mpr
      (GlobalTheory.CompanionTheory.Ar.LieInh.stdSmooth_mvPolynomial A d)
  let e₁ : MvPolynomial (Fin d) A ≃+* MvPolynomial σ A :=
    (MvPolynomial.renameEquiv A (Fintype.equivFinOfCardEq hd).symm).toRingEquiv
  let e₂ : MvPolynomial σ A ≃+* B := RingEquiv.ofBijective _ hb
  have hφ : φ = (e₁.trans e₂).toRingHom.comp (algebraMap A (MvPolynomial (Fin d) A)) := by
    ext a
    simp [e₁, e₂, MvPolynomial.algebraMap_eq]
  rw [hφ]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ h0

private theorem comap_surjective_of_bijective {A B σ : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (y : σ → B) (hb : Function.Bijective (MvPolynomial.eval₂Hom φ y)) :
    Function.Surjective (PrimeSpectrum.comap φ) := by
  let e : MvPolynomial σ A ≃+* B := RingEquiv.ofBijective _ hb
  let ρ : B →+* A := (MvPolynomial.eval₂Hom (RingHom.id A) fun _ => 0).comp e.symm.toRingHom
  have hρ : ρ.comp φ = RingHom.id A := by
    ext a
    have : e.symm (φ a) = MvPolynomial.C a :=
      e.symm_apply_eq.2 (by simp [e])
    simp [ρ, this]
  intro p
  refine ⟨PrimeSpectrum.comap ρ p, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, hρ, PrimeSpectrum.comap_id]

private theorem exists_apply_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hs : Function.Surjective (PrimeSpectrum.comap (f.appLE U V e).hom)) {y : Y} (hy : y ∈ U) :
    ∃ x, f x = y := by
  obtain ⟨p, rfl⟩ : y ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hy
  obtain ⟨q, rfl⟩ := hs p
  refine ⟨hV.fromSpec q, ?_⟩
  have h := congr($(IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e) q)
  simp only [Scheme.Hom.comp_apply] at h
  exact h.symm

private theorem isProper_snd {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (hf : IsProper f) :
    IsProper (pullback.snd f g) :=
  haveI := hf; inferInstance

private theorem exists_chart {R : Type} [CommRing R] {Z W : Sch R} (d : ℕ) [IsSeparated Z.hom]
    [SmoothOfRelativeDimension (d + 1) Z.hom] (π : W ⟶ XX Z) (hπ : IsBl π) (z : Z.left) :
    ∃ (c : DChart Z (d + 1)) (_ : BChart π c.N c.s), (dg Z).left z ∈ c.N := by
  obtain ⟨U, u, hz, hc⟩ := coordEx R Z (d + 1) z
  obtain ⟨c, -, -, hN⟩ := (dChartEx R Z (d + 1)).1 U u hc z hz
  exact ⟨c, (blChart R π hπ (d + 1) c).some, hN⟩

theorem exSmooth : ExSmooth := by
  intro R _ _ Z W d _ _ π hπ
  haveI : Smooth Z.hom := SmoothOfRelativeDimension.smooth (d + 1) Z.hom
  refine ⟨⟨fun x => ?_⟩, ?_, ⟨fun z => ?_⟩⟩
  · obtain ⟨c, b, hN⟩ := exists_chart d π hπ ((exG π).left x)
    have e : (exI π).left ≫ π.left = (exG π).left ≫ (dg Z).left := pullback.condition
    have hW : (exI π).left x ∈ π.left ⁻¹ᵁ c.N := by
      have h := congr($e x)
      simp only [Scheme.Hom.comp_apply] at h
      change π.left ((exI π).left x) ∈ c.N
      rw [h]
      exact hN
    rw [← b.cov] at hW
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hW
    obtain ⟨hA, hB, -, h, hbij⟩ := exChart R π (d + 1) c b j
    exact ⟨_, hA, _, hB, hj, h, stdSmooth_of_bijective (by simp [Fintype.card_subtype_compl]) _ _ hbij⟩
  · exact isProper_snd π.left (dg Z).left (blOff R π hπ).1
  · obtain ⟨c, b, hN⟩ := exists_chart d π hπ z
    obtain ⟨hA, hB, -, h, hbij⟩ := exChart R π (d + 1) c b 0
    exact exists_apply_eq _ hA hB h (comap_surjective_of_bijective _ _ hbij) hN

end UpperTheory.Gal.KunnethLefschetz.G
