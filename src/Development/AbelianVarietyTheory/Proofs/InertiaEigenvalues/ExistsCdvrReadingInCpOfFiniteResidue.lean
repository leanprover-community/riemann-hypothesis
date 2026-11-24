module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegral
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUTestNontrivial, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUTestNontrivial =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUTestNontrivial", "h": "module\n\npublic import Mathlib.NumberTheory.Padics.Complex\npublic import Mathlib.RingTheory.DiscreteValuationRing.Basic\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap\npublic import Mathlib.NumberTheory.NumberField.Basic\npublic import Mathlib.NumberTheory.NumberField.CMField\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DegenerateTest

section Pull

variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
  {L : LB G.left} {L' : LB G'.left} {L'' : LB G''.left}

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}


open IsLocalRing in
theorem exists_padic_embedding (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (h : Finite (ResidueField V)) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (c : FractionRing V →+* PadicAlgCl p),
      ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  obtain ⟨p, _, K₀, e, e₀, -, he⟩ := completeDVR_eq_integralClosure_padicInt.1 V (FractionRing V) h
  refine ⟨p, inferInstance, (algebraMap K₀ (PadicAlgCl p)).comp e.toRingHom, fun x => ?_⟩
  refine (mem_integralClosure_padicInt_iff K₀ (e x)).symm.trans ⟨fun hx => ⟨e₀.symm ⟨e x, hx⟩, ?_⟩, ?_⟩
  · apply e.injective
    rw [he, e₀.apply_symm_apply]
  · rintro ⟨v, rfl⟩
    rw [he]
    exact (e₀ v).2

end GlobalTheory.DegenerateTest

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUTestNontrivial =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt\npublic import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUTestNontrivial\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegral\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.ReadExist

theorem exists_algCl {p : ℕ} [Fact p.Prime] {z : ℂ_[p]} (hz : IsAlgebraic ℚ_[p] z) :
    ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = z := by
  have h1 : IsIntegral (PadicAlgCl p) z := (hz.tower_top (PadicAlgCl p)).isIntegral
  have h2 : (minpoly (PadicAlgCl p) z).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible h1)
  exact minpoly.mem_range_of_degree_eq_one _ _ h2

theorem exists_factor_algCl {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) :
    ∃ b : F →+* PadicAlgCl p, ∀ x, algebraMap (PadicAlgCl p) ℂ_[p] (b x) = φ x := by
  have hex : ∀ x : F, ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = φ x := fun x => by
    apply exists_algCl
    have h1 : IsAlgebraic ℚ (φ x) := by
      have := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom
      simpa using this
    exact h1.tower_top ℚ_[p]
  choose f hf using hex
  have hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p]) :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_mul, hf, hf, hf]; exact map_mul φ x y
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_add (f := _), hf, hf, hf]; exact map_add φ x y

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_inv {x : K} (hx : x ≠ 0) : vV V x⁻¹ = - vV V x := by
  have h := vV_mul (V := V) hx (inv_ne_zero hx)
  have h1 : vV V (1 : K) = 0 := by simp [vV]
  rw [mul_inv_cancel₀ hx, h1] at h
  omega

theorem norm_lt_one_iff_vV_pos {C : Type} [NormedField C] (c : K →+* C)
    (hn : ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V K)) {y : K} (hy : y ≠ 0) :
    ‖c y‖ < 1 ↔ 0 < vV V y := by
  have key : ∀ x, ‖c x‖ ≤ 1 ↔ 0 ≤ vV V x := fun x =>
    (hn x).trans (Set.mem_range.trans (GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff (V := V) x))
  have h0 : 0 < ‖c y‖ := norm_pos_iff.2 ((map_ne_zero c).2 hy)
  have hi := key y⁻¹
  rw [map_inv₀, norm_inv, vV_inv hy, inv_le_one₀ h0] at hi
  constructor
  · intro h
    by_contra h'
    have := hi.2 (by omega)
    linarith
  · intro h
    by_contra h'
    have := hi.1 (not_lt.1 h')
    omega

end Val

theorem mem_iff_vLa_pos {F : Type} [Field F] [NumberField F] (la : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F)
    (hx : (x : F) ≠ 0) : x ∈ la.asIdeal ↔ 0 < vLa la (x : F) := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  have h0 : la.valuation F (x : F) ≠ 0 := (la.valuation F).ne_zero_iff.2 hx
  have e := WithZero.log_lt_log h0 one_ne_zero
  rw [WithZero.log_one] at e
  change _ ↔ 0 < -WithZero.log (la.valuation F (x : F))
  rw [← e]
  omega

theorem exists_isReading : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p])
    (T : CDVR) (io : F →+* T.Fr) (e : ℕ), OverLa (placeAt φ) T.V io e → T.FinRes →
    ∃ k : T.Fr →+* ℂ_[p], IsReading φ T io k := by
  intro p _ F _ _ φ T io e ho hT
  obtain ⟨q, hq, c, hn⟩ := GlobalTheory.DegenerateTest.exists_padic_embedding T.V hT

  have ha : ∀ x : 𝓞 F, ‖c (io (x : F))‖ < 1 ↔ x ∈ (placeAt φ).asIdeal := by
    intro x
    by_cases hx : (x : F) = 0
    · have hx' : x = 0 := by exact_mod_cast hx
      subst hx'
      simp
    rw [norm_lt_one_iff_vV_pos c hn ((map_ne_zero io).2 hx), ho.2, mem_iff_vLa_pos _ x hx]
    constructor
    · intro h
      exact pos_of_mul_pos_right h (by positivity)
    · intro h
      exact mul_pos (by exact_mod_cast ho.1) h

  have hqp : q = p := by
    have h1 := (ha (p : 𝓞 F)).2 (natCast_mem_placeAt φ)
    have e1 : c (io (((p : ℕ) : 𝓞 F) : F)) = algebraMap ℚ_[q] (PadicAlgCl q) (p : ℚ_[q]) := by simp
    rw [e1, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
    exact (Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).1 h1
  subst hqp
  obtain ⟨b, hb⟩ := exists_factor_algCl φ
  have hbn : ∀ x, ‖b x‖ = ‖φ x‖ := fun x => by
    rw [← hb, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  obtain ⟨g, hg⟩ := GlobalTheory.EmbThroughCompletion.exists_conj (c.comp io) b
    (GlobalTheory.EmbThroughCompletion.norm_lt_one_iff (placeAt φ) _ _ ha
      (fun x => by rw [hbn]; exact (mem_placeAt φ x).symm))
  refine ⟨(algebraMap (PadicAlgCl q) ℂ_[q]).comp ((g : PadicAlgCl q →+* PadicAlgCl q).comp c), ?_, ?_⟩
  · intro a
    simp only [RingHom.comp_apply]
    have := hg a
    simp only [RingHom.comp_apply] at this
    rw [RingHom.coe_coe, this, hb]
  · intro x
    simp only [RingHom.comp_apply]
    rw [← PadicComplex.coe_eq, PadicComplex.norm_extends, RingHom.coe_coe, ← PadicAlgCl.spectralNorm_eq,
      ← spectralNorm_eq_of_equiv g, PadicAlgCl.spectralNorm_eq, hn]
    rfl

end GlobalTheory.GeoTie.ReadExist

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue =====
