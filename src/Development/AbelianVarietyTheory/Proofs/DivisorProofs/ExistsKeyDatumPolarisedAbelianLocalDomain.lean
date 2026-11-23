module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSectionNonzeroNearTwoStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieFreeNearTwoPrimesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem exists_keyIn_local : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W]
    (P : PolAV (Sp W)), 1 ≤ P.g → ∃ y : KeyIn W, y.P = P := by
  intro W _ _ _ _ P hg
  have hL := GlobalTheory.abelianSchemeLaws_all
  let m : PrimeSpectrum W := IsLocalRing.closedPoint W
  obtain ⟨th, a, ha, -, hth⟩ := GlobalTheory.T.exists_principalPolarization_section_nonzero_near_two_primes hL.1 hL.2 W P m m
  have c : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨b, hb, -, v, hv⟩ := GlobalTheory.T.exists_lieBasis_away_avoiding_two_primes W P.A P.g P.smoothDim m m
  have hbu : IsUnit b := (IsLocalRing.mem_maximalIdeal b).not.mp hb |> not_not.mp
  let g : Localization.Away b →+* W := IsLocalization.Away.lift (g := RingHom.id W) b hbu
  have hgf : g.comp (algebraMap W (Localization.Away b)) = RingHom.id W := by
    ext x; simp [g]
  have h₁ := isGrpPullback_pullback P.A (spMap (algebraMap W (Localization.Away b)))
  have hA₁ := Out.TLinPf.isAb_pullback (spMap (algebraMap W (Localization.Away b))) P.A P.isAb
  have c₁ := hA₁.comm
  have e : spMap g ≫ spMap (algebraMap W (Localization.Away b)) = 𝟙 (Sp W) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgf, CommRingCat.ofHom_id, Spec.map_id]
  have w₁ : 𝟙 P.A.left ≫ P.A.hom = (P.A.hom ≫ spMap g) ≫ spMap (algebraMap W (Localization.Away b)) := by
    rw [Category.assoc, e]; simp
  haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 P.A))
  have hid : IsGrpPullback P.A P.A (𝟙 _) (𝟙 P.A.left) := isGrpPullback_of_iso (Iso.refl P.A)
  have h₂ : IsGrpPullback P.A _ (spMap g) (h₁.1.lift _ _ w₁) :=
    IsGrpPullback.cancel h₁ (hid.congr e.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange _ W g _ P.A _ h₂ hA₁.smooth P.g v hv
  obtain ⟨rig, hr⟩ := P.rigid
  refine ⟨⟨P, hg, rig, hr, th, fun s => hth s fun h => ?_, v', hb'⟩, rfl⟩
  have hs : s.asIdeal ≤ IsLocalRing.maximalIdeal W := IsLocalRing.le_maximalIdeal s.isPrime.ne_top
  exact ha (hs h)

end GlobalTheory.MBLow
