module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Mathlib.Tactic.Basify
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractio, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractioStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundle, Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundleStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqZpowOfFieldPointDomain, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractio =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractio", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus\npublic import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsConst

theorem exists_factor_generic {R : Type} [CommRing R] [IsDomain R] {k : Type} [Field k] (τ : Sp k ⟶ Sp R)
    (w : Sp k) (hw : τ w = (⊥ : PrimeSpectrum R)) : ∃ κ : FractionRing R →+* k, τ = spMap κ ≫ jK R := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective τ
  have hφ : Function.Injective φ.hom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : PrimeSpectrum.comap φ.hom w = ⊥ := hw
    have h2 : a ∈ (PrimeSpectrum.comap φ.hom w).asIdeal := by
      show φ.hom a ∈ (w : PrimeSpectrum k).asIdeal
      rw [ha]; exact Ideal.zero_mem _
    rw [h1] at h2
    exact h2
  refine ⟨IsFractionRing.lift hφ, ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp

theorem exists_section_generic {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] {n : ℕ} (hA : IsAbelianScheme A) (hn : IsUnit (n : Γ(Sp R, ⊤)))
    (h : TorsRat A n) {K : Type} [Field K] [IsAlgClosed K] (κ : FractionRing R →+* K)
    (x : Over.mk (spMap κ ≫ jK R) ⟶ A) (hx : x ^ n = 1) :
    ∃ σ : 𝟙_ (Over (Sp R)) ⟶ A, σ ^ n = 1 ∧ toUnit _ ≫ σ = x := by
  obtain ⟨x₀, h₀⟩ := h K κ x hx
  let ρ : Over.mk (spMap κ ≫ jK R) ⟶ Over.mk (jK R) := Over.homMk (spMap κ) rfl
  have e₀ : x = ρ ≫ x₀ := Over.OverMorphism.ext h₀
  have hfl : Flat (spMap κ) := by
    letI := κ.toAlgebra
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsu : Surjective (spMap κ) := ⟨fun p => ⟨Classical.arbitrary _, Subsingleton.elim (α := Sp (FractionRing R)) _ _⟩⟩
  have hepi : Epi ρ.left := Flat.epi_of_flat_of_surjective (spMap κ)
  have hx₀ : x₀ ^ n = 1 := by
    have : ρ ≫ x₀ ^ n = ρ ≫ 1 := by rw [MonObj.comp_pow, ← e₀, hx, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi ρ.left).1 congr(($this).left))
  have hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := fun p => by
    refine ⟨inferInstance, ?_⟩
    have : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
    have h := StructureSheaf.IsLocalization.to_stalk R p
    exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _
      (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
  have j₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have j₂ : Flat (jK R) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have j₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro a ha
    have : a = 0 := IsFractionRing.injective R (FractionRing R) (ha.trans (map_zero _).symm)
    rw [this]; exact Ideal.zero_mem _)⟩
  have hp : IsProper A.hom := hA.proper
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_pow_eq_one hT (jK R) A n hn _ x₀ hx₀ (𝟙 _) (Category.id_comp _)
  let σ : 𝟙_ (Over (Sp R)) ⟶ A := Over.homMk s hs₁
  have e₁ : toUnit (Over.mk (jK R)) ≫ σ = x₀ := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    exact hs₂.trans (Category.id_comp _)
  refine ⟨σ, ?_, ?_⟩
  · have : toUnit (Over.mk (jK R)) ≫ σ ^ n = toUnit (Over.mk (jK R)) ≫ 1 := by
      rw [MonObj.comp_pow, e₁, hx₀, MonObj.comp_one]
    apply Over.OverMorphism.ext
    have h2 := congr(($this).left)
    rw [Over.comp_left, Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at h2
    have : AlgebraicGeometry.IsReduced (𝟙_ (Over (Sp R))).left := inferInstanceAs (AlgebraicGeometry.IsReduced (Sp R))
    exact ext_of_isDominant_of_isSeparated A.hom (by rw [Over.w, Over.w]) (jK R) h2
  · rw [e₀, ← e₁, ← Category.assoc, comp_toUnit]

theorem exists_section_of_torsRat : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  intro R _ _ _ _ A _ _ n hA hn h K _ _ t x hx
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion A hn'
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion A n x hx
  obtain ⟨w⟩ : Nonempty (Sp K) := inferInstance
  have hs : (⊥ : PrimeSpectrum R) ⤳ (torsion A n).hom (y.left w) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨z, hz, ez⟩ := Flat.generalizingMap (torsion A n).hom hs
  let k := AlgebraicClosure ((torsion A n).left.residueField z)
  let u : Sp k ⟶ (torsion A n).left :=
    spMap (algebraMap ((torsion A n).left.residueField z) k) ≫ (torsion A n).left.fromSpecResidueField z
  obtain ⟨v⟩ : Nonempty (Sp k) := inferInstance
  have hu : u v = z := by
    have : u v ∈ Set.range ((torsion A n).left.fromSpecResidueField z) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨κ, hκ⟩ := exists_factor_generic (u ≫ (torsion A n).hom) v
    ((Scheme.Hom.comp_apply _ _ _).trans (by rw [hu]; exact ez))
  let u' : Over.mk (spMap κ ≫ jK R) ⟶ torsion A n := Over.homMk u hκ
  obtain ⟨σ, hσ, eσ⟩ := exists_section_generic A hA hn' h κ (u' ≫ torsion.ι A n) (by
    rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one])
  obtain ⟨C, hC, hCz⟩ := TorsionCover.exists_clopen_eq_one A hA hn'
    (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) (by
      rw [mul_pow, inv_pow, ← MonObj.comp_pow, hσ, MonObj.comp_one, LatticeTorsion.torsionι_pow_eq_one, inv_one,
        _root_.mul_one])
  have key : ∀ (T : Over (Sp R)) (a : T ⟶ torsion A n),
      a ≫ (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) = 1 ↔ toUnit T ≫ σ = a ≫ torsion.ι A n := fun T a => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, mul_inv_eq_one, eq_comm]
  have hzC : z ∈ C := (hCz _ u').1 ((key _ _).2 eσ) ⟨v, hu⟩
  have hyC : y.left w ∈ C := hz.mem_closed hC.isClosed hzC
  refine ⟨σ, hσ, ?_⟩
  rw [← hy]
  refine (key _ _).1 ((hCz _ y).2 ?_)
  rintro _ ⟨w', rfl⟩
  rwa [Subsingleton.elim (α := Sp K) w' w]

end GlobalTheory.TorsConst
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractio =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractioStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractioStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractio\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractioStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundle =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundle", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundle =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundleStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundleStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundle\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundleStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqZpowOfFieldPointDomain =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqZpowOfFieldPointDomain", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs\nimport Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds\nimport Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural\nimport Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WeilRoot

theorem eq_zpow_of_map_eq {O K : Type} [CommRing O] [IsDomain O] [Field K] (κ : O →+* K) {N : ℕ} (hN : 0 < N)
    (hu : IsUnit (N : O)) {ζ w : Oˣ} (hζ : IsPrimitiveRoot ζ N) (hw : w ^ N = 1) (m : ℤ)
    (h : Units.map κ.toMonoidHom w = Units.map κ.toMonoidHom (ζ ^ m)) : w = ζ ^ m := by
  have : NeZero N := ⟨hN.ne'⟩
  set y : Oˣ := w * (ζ ^ m)⁻¹ with hy
  have hyN : y ^ N = 1 := by
    rw [hy, _root_.mul_pow, hw, _root_.one_mul, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hζ.pow_eq_one, one_zpow, inv_one]
  have hζ' : IsPrimitiveRoot (ζ : O) N := IsPrimitiveRoot.coe_units_iff.2 hζ
  obtain ⟨i, hi, hiy⟩ := hζ'.eq_pow_of_pow_eq_one (ξ := (y : O)) (by rw [← Units.val_pow_eq_pow_val, hyN, Units.val_one])
  have hκ : IsPrimitiveRoot (κ ζ) N := by
    have : NeZero (N : K) := ⟨by simpa using (hu.map κ).ne_zero⟩
    rw [← (Polynomial.isRoot_cyclotomic_iff (R := K) (n := N)), ← Polynomial.map_cyclotomic N κ]
    exact (hζ'.isRoot_cyclotomic hN).map κ
  have hκy : κ (y : O) = 1 := by
    have h' : κ (w : O) = κ ((ζ ^ m : Oˣ) : O) := congrArg (fun u : Kˣ => (u : K)) h
    rw [hy, Units.val_mul, map_mul, h', ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hi0 : i = 0 := by
    have h1 : κ (ζ : O) ^ i = 1 := by rw [← map_pow, hiy, hκy]
    have := hκ.dvd_of_pow_eq_one i h1
    exact Nat.eq_zero_of_dvd_of_lt this hi
  have hy1 : y = 1 := Units.ext (by rw [← hiy, hi0, pow_zero, Units.val_one])
  rw [hy] at hy1
  exact mul_inv_eq_one.1 hy1

end GlobalTheory.WeilRoot
end

noncomputable section
namespace GlobalTheory.WeilRoot

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem weilIs_zpow_of_fieldPoint : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), IsPPol A P → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (ζ : Oˣ), IsPrimitiveRoot ζ N → ∀ (m : ℤ) (K : Type) [Field K] (κ : O →+* K), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap κ)) ≫ u) (toUnit (Over.mk (spMap κ)) ≫ v) (unitOn (Units.map κ.toMonoidHom (ζ ^ m))) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom (ζ ^ m))) := by
  intro O _ _ A _ _ hA P hPP N hN hNu u v hu hv ζ hζ m K _ κ H k _ ρ
  obtain ⟨⟨hP, h₁, h₂, -⟩, hamp, -⟩ := hPP
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over (Sp O)) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over (Sp O)) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : 𝟙_ (Over (Sp O)) ⟶ A, z ^ N = 1 → ∀ p : (𝟙_ (Over (Sp O))).left, ∃ V : (𝟙_ (Over (Sp O))).left.Opens,
      p ∈ V ∧ ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      obtain ⟨θ, hθ⟩ := exists_theta_diag hP hB hB' (k := N) (Out.overResι ⊤ ≫ z)
        (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
      exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts u hu) (lifts v hv)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts 1 (one_pow N)) (lifts v hv)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ = 1 := mul_eq_left.1 (CommutatorPairing.weilIs_unique hG hA hD h11 hc₁)
  have pw : ∀ n : ℕ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (u ^ (n + 1)) v (c₀ ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa using hc₀
    | succ n ih =>
      rw [pow_succ u (n + 1), pow_succ c₀ (n + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hu] at hp
  have hc₀N : c₀ ^ N = 1 := CommutatorPairing.weilIs_unique hG hA hD hp (e₁ ▸ hc₁)
  obtain ⟨w, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 c₀
  have hwN : w ^ N = 1 := by
    apply GlobalTheory.Ex.Specialise.unitOn_bijective.1
    have e : unitOn (w ^ N) = unitOn w ^ N := by unfold unitOn; exact map_pow _ _ _
    rw [e, hc₀N]
    unfold unitOn; exact (map_one _).symm
  have spec : ∀ (F : Type) [Field F] (σ : O →+* F), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N
      (toUnit (Over.mk (spMap σ)) ≫ u) (toUnit (Over.mk (spMap σ)) ≫ v) (unitOn (Units.map σ.toMonoidHom w)) := by
    intro F _ σ
    have hN' := CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk (spMap σ))) hc₀
    have hl : (toUnit (Over.mk (spMap σ))).left = spMap σ := rfl
    rw [hl, GlobalTheory.Ex.Specialise.map_unitOn] at hN'
    exact hN'
  have e := GlobalTheory.Ex.Specialise.unitOn_bijective.1 (CommutatorPairing.weilIs_unique hG hA hD (spec K κ) H)
  have hw : w = ζ ^ m := eq_zpow_of_map_eq κ hN hNu hζ hwN m e
  rw [← hw]
  exact spec k ρ

end GlobalTheory.WeilRoot
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqZpowOfFieldPointDomain =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionOfTorsionRationalOverFractioStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackOfSameFibreWithSquareBundleStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqZpowOfFieldPointDomain\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute\nimport Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevSpread

theorem eq_of_comp_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Z : Over S) [PreconnectedSpace Z.left] (x y : Z ⟶ A) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (T : Over S) (z : T ⟶ Z) [Nonempty T.left] (h : z ≫ x = z ≫ y) : x = y := by
  have hw : (x * y⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, _root_.mul_one]
  obtain ⟨C, hC, hz⟩ := GlobalTheory.TorsionCover.exists_clopen_eq_one A hA hn (x * y⁻¹) hw
  have h1 : z ≫ (x * y⁻¹) = 1 := by
    show (preHom z) (x * y⁻¹) = 1
    rw [map_mul, map_inv]
    show (z ≫ x) * (z ≫ y)⁻¹ = 1
    rw [h, mul_inv_cancel]
  have hsub := (hz T z).1 h1
  obtain ⟨p⟩ := ‹Nonempty T.left›
  have hne : C.Nonempty := ⟨_, hsub ⟨p, rfl⟩⟩
  have huniv : C = Set.univ := hC.eq_univ hne
  have h2 : 𝟙 Z ≫ (x * y⁻¹) = 1 := (hz Z (𝟙 Z)).2 (by rw [huniv]; exact Set.subset_univ _)
  rw [Category.id_comp] at h2
  exact mul_inv_eq_one.1 h2

end GlobalTheory.LevSpread

namespace GlobalTheory.LevSpread

theorem l2 : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  intro R₀ _ _ _ _ A _ _ n hA hnR hT K _ t x hx
  have hnΓ : IsUnit (n : Γ(Sp R₀, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom
    rwa [map_natCast] at this
  let t' : Sp (AlgebraicClosure K) ⟶ Sp R₀ := spMap (algebraMap K (AlgebraicClosure K)) ≫ t
  let z : Over.mk t' ⟶ Over.mk t := Over.homMk (spMap (algebraMap K (AlgebraicClosure K))) rfl
  obtain ⟨σ, hσ, hσx⟩ := _root_.GlobalTheory.TorsConst.exists_section_of_torsRat R₀ A n hA hnR hT (AlgebraicClosure K) t' (z ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  refine ⟨σ, hσ, ?_⟩
  haveI : PreconnectedSpace (Over.mk t).left := inferInstanceAs (PreconnectedSpace (Sp K))
  haveI : Nonempty (Over.mk t').left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  refine eq_of_comp_eq A hA hnΓ (Over.mk t) _ x (by rw [← MonObj.comp_pow, hσ, MonObj.comp_one]) hx (Over.mk t') z ?_
  rw [← Category.assoc, show z ≫ toUnit (Over.mk t) = toUnit (Over.mk t') from toUnit_unique _ _, hσx]

theorem l3 : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), IsPPol A P → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (ζ : Oˣ), IsPrimitiveRoot ζ N → ∀ (m : ℤ) (K : Type) [Field K] (κ : O →+* K), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap κ)) ≫ u) (toUnit (Over.mk (spMap κ)) ≫ v) (unitOn (Units.map κ.toMonoidHom (ζ ^ m))) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom (ζ ^ m))) := _root_.GlobalTheory.WeilRoot.weilIs_zpow_of_fieldPoint

theorem prim_map {n : ℕ} (hn : n ≠ 0) {R : Type} [CommRing R] [IsDomain R] (β : cycAway n →+* R) :
    IsPrimitiveRoot (β (zetaAway n)) n := by
  have h₁ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn) Subtype.val_injective
  have : NeZero (n : R) := ⟨by simpa using ((isUnit_natCast hn).map β).ne_zero⟩
  have h₂ := (h₁.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map (f := β)
  rwa [Polynomial.map_cyclotomic, Polynomial.isRoot_cyclotomic_iff] at h₂

end GlobalTheory.LevSpread
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf =====
