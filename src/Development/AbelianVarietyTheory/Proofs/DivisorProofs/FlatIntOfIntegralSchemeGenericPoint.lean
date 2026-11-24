module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Mathlib.Algebra.CharP.Algebra
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.SurjOfCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.IntFlat

theorem flat_of_generic_zero : ∀ {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Spec (CommRingCat.of ℤ)) (x : X), (s x).asIdeal = ⊥ → Flat s := by
  intro X _ s x hx
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) X.affineOpenCover.openCover fun i => ?_
  let R := X.affineOpenCover.X i
  let j : Spec R ⟶ X := X.affineOpenCover.f i
  have : IsOpenImmersion j := X.affineOpenCover.map_prop i
  change Flat (j ≫ s)
  rcases isEmpty_or_nonempty (Spec R) with h | h
  · infer_instance
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 this
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ s)
  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hg : genericPoint X ∈ Set.range j :=
    (genericPoint_specializes (j (Classical.arbitrary (Spec R)))).mem_open
      j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := hg
  have h1 : p0 ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have h2 : j p0 ⤳ x := hq ▸ (h1.map j.continuous) |>.trans (genericPoint_specializes x)
  have h3 : (j ≫ s) p0 ⤳ s x := h2.map s.continuous
  have h4 : ((j ≫ s) p0).asIdeal ≤ ⊥ := hx ▸ (PrimeSpectrum.le_iff_specializes _ _).2 h3
  rw [← hφ] at h4
  have hinj : Function.Injective φ.hom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro n hn
    have : n ∈ ((Spec.map φ) p0).asIdeal := by
      show n ∈ Ideal.comap φ.hom ⊥
      simp [hn]
    simpa using h4 this
  have e : φ.hom = algebraMap ℤ R := RingHom.ext_int _ _
  have : CharZero R := charZero_of_injective_algebraMap (e ▸ hinj)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Flat)]
  rw [e, RingHom.flat_algebraMap_iff]
  infer_instance

end GlobalTheory.IntFlat
