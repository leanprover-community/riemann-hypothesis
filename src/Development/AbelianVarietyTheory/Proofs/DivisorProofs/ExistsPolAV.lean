module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarisationOfFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolFieldDescent

theorem exists_polAV : ∀ (K K' : Type) [Field K] [Field K'] (ga : K →+* K') (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → Out.Sym G L → ∀ (A' : PolAV (Sp K')) (α : A'.A.left ⟶ G.left), IsGrpPullback A'.A G (spMap ga) α → LBIso A'.L (L.pull α) → ∃ (A : PolAV (Sp K)) (gen : G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) L := by
  intro K K' _ _ ga G _ _ L hL hS A' α hP hw
  letI : Algebra K K' := ga.toAlgebra
  have hP' : IsGrpPullback A'.A G (spMap (algebraMap K K')) α := hP
  have : Flat (spMap ga) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (spMap ga) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := K) (B := K')⟩
  have : QuasiCompact (spMap ga) := inferInstance
  have hAb : IsAbelianScheme G := PolFlatDescent.isAbelianScheme_of_pull hP A'.isAb
  have hdim : SmoothOfRelativeDimension A'.g G.hom :=
    CM.smoothOfRelativeDimension_of_fibre K K' ga G A'.A.left α A'.A.hom A'.g hAb hP.1 A'.smoothDim
  have hrig : Out.Rigidified G L := DVR.exists_gen_of_local L hL _ _
  have hamp : Out.RelAmple G L :=
    AmpleDescent.relAmple_of_faithfullyFlat K K' G A'.A α L A'.L hAb hP' hL A'.isLB hw A'.ample
  have hK : Out.KTriv G L := AmpleDescent.kTriv_of_pull hP hL A'.isLB hw A'.ktriv
  refine ⟨⟨G, hAb, A'.g, hdim, L, hL, hrig, hS, hamp, hK⟩, Iso.refl G, ?_, ?_⟩
  · show IsMonHom (𝟙 G); infer_instance
  · exact GlobalTheory.lbIso_pull_id hL

end GlobalTheory.PolFieldDescent
