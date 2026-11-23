module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pExtPts :
    ExtPts := by
  intro W Z B _ p _ f g hfg hpt
  let X' : Over B := Over.mk (f ≫ p)
  let Y' : Over B := Over.mk p
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g hfg.symm
  have : IsSeparated Y'.hom := ‹_›
  have hsurj : Surjective (equalizer.ι f' g').left := by
    constructor
    intro x
    let K := W.residueField x
    let Ω := AlgebraicClosure K
    let y : Spec (CommRingCat.of Ω) ⟶ W :=
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x
    have hy : y ≫ f = y ≫ g := hpt Ω y
    let U' : Over B := Over.mk (y ≫ f ≫ p)
    let y' : U' ⟶ X' := Over.homMk y
    have hy' : y' ≫ f' = y' ≫ g' := by
      ext1
      exact hy
    let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
    refine ⟨(equalizer.lift y' hy').left pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
    show (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x) pt = x
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have := isIso_of_isClosedImmersion_of_surjective (Y := W) (equalizer.ι f' g').left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)
