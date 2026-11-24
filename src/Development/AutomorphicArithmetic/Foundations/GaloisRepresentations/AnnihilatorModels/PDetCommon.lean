module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepConjInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detCommon_of :
    CommonModel := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c hr hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₁, r₁, hm₁, hc₁⟩ := hr
  obtain ⟨L₂, c₂, hm₂, hp₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  haveI := L₁.2
  haveI := (supExt L₁ L₂).2
  have hs₁ : IsSst P (Bw.repE L₁ r₁) := GlobalTheory.CrysSst.isSst_of_isCrys P AI T (Bw.repE L₁ r₁) hc₁
  have hs := GlobalTheory.AboveL.RepConj.isSst_enlarge P Bw l₁ r₁ hs₁
  refine ⟨supExt L₁ L₂, mapRep (IntermediateField.inclusion l₁).toRingHom r₁,
    mapRep (IntermediateField.inclusion l₂).toRingHom c₂, hm₁.enlarge l₁, hm₂.enlarge l₂, hs, ?_,
    GlobalTheory.PstExt.isPst_enlarge P Bw l₂ c₂ hp₂⟩
  haveI : FiniteDimensional ℚ_[l] (Fin a → ↥(supExt L₁ L₂).1) := Module.Finite.trans ↥(supExt L₁ L₂).1 _
  exact GlobalTheory.GalCut.IwaTwist.isPst_of_isSst P AI T _ hs
