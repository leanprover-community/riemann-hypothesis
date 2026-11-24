module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.BlockCoefficientLocalGlobalFactor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.block_coefficient_local_global_factor : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → ∀ (d : ℕ) (b : Module.Basis (Fin d) D.host.F D.host.E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F)) (lamv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F ⊗[D.host.F] D.host.E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lamv v)) → IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) b laminf r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig b laminf r) minf → (∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) b (lamv v) r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig b (lamv v) r) (m v)) → ∀ I : Measure (Fin r → Fin V.rank → AE D), GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig β.1 (hermE_symm β))) (fun v => m v (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig β.1 (hermE_symm β))) → Integrable (fun X => φ (trM X)) I → W ψ V μ lam φ β = ∫ X, φ (trM X) ∂I := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.whit_eq_integral | exact GlobalTheory.CompanionTheory.WhitFree.whit_eq_integral
