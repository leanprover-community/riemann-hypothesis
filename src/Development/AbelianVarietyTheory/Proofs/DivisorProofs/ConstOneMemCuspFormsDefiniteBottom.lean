module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section
namespace GlobalTheory.BottomCusp

theorem isAniso_neg {D : D7} {A : HSp D} (h : IsAniso A) : IsAniso (GlobalTheory.Grid.neg A) := by
  rintro r C ⟨hr, hC, h0⟩
  refine h r C ⟨hr, hC, ?_⟩
  have e : (GlobalTheory.Grid.neg A).gram = -A.gram := GlobalTheory.Grid.neg_gram A
  rw [e, Matrix.mul_neg, Matrix.neg_mul] at h0
  exact neg_eq_zero.1 h0

theorem const_one_mem_cuspForms_of_anisotropic {D : D7} {V : HSp D} (h : IsAniso V) (θ : GlobalTheory.Mem.Th.InfF D) (A : CptF V) :
    (fun _ => (1 : ℂ)) ∈ A0 θ V A :=
  GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨isAutFunSm_const θ V 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

theorem one_mem_A0_of_isBottomTri : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ cA : CptF (GlobalTheory.Grid.neg A), HidaSetting W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s A'.rank cA → (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X hX t cA _
  exact const_one_mem_cuspForms_of_anisotropic (isAniso_neg (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.std.1)) W.θ cA

end GlobalTheory.BottomCusp
