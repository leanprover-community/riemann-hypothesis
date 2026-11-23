module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.MajFrame

theorem exists_maj_cart : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → ∃ a : GL (Fin A.rank) (AE D), IsMaj A a ∧ ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1 := by
  intro D θ A sA hθ hs
  obtain ⟨a, ha, -, hfs⟩ := GlobalTheory.Doubling.exists_isMaj_frameInv_eq hθ hs
  refine ⟨a, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ
  rw [← hfs τ, GlobalTheory.Doubling.frameInv]
  have : (compAt θ τ a.1)ᴴ * (gramAt D A τ * (compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D A τ)) * compAt θ τ a.1 =
      ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) := by
    simp only [Matrix.mul_assoc]
  rw [this, hε, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp

end GlobalTheory.Core.Rk.MajFrame
