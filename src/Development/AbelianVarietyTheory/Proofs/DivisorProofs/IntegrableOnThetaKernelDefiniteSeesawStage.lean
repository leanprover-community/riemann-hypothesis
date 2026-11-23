module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.SqTower

theorem integrableOn_ker'_of_stage_zero : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (p : ℕ)
    (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
    ∀ (t : T) (P' : PolF D WW.rank A'.rank) (h : GA D WW), MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m' := by
  intro D T Lc sc G W i j p A A' WW X hX t P' h
  obtain ⟨-, -, -, -, -, hA', -, hIs⟩ := hX
  have hom : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hIs.weil' t
  have hpos : ∀ τ, (gramAt D A' τ).PosDef := fun τ =>
    GlobalTheory.DefiniteQuotient.posDef_of_signature (hA' τ)
  have hf : IsThetaFunO W.ψ A' WW (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P') :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hIs.isVac'.1 hIs.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hIs.isVac'.1 hIs.isVac'.2.inf (hIs.snd t) hIs.isVac'.2.theta) P'
  have key := GlobalTheory.DefiniteQuotient.integrableOn_theta D W.ψ hom.std A' WW _ _ (X.ω' t) hom hpos ℂ
    (LinearMap.toSpanSingleton ℂ _ (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P'))
    (fun x => GlobalTheory.OrientedHeis.theta_smul x hf) (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
    X.m' X.fd' hIs.meas'.1 hIs.meas'.2 h
  simp only [LinearMap.toSpanSingleton_apply, one_smul] at key
  exact key

end GlobalTheory.SqTower

end
