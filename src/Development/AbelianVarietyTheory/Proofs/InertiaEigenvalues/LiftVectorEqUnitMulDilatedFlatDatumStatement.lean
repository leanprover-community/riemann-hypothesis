module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftVectorEqUnitMulDilatedFlatDatum
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.lift_vector_eq_unit_mul_dilated_flat_datum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ Gc : ℂ, UnitOff (GlobalTheory.TwistField.tupPrime R t) Gc ∧ IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (fun x => Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0)) ∧ ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → R.vP i t = Tm (fun x => Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0)) := by
  first | exact @GlobalTheory.LiftFlatModel.lift_eq_model_flat | exact GlobalTheory.LiftFlatModel.lift_eq_model_flat | (intros; apply GlobalTheory.LiftFlatModel.lift_eq_model_flat <;> assumption)
