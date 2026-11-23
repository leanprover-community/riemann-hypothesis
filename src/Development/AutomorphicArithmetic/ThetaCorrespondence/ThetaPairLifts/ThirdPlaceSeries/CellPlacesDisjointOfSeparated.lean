module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesOfAdmissibleTwist
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.SepPlaces
end GlobalTheory.SepPlaces
namespace GlobalTheory.SepPlaces
end GlobalTheory.SepPlaces
namespace GlobalTheory.SepPlaces
theorem cell_places_separated_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → ¬ (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∧ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ (∀ kv, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv)).v ≠ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') := by
  intro _ hL
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l v i b ψ hA j _ _ _ P' hP'
  exact sep_gen (Dof x) (cell (D := Dof x) l.b.Bs.exp b hA j) (fun P hP => hA.2.1 P hP) P' hP'
end GlobalTheory.SepPlaces
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

theorem _root_.GlobalTheory.T.cell_places_disjoint_of_admTw : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → ¬ (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∧ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ (∀ kv, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv)).v ≠ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') := by
  first | exact @_root_.GlobalTheory.SepPlaces.cell_places_separated_alt | exact _root_.GlobalTheory.SepPlaces.cell_places_separated_alt | (intros; apply _root_.GlobalTheory.SepPlaces.cell_places_separated_alt <;> assumption)
end
end
