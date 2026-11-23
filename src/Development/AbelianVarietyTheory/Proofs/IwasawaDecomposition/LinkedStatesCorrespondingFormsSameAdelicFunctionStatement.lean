module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCorrespondingFormsSameAdelicFunction
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

theorem _root_.GlobalTheory.T.linkedStates_corresponding_forms_same_adelicFunctions : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → GlobalTheory.TwInputs.Move.SameMap (GlobalTheory.TwInputs.Move.evidence (sideAt x g hg a) j y) (GlobalTheory.TwInputs.Move.evidence (sideAt x' g' hg' a') j' y') := by
  first | exact @GlobalTheory.HeightCounting.SerMove.reading_link | exact GlobalTheory.HeightCounting.SerMove.reading_link | (intros; apply GlobalTheory.HeightCounting.SerMove.reading_link <;> assumption)
