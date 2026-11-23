module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Adapted
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealVectorsAllPlacesOfLocalData
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realVectors_allPlaces_of_localData : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S S' : D.what₂.Tau → SPar}
  (M₀ : DSModel Y S') (M : DSModel V S) (q : ℝ) (εA : D.what₂.Tau → Fin Y.rank → Bool)
  (A : D.what₂.Tau → Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (εB : D.what₂.Tau → Fin V.rank → Bool)
  (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : ∀ τ, M.H τ) (g₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
  (w : ∀ τ, M₀.H τ) (c : D.what₂.Tau → ℂ),
  (∀ τ, GlobalTheory.PackLoc.LocOK θ d M₀ M τ q (εA τ) (A τ) (εB τ) (B τ) (v₀ τ) (g₀ τ) (w τ) (c τ)) →
    ∃ p : Pack M₀ M, p.Is θ d (Fintype.card D.what₂.Tau * q) := by
  first | exact @GlobalTheory.PackGlob.pack_of_loc | exact GlobalTheory.PackGlob.pack_of_loc | (intros; apply GlobalTheory.PackGlob.pack_of_loc <;> assumption)
