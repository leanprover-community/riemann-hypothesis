module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.periodRings_galoisAction_laws_frobenius_comm : ∀ (l : ℕ) [Fact l.Prime], (∀ (g h : Per.Gq l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x)) ∧ (∀ x : Per.Bcris l, Per.σB 1 x = x) ∧ (∀ (g h : Per.Gq l) (x : Per.BdR l), Per.σD (g * h) x = Per.σD g (Per.σD h x)) ∧ (∀ x : Per.BdR l, Per.σD 1 x = x) ∧ (∀ (g : Per.Gq l) (x : Per.Bcris l), Per.φB l (Per.σB g x) = Per.σB g (Per.φB l x)) ∧ (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σB g (Per.aB l a) = Per.aB l (Per.σA g a)) ∧ (∀ a : Per.Ainf l, Per.φB l (Per.aB l a) = Per.aB l (Per.φA l a)) ∧ (∀ (g : Per.Gq l) (z : ℤ_[l]), Per.σA g (Per.zA l z) = Per.zA l z) ∧ (∀ z : ℤ_[l], Per.φA l (Per.zA l z) = Per.zA l z) ∧ (∀ (g : Per.Gq l) (y : Per.BdRp l), Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y)) ∧ (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σDp g (aDp l a) = aDp l (Per.σA g a)) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (sigA g x)) ∧ ∀ x : Per.Acris l, Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) := by
  first | exact @GlobalTheory.MemLoc.ActLaws.act_laws | exact GlobalTheory.MemLoc.ActLaws.act_laws | (intros; apply GlobalTheory.MemLoc.ActLaws.act_laws <;> assumption)
