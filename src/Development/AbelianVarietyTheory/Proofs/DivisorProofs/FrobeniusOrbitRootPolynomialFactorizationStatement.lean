module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitRootPolynomialFactorization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (b : Fin r → Fin r) (x : Cyc b → Fbar p) (f : (ZMod p)[X]), IsRootPoly x f → f.natDegree = r ∧ f.coeff 0 ≠ 0 ∧ (Squarefree f ↔ Function.Injective (rootElt x)) ∧ (Squarefree f → (∀ c, (minpoly (ZMod p) (x c)).natDegree = cycLen b c) ∧ Function.Injective (fun c => minpoly (ZMod p) (x c)) ∧ f = ∏ c, minpoly (ZMod p) (x c)) := by
  first | exact @GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor | exact GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor | (intros; apply GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor <;> assumption)
