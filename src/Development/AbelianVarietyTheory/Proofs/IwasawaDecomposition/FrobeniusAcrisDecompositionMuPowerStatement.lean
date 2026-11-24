module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusAcrisDecompositionMuPower
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

theorem _root_.GlobalTheory.T.frobenius_acris_decomposition_mu_power : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ w : Per.Acris l, (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) → ∀ y : Per.Acris l, ∃ (a : Per.Ainf l) (z : Per.Acris l), phiA l y = algebraMap (Per.Ainf l) (Per.Acris l) a + w * z := by
  first | exact @GlobalTheory.MemLoc.phiA_mem_ainf_add | exact GlobalTheory.MemLoc.phiA_mem_ainf_add | (intros; apply GlobalTheory.MemLoc.phiA_mem_ainf_add <;> assumption)
