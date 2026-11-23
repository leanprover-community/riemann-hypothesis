module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryConjSplitSupportedFiniteAdelicPoi
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalUnitary_conj_splitSupported_finiteAdelicPoint : ∀ (D : D7) (V : HSp D) (S : Finset ℕ) (γ : GL (Fin V.rank) D.host.E) (h : GA D V),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram → h ∈ GfC V →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) →
    ∃ u : GA D V, u ∈ GfC V ∧ (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u ∧ ∀ w ∈ P, Off S w) ∧
      (Formalism.IndefR.Lev.finE V u).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (γ⁻¹).1.map (eToEAf D) := by
  first | exact @GlobalTheory.ConjSplit.conj_supp | exact GlobalTheory.ConjSplit.conj_supp | (intros; apply GlobalTheory.ConjSplit.conj_supp <;> assumption)
