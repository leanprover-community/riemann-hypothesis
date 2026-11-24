module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetRepresentativesCongrAtTwistPrime
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.couplingCoset_representatives_congr_at_twistPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (g k : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))),
    g ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    SameCoset t.sel (t.tup μ) (t.cst μ) P (g (y0At A (t.m2 + 1) hi β P)) (y0At A (t.m2 + 1) hi β P) →
    k ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    (∀ w ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (k w - w) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) →
    (∀ w, frsF t.sel (t.tup μ) p₁ P w = frsF t.sel (t.tup μ) p P (g (k w))) →
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) := by
  first | exact @GlobalTheory.LocQCoset.coset_agree | exact GlobalTheory.LocQCoset.coset_agree | (intros; apply GlobalTheory.LocQCoset.coset_agree <;> assumption)
