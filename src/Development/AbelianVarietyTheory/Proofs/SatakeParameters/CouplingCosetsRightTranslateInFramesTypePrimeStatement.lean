module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coupling_cosets_right_translate_in_frames_type_prime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1))
    (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (Gg k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1) z, A.cplRel β P Gg.1 z →
    redGL _ P.1 k = redGL _ P.1 Gg → frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 →
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l)) ∧
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) l)) ∧
    k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E _ P.1) := by
  first | exact @GlobalTheory.CplCosetPt.cosetOf_frames_vG | exact GlobalTheory.CplCosetPt.cosetOf_frames_vG | (intros; apply GlobalTheory.CplCosetPt.cosetOf_frames_vG <;> assumption)
