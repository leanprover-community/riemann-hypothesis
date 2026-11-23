module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutMemLatticeStabilizerOfProductLevel
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix

theorem _root_.GlobalTheory.T.idempotentCut_mem_latticeStabilizer_of_productLevel : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    {n' : P → ℕ} (h : ∀ w, n' w = n) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (x : GL (Fin n) (Lev.EAf D)),
    x ∈ prodLev β P h K → ∀ (b : Lev.EAf D) (hb : b * b = b),
    (∀ w : Pl D.host.E, (∃ PP ∈ P, w.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.StdFrames.cpt (D := D) w b = 0) →
    GlobalTheory.UnitaryIdemCut.cutGL b hb x ∈ St β := by
  first | exact @GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev | exact GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev | (intros; apply GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev <;> assumption)
