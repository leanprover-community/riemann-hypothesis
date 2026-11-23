module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKsSubMapClsEqHomO
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

theorem _root_.GlobalTheory.T.finrank_ksSub_map_cls_eq_finrank_homO : ∀ {k O H : Type*} [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (σ : O →+* Module.End k H) (G Z : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z), Z ≤ G → finrank k ((ksSub σ 0 G Z).map (cls G)) = finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (qAct σ G hG)) := by
  first | exact @GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO | exact GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO | (intros; apply GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO <;> assumption)
