module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FPiece
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCells
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

theorem UpperTheory.Lit.Full.firstProd :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : Set (IrrGL (k := k))) (h : ℕ) (y : Fin h → IrrGL (k := k)) (x : IrrGL (k := k)) (hc : ∑ i, (y i).1 = x.1), (∀ i, FirstIn (y i) P) → jhMult x.rep (prodIrr y hc) ≠ 0 → FirstIn x P := by
  intro hG hBZ k _ _ _ _ P h y x hc hy hx q hq hq0 hjm
  classical
  have h1 : jm q hq (prodIrr y hc) ≠ 0 :=
    jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 hjm).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac _ (isSmooth_parInd _ _) (jhMult_ne_zero_iff.1 hx)))
  obtain ⟨z, hr, hz, hrow, hcol⟩ := UpperTheory.Lit.Cas.cells hG hBZ k h x.1 y hc q hq h1
  have hpos : 0 < ∑ i, (z i 0).1 := (hz 0).symm ▸ hq0.1
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  obtain ⟨A, hA, w, hwA, hwP⟩ :=
    (UpperTheory.Lit.Full.piece hG hBZ k (y i) P (z i) (hr i) (hrow i)).1 (hy i) (Nat.pos_of_ne_zero hi)
  choose t ht using fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (z j 0)
  have hS := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := fun j => z j 0) (hd := hz 0) ht
    (q 0).2.rep.irr (jhMult_ne_zero_iff.1 (hcol 0))
  have e1 : ∑ j, t j = {q 0} := SupportUnique.eq_singleton_of_isCusp hq0 hS
  have e2 : t i = A := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ (ht i) hA
  have hw : w ∈ ∑ j, t j :=
    Multiset.mem_of_le (Finset.single_le_sum (f := t) (fun _ _ => zero_le) (Finset.mem_univ i)) (e2 ▸ hwA)
  rw [e1, Multiset.mem_singleton] at hw
  exact hw ▸ hwP
