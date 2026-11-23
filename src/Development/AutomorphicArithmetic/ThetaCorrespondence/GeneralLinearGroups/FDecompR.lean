module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsNeOfNeBot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FAssocR
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

theorem UpperTheory.Lit.Full.decompR :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))), ∃ y z, Emb x y z ∧ LastIn y Pᶜ ∧ SuppIn z P := by
  intro hG hBZ k _ _ _ _ x P
  have key : ∀ (n : ℕ) (y z : IrrGL (k := k)), y.1 = n → Emb x y z → SuppIn z P →
      ∃ y z, Emb x y z ∧ LastIn y Pᶜ ∧ SuppIn z P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro y z rfl hxyz hz
      by_cases hl : LastIn y Pᶜ
      · exact ⟨y, z, hxyz, hl, hz⟩
      obtain ⟨q, hq, hc, hj, hP⟩ : ∃ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = y.1),
          (q 1).IsCusp ∧ jm q hq y.rep ≠ 0 ∧ q 1 ∈ P := by
        by_contra hn
        exact hl fun q hq hc hj hP => hn ⟨q, hq, hc, hj, hP⟩
      obtain ⟨u, hu⟩ := UpperTheory.Lit.Full.embR hG hBZ k y q hq hc hj
      obtain ⟨v, ⟨hd, hv⟩, hxuv⟩ := UpperTheory.Lit.Full.assocR hG hBZ k x y z u (q 1) hxyz hu
      obtain ⟨A, hA, hAP⟩ := hz
      have hlt : u.1 < y.1 := by
        obtain ⟨hd', -⟩ := hu
        have h1 : u.1 + (q 1).1 = y.1 := by simpa using hd'
        have := hc.1
        omega
      refine ih u.1 hlt u v rfl hxuv ⟨∑ a, (![{q 1}, A] : Fin 2 → Multiset (IrrGL (k := k))) a, ?_, ?_⟩
      · refine GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![q 1, z]) ?_ v.2.rep.irr
          (jhMult_ne_zero_iff.1 hv)
        exact Fin.forall_fin_two.2 ⟨hasSupport_self hc, hA⟩
      · intro w hw
        have hw' : w ∈ ({q 1} : Multiset (IrrGL (k := k))) + A := by simpa using hw
        rcases Multiset.mem_add.1 hw' with h | h
        · rw [Multiset.mem_singleton.1 h]; exact hP
        · exact hAP w h
  let o : IrrGL (k := k) := ⟨0, (IrrRep.det (Fin 0) (1 : kˣ →* ℂˣ) isSmoothChar_one).cl⟩
  have hd : ∑ a, (![x, o] a).1 = x.1 := by simp [o]
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_pair_zero k x o rfl hd
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG o
  refine key x.1 x o rfl ⟨hd, φ.toIntertwiningMap, φ.toLinearEquiv.injective⟩ ⟨s, hs, ?_⟩
  rw [GlobalTheory.LocGL.SupportUnique.eq_zero_of_hasSupport (N := o.1) rfl hs]
  simp
