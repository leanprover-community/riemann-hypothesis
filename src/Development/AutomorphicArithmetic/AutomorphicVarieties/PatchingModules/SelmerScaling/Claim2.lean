module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlSel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefULift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUPush
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUTest
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PhDecDApply
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.claim2 :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ m : Fin S.k.g → S.U.N, S.DualM m → ∀ Φ ∈ S.Ph, ∃ α : Fin S.k.g → S.Tp, (∀ j b, (α j : S.Bh →+ S.F) b = Φ (b • m j) - S.rF b * Φ (m j)) ∧ Lifts S.h S.k fun j => S.alC (α j) := by
  intro l _ S m hm Φ hΦ
  obtain ⟨e, α, μ, hα, hμ, hΦd⟩ := phDec l S Φ hΦ
  let c : Fin e → Fin S.k.g → S.F := fun k j => μ k (m j)
  obtain ⟨u, ψ, hu, h1, h2⟩ := defUTest l S e α μ Φ hα hμ hΦd
  obtain ⟨u', hu', h1', h2'⟩ := defUConj l S.L S.G S.G0 S.h S.n S.x e u ψ
    (fun k => ∑ j, c k j • kapF S.h S.k j) hu
    (fun k => by rw [h1 k]; exact hm (μ k) (hμ k))
  obtain ⟨u'', ψ'', hu'', h1'', h2''⟩ := defUPush l S.L S.G S.G0 S.h S.n S.x S.k e u' ψ c hu' h1'
  have hL := defULift l S.L S.G S.G0 S.h S.n S.x S.k u'' ψ'' hu'' h1''
  refine ⟨fun j => ⟨∑ k, c k j • α k, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hα k)⟩, ?_, ?_⟩
  · intro j b
    show (∑ k, c k j • α k) b = _
    rw [hΦd, add_sub_cancel_left]
    simp [c, mul_comm]
  · have e2 : (fun j => S.alC (∑ k, c k j • α k)) = epC' S.h S.x u'' := by
      funext j
      rw [h2'' j, (alSel l S).2.2.1 (Fin e) (fun k => c k j) α]
      simp only [h2', h2]
    show Lifts S.h S.k (fun j => S.alC (∑ k, c k j • α k))
    rw [e2]
    exact hL
