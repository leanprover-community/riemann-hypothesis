module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CongruenceSubgroupEventually
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalConjugateMem
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

private theorem unif_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    ValuativeRel.valuation k ((UpperTheory.V.Hi.unif k : kˣ) : k) < 1 := by
  have hex : ∃ x : kˣ, ValuativeRel.valuation k (x : k) = ValuativeRel.uniformizer k := by
    obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := k) (ValuativeRel.uniformizer k)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact ValuativeRel.uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x hx0, hx⟩
  have h := Classical.epsilon_spec hex
  have h' : ValuativeRel.valuation k ((UpperTheory.V.Hi.unif k : kˣ) : k) = ValuativeRel.uniformizer k := h
  rw [h']
  exact ValuativeRel.uniformizer_lt_one

private theorem diagT_val (k : Type) [Field k] (n : ℕ) (t : Fin n → kˣ) :
    ((GlobalTheory.SmGL.diagT k (Fin n) t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => (t i : k)) := by
  exact GlobalTheory.SmGL.val_diagT k t

private theorem unipB_spec (k : Type) [Field k] (n : ℕ) (g : GL (Fin n) k)
    (hg : g ∈ GlobalTheory.SmGL.unipB k (Fin n)) :
    (g : Matrix (Fin n) (Fin n) k).BlockTriangular id ∧ ∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1 := by
  obtain ⟨p, hp, rfl⟩ := hg
  refine ⟨p.2, fun i => ?_⟩
  have h1 : GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.points (Fin n)) p = 1 := hp
  have h2 := congrArg (fun x => ((x i : GL Unit k) : Matrix Unit Unit k) () ()) h1
  have h3 : ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = (1 : Matrix Unit Unit k) () () := h2
  simpa using h3

theorem UpperTheory.Reformulated.B.BranchingSmooth.br_smooth :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k]
      [inst_3 : IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [inst_4 : AddCommGroup V] [inst_5 : _root_.Module ℂ V]
      (π : Representation ℂ (GL (Fin n) k) V), GlobalTheory.PRep.IsSmooth π → (UpperTheory.V.Hi.glIwa k n).Smooth π := by
  intro k _ _ _ _ n V _ _ π hπ v
  obtain ⟨c, hc⟩ := UpperTheory.congruence_subgroup_eventually (k := k) (n := n) {g | π g v = v} ((hπ v).mem_nhds (by simp))
  refine ⟨c, ?_, ?_, ?_⟩
  · show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := unipB_spec k n x hx.1
    exact hc c le_rfl _ (UpperTheory.diagonal_conjugate_mem (UpperTheory.V.Hi.unif k) (unif_lt k) c _ x (diagT_val k n _) hx.2 h1 h2)
  · show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _
    intro g hg
    exact hc (c + 1) (Nat.le_succ c) g hg.2
  · show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _
    intro g hg
    exact hc (c + 1) (Nat.le_succ c) g hg.2
