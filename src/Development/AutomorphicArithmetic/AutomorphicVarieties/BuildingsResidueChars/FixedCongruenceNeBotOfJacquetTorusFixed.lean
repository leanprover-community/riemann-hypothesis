module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CongruenceSubgroupEqDiagonalUnipotentLowerIwahor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.fixed_congruence_ne_bot_of_jacquet_torus_fixed :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1),
    IsAdmissible π → ∀ y : Jacquet π (unipB k (Fin N)), y ≠ 0 →
    (∀ t : Fin N → kˣ, (∀ i, valuation k ((t i : k) - 1) < γ) → jacBU π t y = y) →
    fixed π (GlobalTheory.CentralExponent.cong (Fin N) γ hγ) ≠ ⊥ := by
  intro k _ _ _ _ N V _ _ π γ hγ hπ y hy0 hy hbot
  have hmem : ∀ d : Fin N → kˣ, diagT k (Fin N) d ∈ GlobalTheory.CentralExponent.cong (Fin N) γ hγ ↔
      ∀ i, valuation k ((d i : k) - 1) < γ := by
    intro d
    constructor
    · intro h i
      have := h i i
      simpa [val_diagT] using this
    · intro h i j
      by_cases hij : i = j
      · subst hij
        simpa [val_diagT] using h i
      · simp [val_diagT, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  obtain ⟨v, hv, e⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_mk_eq hπ
    (GlobalTheory.CentralExponent.isOpen_cong γ hγ) (GlobalTheory.CentralExponent.isCompact_cong γ hγ) (diagT k (Fin N))
    (N := unipB k (Fin N)) (fun _ => leviEmb_mem_normalizer k (points (Fin N)) _)
    ((GlobalTheory.CentralExponent.cong (Fin N) γ hγ).comap (diagT k (Fin N)))
    (fun _ h => h) (GlobalTheory.SmGL.IwahoriOnto.lowerInt k (Fin N))
    (fun g hg => by
      obtain ⟨d, hd, x, hx, c, hc, e⟩ := UpperTheory.congruence_subgroup_eq_diagonal_unipotent_lower_iwahori k N γ hγ g hg
      exact ⟨d, (hmem d).2 hd, x, hx, c, hc, e⟩)
    (GlobalTheory.SmGL.IwahoriOnto.lowerInt_contract k (Fin N)) y
    (fun d => by
      have := hy d ((hmem d).1 d.2)
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      exact this)
  rw [hbot, Submodule.mem_bot] at hv
  exact hy0 (by rw [← e, hv, map_zero])
