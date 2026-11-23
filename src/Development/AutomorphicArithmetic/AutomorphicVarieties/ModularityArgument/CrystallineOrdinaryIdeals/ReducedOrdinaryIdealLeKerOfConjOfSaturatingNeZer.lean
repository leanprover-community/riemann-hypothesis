module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariantStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsMapAlgHomStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem icr_le_ker_of_conj : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (S : Type) [CommRing S] [IsDomain S] [Algebra O S] (i α : U.R →ₐ[O] S) (u : GL (Fin 3) S), push α U.r.hom = conjBy u (push i U.r.hom) → GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker i → i (GlobalTheory.OrdLoc.del D U.r.hom) ≠ 0 → GlobalTheory.OrdLoc.Icr D U ≤ RingHom.ker α := by
  intro l _ O _ _ _ D U S _ _ _ i α u hc hY hd
  have hm : HasMult D.η (push i U.r.hom) := U.r.hasMult
  obtain ⟨hcI, -, hcd⟩ := GlobalTheory.T.ordinaryIdeal_saturators_conj_invariant D (push i U.r.hom) u hm
  obtain ⟨hiI, -, hid⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D i U.r.hom
  obtain ⟨haI, -, had⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D α U.r.hom
  have hord : ordIdeal D U.r.hom ≤ IY D U := fun a ha => ⟨0, by simpa using ha⟩
  have hbot : ordIdeal D (push i U.r.hom) = ⊥ := by
    rw [← hiI, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    simpa [Ideal.mem_comap] using hY (hord ha)
  have hα : ordIdeal D (push α U.r.hom) = ⊥ := by rw [hc, hcI, hbot]
  have hdel : α (del D U.r.hom) ≠ 0 := by
    rw [had, hc, hcd, ← hid]; exact hd
  intro x hx
  obtain ⟨k, n, hn⟩ := hx
  have h1 : α (del D U.r.hom ^ n * x ^ k) ∈ ordIdeal D (push α U.r.hom) := by
    rw [← haI]; exact Ideal.mem_map_of_mem _ hn
  rw [hα, Ideal.mem_bot, map_mul, map_pow, map_pow] at h1
  have h2 : α x ^ k = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (pow_eq_zero_iff'.1 h).1 hdel
    · exact h
  exact RingHom.mem_ker.2 (pow_eq_zero_iff'.1 h2).1

end GlobalTheory.OrdLoc
