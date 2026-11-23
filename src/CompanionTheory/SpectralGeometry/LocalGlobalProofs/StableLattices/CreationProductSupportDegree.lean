module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgExh

theorem suppIn_deg_cre_prod : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (P : Pos n → Prop) (l : List (Pos n)) (x : Cn n V) (j : ℕ),
    (∀ i ∈ l, P i) → SuppIn P x → Deg j x →
      SuppIn P (((l.map cre).prod : Module.End ℂ (Cn n V)) x) ∧
        Deg (j + l.length) (((l.map cre).prod : Module.End ℂ (Cn n V)) x) := by
  intro n V _ _ P l x j hl hx hd
  induction l with
  | nil => simpa using And.intro hx hd
  | cons i l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hl k (List.mem_cons_of_mem i hk)
    have hi : P i := hl i List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]
    constructor
    · intro A hA k hk
      obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.cre_ne hA
      by_cases hki : k = i
      · exact hki ▸ hi
      · exact ih1 _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)
    · intro A hA
      obtain ⟨h1, h2⟩ := CompanionTheory.D.LK.cre_ne hA
      have h3 := ih2 _ h2
      have h4 := Finset.card_erase_add_one h1
      omega

end GlobalTheory.CompanionTheory.RgExh
