module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.PGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.PhiLe
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.burnsideHom :
    ∀ (p : ℕ) [Fact p.Prime] (P : Type) [Group P] [Finite P], IsPGroup p P → ∀ K : Subgroup P, (∀ f : P →* Multiplicative (ZMod p), K ≤ f.ker → f = 1) → K = ⊤ := by
  intro p _ P _ _ hP K hK
  rcases IsCoatomic.eq_top_or_exists_le_coatom K with h | ⟨M, hM, hKM⟩
  · exact h
  exfalso
  obtain ⟨hMn, hMi, -⟩ := UpperTheory.V.CF.phiLe p P hP M hM
  have hcardQ : Nat.card (P ⧸ M) = p := by rw [← Subgroup.index_eq_card, hMi]
  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by simp
  let e : (P ⧸ M) ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcardQ hcardZ
  let f : P →* Multiplicative (ZMod p) := e.toMonoidHom.comp (QuotientGroup.mk' M)
  have hKf : K ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have : (QuotientGroup.mk' M x) = 1 := (QuotientGroup.eq_one_iff x).mpr (hKM hx)
    show e (QuotientGroup.mk' M x) = 1
    rw [this, map_one]
  have hf1 := hK f hKf
  apply hM.1
  rw [eq_top_iff]
  intro x _
  have hx : f x = 1 := by rw [hf1]; rfl
  have : QuotientGroup.mk' M x = 1 := e.injective (by simpa [f] using hx)
  exact (QuotientGroup.eq_one_iff x).mp this
