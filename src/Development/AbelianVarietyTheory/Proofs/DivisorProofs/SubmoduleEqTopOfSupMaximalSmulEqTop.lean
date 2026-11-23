module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maximal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory

theorem submodule_eq_top_of_sup_maximal_smul_eq_top :
    ∀ (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
      (M : Submodule R N), (∀ m : Ideal R, m.IsMaximal → M ⊔ m • ⊤ = ⊤) → M = ⊤ := by
  intro R _ N _ _ _ M h

  have hQ : ∀ m : Ideal R, m.IsMaximal → (⊤ : Submodule R (N ⧸ M)) ≤ m • ⊤ := by
    intro m hm
    have h1 := congrArg (Submodule.map M.mkQ) (h m hm)
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
    have h2 : Submodule.map M.mkQ M = ⊥ := Submodule.mkQ_map_self M
    rw [h2, bot_sup_eq] at h1
    rw [h1]
  have hfg : (⊤ : Submodule R (N ⧸ M)).FG := Module.Finite.fg_top
  have hann : Module.annihilator R (N ⧸ M) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤ hfg (hQ m hm)
    have hrm : r ∈ m := hle (Module.mem_annihilator.mpr fun q => hr q Submodule.mem_top)
    have : (1 : R) ∈ m := by
      have := m.sub_mem hrm hr1
      simpa using this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr this)
  rw [eq_top_iff]
  intro n _
  have h1 : (1 : R) ∈ Module.annihilator R (N ⧸ M) := hann ▸ Submodule.mem_top
  have h0 : (Submodule.Quotient.mk n : N ⧸ M) = 0 := by
    simpa using Module.mem_annihilator.mp h1 (Submodule.Quotient.mk n)
  exact (Submodule.Quotient.mk_eq_zero M).mp h0

end GlobalTheory
