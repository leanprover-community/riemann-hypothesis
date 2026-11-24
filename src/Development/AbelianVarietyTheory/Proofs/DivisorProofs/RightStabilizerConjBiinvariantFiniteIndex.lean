module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RStabFin

theorem rStab_conj_index_ne_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G)
    (f : G → ℂ) (δ : G), IsCompact (K : Set G) → IsOpen (K' : Set G) → K' ≤ K →
    (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) → ∀ x : G,
    (rStab fun k : K => f ((x * k)⁻¹ * δ * (x * k))).index ≠ 0 := by
  intro G _ _ _ K K' f δ hK hK' _ hf x
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := hK'.preimage continuous_subtype_val
  have hfin : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  have h0 : (K'.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : K'.subgroupOf K ≤ rStab fun k : K => f ((x * k)⁻¹ * δ * (x * k)) := by
    intro k hk y
    have hk' : ((k : K) : G) ∈ K' := hk
    show f ((x * ((y * k : K) : G))⁻¹ * δ * (x * ((y * k : K) : G))) = f ((x * (y : G))⁻¹ * δ * (x * (y : G)))
    have e : (x * ((y * k : K) : G))⁻¹ * δ * (x * ((y * k : K) : G))
        = ((k : G))⁻¹ * ((x * (y : G))⁻¹ * δ * (x * (y : G)) * (k : G)) := by
      simp only [Subgroup.coe_mul, _root_.mul_inv_rev]; group
    rw [e, (hf _ (inv_mem hk') _).1, (hf _ hk' _).2]
  exact fun h => h0 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))

end GlobalTheory.RStabFin
