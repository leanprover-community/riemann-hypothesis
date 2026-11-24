module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
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

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem mem_FO_assembled_iff :
    ∀ (X : Stages) (z : ℂ), z ∈ FO X.toD7 ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z := by
  intro X z
  have hphi : ∀ y : 𝓞 X.B.Ks, X.toD7.what₂.phiO y = X.B.embLL ((y : X.B.Ks) : X.B.LL) := fun _ => rfl
  constructor
  · intro hz
    have hle : FO X.toD7 ≤ X.B.Ks.map X.B.embLL.toRatAlgHom := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, rfl⟩
      exact ⟨((show 𝓞 X.B.Ks from y : X.B.Ks) : X.B.LL), SetLike.coe_mem _, (hphi y).symm⟩
    obtain ⟨x, hx, rfl⟩ := hle hz
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) (⟨x, hx⟩ : X.B.Ks)
    have hx' : x = ((a : X.B.Ks) : X.B.LL) / ((b : X.B.Ks) : X.B.LL) := by
      have := congrArg (fun t : X.B.Ks => (t : X.B.LL)) hab
      exact this.symm
    rw [hx', map_div₀, ← hphi a, ← hphi b]
    exact div_mem (phiO_mem_FO _ _) (phiO_mem_FO _ _)

end GlobalTheory.Mem
