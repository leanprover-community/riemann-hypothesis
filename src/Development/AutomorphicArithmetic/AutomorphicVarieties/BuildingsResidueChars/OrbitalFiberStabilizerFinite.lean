module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory

theorem orbitalFiber_stabilizer_finite : UpperTheory.V.Z.Sym.Glob.Fib.StabFin := by
  intro H G _ _ S U U' ι x hS hidx hfin
  let ψ : H →* G := (MulAut.conj x⁻¹).toMonoidHom.comp (S.subtype.comp ι)
  have hψ : ∀ h, ψ h = x⁻¹ * ι h * x := fun h => by simp [ψ]
  have hB : (U' ⊓ S).comap ψ = U'.comap ψ := by
    ext h
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, and_iff_left_iff_imp]
    intro _
    rw [hψ]
    simpa using hS.conj_mem _ (ι h).2 x⁻¹
  have h1 : (U.comap ψ).relIndex (U'.comap ψ) ≠ 0 := by
    rw [← hB]
    exact Subgroup.relIndex_comap_ne_zero ψ hidx
  have hA : Finite (U.comap ψ) := by
    have : ((U.comap ψ : Subgroup H) : Set H).Finite := by
      convert hfin using 1
      ext h
      simp [hψ]
    exact this.to_subtype
  have hA' : Finite ((U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Finite.of_injective (fun a => (⟨a.1.1, a.2⟩ : U.comap ψ)) (fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : U.comap ψ => (z : H)) hab)
  have hq : Finite ((U'.comap ψ) ⧸ (U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Nat.finite_of_card_ne_zero h1
  have hfB : Finite (U'.comap ψ) :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup
      (s := (U.comap ψ).subgroupOf (U'.comap ψ))).symm
  have : ((U'.comap ψ : Subgroup H) : Set H).Finite := Set.toFinite _
  convert this using 1
  ext h
  simp [hψ]

end UpperTheory
