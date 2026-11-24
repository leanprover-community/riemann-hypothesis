module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreSide
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem aux {R Q M : Type} [CommRing R] [Group Q] [AddCommGroup M] [Module R M]
    (π : Representation R Q M) (H : Subgroup Q) (f : Q → M) (hf : ∀ g h, f (g * h) = f g + π g (f h))
    (h0 : ∀ u ∈ H, f u = 0) : ∃ m, ∀ g, H.index • f g = π g m - m :=
  _root_.UpperTheory.Reformulated.B.Qi36.aux π H f hf h0

theorem UpperTheory.V.Base.kerResSmul :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (x : H1U ρ U), resU ρ h x = 0 → U'.relIndex U • x = 0 := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 hx
  obtain ⟨s, hs⟩ := aux (ρ.comp U.subtype : Representation R U M) (U'.subgroupOf U)
    (fun u => z.1 u - (ρ u m - m))
    (fun g k => by
      have e : z.1 (g * k) = z.1 g + ρ g (z.1 k) := z.2.2 g k
      show z.1 (g * k) - (ρ ((g : G) * k) m - m) = z.1 g - (ρ g m - m) + ρ g (z.1 k - (ρ k m - m))
      rw [e, map_mul, Module.End.mul_apply, map_sub, map_sub]
      abel)
    (fun u hu => sub_eq_zero.2 (hm ⟨u.1, hu⟩))
  have e0 : U'.relIndex U • (Submodule.Quotient.mk z : H1U ρ U) = Submodule.Quotient.mk (U'.relIndex U • z) :=
    (map_nsmul (Submodule.mkQ _) _ z).symm
  rw [e0, Submodule.Quotient.mk_eq_zero]
  refine (mem_coboundaries1 _ _).2 ⟨s + U'.relIndex U • m, fun g => ?_⟩
  have e : U'.relIndex U • (z.1 g - (ρ g m - m)) = ρ g s - s := hs g
  show U'.relIndex U • z.1 g = ρ g (s + U'.relIndex U • m) - (s + U'.relIndex U • m)
  rw [smul_sub, smul_sub, sub_eq_iff_eq_add] at e
  rw [e, map_add (f := _), map_nsmul]
  abel
