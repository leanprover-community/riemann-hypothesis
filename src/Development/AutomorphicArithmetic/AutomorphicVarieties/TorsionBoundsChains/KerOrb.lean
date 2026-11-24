module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
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

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.kerOrb :
    ∀ (G X : Type) [Group G] [MulAction G X],
      LinearMap.ker (Finsupp.lmapDomain ℤ ℤ
        (Quotient.mk (MulAction.orbitRel G X) : X → MulAction.orbitRel.Quotient G X)) =
      Representation.Coinvariants.ker (perm G X) := by
  intro G X _ _
  set q : X → MulAction.orbitRel.Quotient G X := Quotient.mk (MulAction.orbitRel G X) with hq
  set K := Representation.Coinvariants.ker (perm G X) with hK
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker, Finsupp.lmapDomain_apply] at hf
    let r : X → X := fun x => Quotient.out (q x)
    have hstep : ∀ f : X →₀ ℤ, f - Finsupp.mapDomain r f ∈ K := by
      intro f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
        rw [Finsupp.mapDomain_add]
        have := K.add_mem ha hb
        convert this using 1
        abel
      | single x c =>
        rw [Finsupp.mapDomain_single]
        have hx : (MulAction.orbitRel G X) (r x) x := Quotient.mk_out (s := MulAction.orbitRel G X) x
        obtain ⟨g, hg⟩ := hx
        have hg' : g • x = r x := hg
        have hmem := Representation.Coinvariants.mem_ker_of_eq (ρ := perm G X) g
          (Finsupp.single x c) _ rfl
        have hneg := K.neg_mem hmem
        convert hneg using 1
        rw [perm_single, hg']
        abel
    have h0 : Finsupp.mapDomain r f = 0 := by
      have : r = (fun c => Quotient.out c) ∘ q := rfl
      rw [this, Finsupp.mapDomain_comp, hf, Finsupp.mapDomain_zero]
    have := hstep f
    rwa [h0, sub_zero] at this
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change Finsupp.lmapDomain ℤ ℤ q ((perm G X) g v - v) = 0
    rw [map_sub, perm_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
      ← Finsupp.mapDomain_comp]
    have : q ∘ (fun x => g • x) = q := by
      funext x
      exact Quotient.sound ⟨g, rfl⟩
    rw [this, sub_self]
