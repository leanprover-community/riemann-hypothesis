module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BarKHomSurjective
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.Published GlobalTheory.IdemAdj

namespace GlobalTheory.IdemAdj

theorem typeClosure_of_intertwine : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) (U : Submodule ℂ π.V), FiniteDimensional ℂ U → (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) → ∀ f : π.V →ₗ[ℂ] π.V, (∀ k, ∀ u ∈ U, f (cptOn π k u) = cptOn π k (f u)) → ∀ u ∈ U, (∀ g, (fun k : Kinf E a => (cptRep E a k u.1).1 g) ∈ AutFin.coeffSpan ρ₀) → ∀ g, (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) ∈ AutFin.coeffSpan ρ₀ := by
  intro E _ _ _ a π W _ _ ρ₀ U hU hst f hf u hu hcoef g
  haveI := hU
  let w : Kinf E a → U := fun k => ⟨cptOn π k u, hst k u hu⟩
  let A : (U →ₗ[ℂ] ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
    { toFun := fun ℓ k => ℓ (w k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ev : GA E a → (U →ₗ[ℂ] ℂ) := fun h =>
    (LinearMap.proj h).comp ((Sm E a).subtype.comp (π.V.subtype.comp U.subtype))
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    haveI hfr : Module.Free ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) :=
      Module.Free.of_divisionRing ℂ _
    haveI : Module.Projective ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) :=
      @Module.Projective.of_free _ _ _ _ _ hfr
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push_neg at hc
    exact hz (Subtype.ext (Subtype.ext (Subtype.ext (funext fun h => hc _ ⟨h, rfl⟩))))
  let L : U →ₗ[ℂ] ℂ :=
    (LinearMap.proj g).comp ((Sm E a).subtype.comp (π.V.subtype.comp (f.comp U.subtype)))
  have hL : L ∈ (AutFin.coeffSpan ρ₀).comap A := by
    have hmem : L ∈ Submodule.span ℂ (Set.range ev) := hspan ▸ Submodule.mem_top
    refine (Submodule.span_le.2 ?_) hmem
    rintro _ ⟨h, rfl⟩
    exact hcoef h
  have key : (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) = A L := by
    funext k
    show _ = (f (cptOn π k u)).1.1 g
    rw [hf k u hu, cptOn_val]
  rw [key]
  exact hL

end GlobalTheory.IdemAdj
