module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegZeroCocycleExistsCoboundaryOfRichBasedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantCochainOneConstOnDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterFunctionEqZeroOfComposableStatement
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_perCl {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hR : K.Rich) (hB : K.Based) (c : H1 K.Oc) : ∃ per : Λ →+ Hol F.V, c = K.perCl per := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective K.Oc c
  obtain ⟨G, hG⟩ := GlobalTheory.T.degZeroCocycle_exists_coboundary_of_rich_based K hR hB f.1 (fun T T' T'' φ ψ _ _ ↦ f.2 φ ψ)
  let f' : Z1 K.Oc := f - ⟨d0 K.Oc G, commAlgFunctorCoboundaryZero_mem_cocyclesOne K.Oc G⟩
  have hv : ∀ (T T' : K.Obj) (φ : T ⟶ T'), f'.1 T T' φ = f.1 T T' φ - (G T' - φ.φ (G T)) :=
    fun _ _ _ ↦ rfl
  have h0 : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → f'.1 T T' φ = 0 := by
    intro T T' φ hφ
    rw [hv, hG T T' φ hφ, sub_self]
  have hc : ∀ {T T' T'' : K.Obj} (φ : T ⟶ T') (ψ : T' ⟶ T''),
      f'.1 T T'' (φ ≫ ψ) = ψ.φ (f'.1 T T' φ) + f'.1 T' T'' ψ := fun φ ψ ↦ f'.2 φ ψ
  have hp : ∀ l : Λ, ∃ p : Hol F.V, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = l →
      f'.1 T T' φ = algebraMap (Hol F.V) T'.C p :=
    fun l ↦ GlobalTheory.T.invariant_cochainOne_const_on_degree K hR f'.1 l
      (fun T T' T'' φ ψ _ hψ ↦ by rw [hc, h0 _ _ ψ hψ, add_zero])
      (fun T T' T'' φ ψ hφ _ ↦ by rw [hc, h0 _ _ φ hφ, map_zero, zero_add])
  choose p hp using hp
  have hcom : ∀ {T T' : K.Obj} (ψ : T ⟶ T') (x : Hol F.V),
      ψ.φ (algebraMap (Hol F.V) T.C x) = algebraMap (Hol F.V) T'.C x := fun ψ x ↦ ψ.φ.commutes x
  have hadd : ∀ l m, p (l + m) = p l + p m := by
    intro l m
    rw [← sub_eq_zero]
    refine GlobalTheory.T.parameter_function_eq_zero_of_composable K hR l m _ fun k k' k'' hl hm ↦ ?_
    let φ : K.triv k ⟶ K.triv k' := ptHom (K.triv k') hl
    let ψ : K.triv k' ⟶ K.triv k'' := ptHom (K.triv k'') hm
    have e := hc φ ψ
    rw [hp (l + m) _ _ (φ ≫ ψ) rfl, hp l _ _ φ rfl, hp m _ _ ψ rfl, hcom ψ] at e
    change K.cst k'' (p (l + m)) = K.cst k'' (p l) + K.cst k'' (p m) at e
    rw [(K.cst k'').map_sub, (K.cst k'').map_add, e, sub_self]
  refine ⟨AddMonoidHom.mk' p hadd, ?_⟩
  rw [perCl, H1.mk_eq_mk]
  refine ⟨G, ?_⟩
  funext T T' φ
  have e := hp φ.deg T T' φ rfl
  rw [hv] at e
  change G T' - φ.φ (G T) = f.1 T T' φ - algebraMap (Hol F.V) T'.C (p φ.deg)
  rw [← e]
  ring

end GlobalTheory.AnPer.Charts
