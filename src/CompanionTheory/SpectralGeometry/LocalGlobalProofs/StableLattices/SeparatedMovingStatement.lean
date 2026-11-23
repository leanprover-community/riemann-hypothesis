module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

variable {G G' : Type} [Group G] [Group G']

def cosetEquiv (e : G ≃* G') (K : Subgroup G) : G ⧸ K ≃ G' ⧸ K.map e.toMonoidHom :=
  Quotient.congr (ra := QuotientGroup.leftRel K) (rb := QuotientGroup.leftRel (K.map e.toMonoidHom))
    e.toEquiv (by
      intro a b
      have h : (e.toEquiv a)⁻¹ * e.toEquiv b = e.toMonoidHom (a⁻¹ * b) := by simp
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, h]
      exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm)

lemma cosetEquiv_smul (e : G ≃* G') (K : Subgroup G) (g : G) (x : G ⧸ K) :
    cosetEquiv e K (g • x) = e g • cosetEquiv e K x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    change ((e (g * a) : G') : G' ⧸ K.map e.toMonoidHom) = ((e g * e a : G') : G' ⧸ K.map e.toMonoidHom)
    rw [map_mul]

theorem stSepMove : StSepMove := by
  intro G G' _ _ e K hK S
  classical
  let φ := cosetEquiv e K
  obtain ⟨Γ', hfin, hstab, hsep⟩ := hK (S.image φ)
  let Γ : Subgroup G := Γ'.comap e.toMonoidHom
  have hmem : ∀ γ : Γ, e (γ : G) ∈ Γ' := fun γ => γ.2
  have hsymm : ∀ γ' : Γ', e.symm (γ' : G') ∈ Γ := fun γ' => by
    change e (e.symm (γ' : G')) ∈ Γ'
    simpa using γ'.2
  have hact : ∀ (γ : Γ) (x : G ⧸ K), φ (γ • x) = (⟨e (γ : G), hmem γ⟩ : Γ') • φ x := fun γ x =>
    cosetEquiv_smul e K (γ : G) x
  refine ⟨Γ, ?_, ?_, ?_⟩
  · let f : MulAction.orbitRel.Quotient Γ' (G' ⧸ K.map e.toMonoidHom) →
        MulAction.orbitRel.Quotient Γ (G ⧸ K) :=
      Quotient.map' φ.symm (by
        rintro a b ⟨γ', rfl⟩
        refine ⟨⟨e.symm (γ' : G'), hsymm γ'⟩, ?_⟩
        apply φ.injective
        change φ (_ • φ.symm b) = φ (φ.symm (γ' • b))
        rw [hact]
        have h : (⟨e (e.symm (γ' : G')), hmem ⟨e.symm (γ' : G'), hsymm γ'⟩⟩ : Γ') = γ' :=
          Subtype.ext (e.apply_symm_apply _)
        rw [h, φ.apply_symm_apply, φ.apply_symm_apply])
    refine Finite.of_surjective f ?_
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      exact ⟨Quotient.mk'' (φ x),
        congrArg (Quotient.mk'' (s₁ := MulAction.orbitRel Γ (G ⧸ K))) (φ.symm_apply_apply x)⟩
  · intro x
    let f : MulAction.stabilizer Γ x → MulAction.stabilizer Γ' (φ x) := fun γ =>
      ⟨⟨e ((γ : Γ) : G), hmem γ⟩, by
        rw [MulAction.mem_stabilizer_iff, ← hact, MulAction.mem_stabilizer_iff.mp γ.2]⟩
    refine Finite.of_injective f ?_
    intro a b hab
    have h := congrArg (fun c : MulAction.stabilizer Γ' (φ x) => ((c : Γ') : G')) hab
    exact Subtype.ext (Subtype.ext (e.injective h))
  · intro x hx y hy γ hxy
    apply φ.injective
    exact hsep (φ x) (Finset.mem_image_of_mem φ hx) (φ y) (Finset.mem_image_of_mem φ hy)
      ⟨e (γ : G), hmem γ⟩ (by rw [← hact, hxy])

end GlobalTheory.CompanionTheory.RgFl
