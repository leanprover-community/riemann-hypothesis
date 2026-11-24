module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂

namespace SncBlowup

def IsSncCentre {X : Scheme.{0}} (E : Closeds X) (Z : X.IdealSheafData) : Prop :=
  ∀ x ∈ Z.support, ∃ (U : X.affineOpens) (hx : x ∈ U.1) (n : ℕ) (z : Fin n → Γ(X, U.1)) (J J' : Finset (Fin n)),
    FinalTheorems.Rsp (X.presheaf.stalk x) n (fun i => X.presheaf.germ U.1 x hx (z i)) ∧
      (Scheme.IdealSheafData.vanishingIdeal E).ideal U = Ideal.span {∏ j ∈ J, z j} ∧
      Z.ideal U = Ideal.span (z '' (J' : Set (Fin n)))

def totalTransform {X X' : Scheme.{0}} (π : X' ⟶ X) (Z : X.IdealSheafData) (E : Closeds X) : Closeds X' :=
  (E ⊔ Z.support).preimage π.continuous

inductive IsSncBlowupSeq {S X : Scheme.{0}} (g : X ⟶ S) (E : Closeds X) :
    ∀ {X' : Scheme.{0}}, (X' ⟶ X) → Closeds X' → Prop

  | id : IsSncBlowupSeq g E (𝟙 X) E

  | step {X₁ X₂ : Scheme.{0}} {s : X₁ ⟶ X} {E₁ : Closeds X₁} (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁) :
      IsSncBlowupSeq g E s E₁ → Smooth (s ≫ g) → Smooth (Z.subschemeι ≫ s ≫ g) → IsSncCentre E₁ Z →
      FinalTheorems.Blowup π Z → IsSncBlowupSeq g E (π ≫ s) (totalTransform π Z E₁)

theorem IsSncBlowupSeq.isSmoothBlowupSeq {S X X' : Scheme.{0}} {g : X ⟶ S} {E : Closeds X} {s : X' ⟶ X}
    {E' : Closeds X'} (h : IsSncBlowupSeq g E s E') : IsSmoothBlowupSeq g Set.univ s := by
  induction h with
  | id => exact IsSmoothBlowupSeq.id
  | step Z π _ _ hZ _ hB ih => exact IsSmoothBlowupSeq.step Z π ih hZ (Set.subset_univ _) hB

end SncBlowup

open SncBlowup

def PrincipalisationCharZero : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp k),
    SmoothOfRelativeDimension d g → QuasiCompact g → IsSeparated g →
    ∀ (I : X.IdealSheafData) (E : Closeds X),
      (∀ C ∈ irreducibleComponents X, ¬ C ⊆ (I.support : Set X)) →
      (∀ x ∈ E, FinalTheorems.SncAt (Scheme.IdealSheafData.vanishingIdeal E) x) →
      ∃ (X' : Scheme.{0}) (s : X' ⟶ X) (E' : Closeds X'),
        IsSncBlowupSeq g E s E' ∧ Smooth (s ≫ g) ∧
        FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support) ∧
        IsIso (s ∣_ I.support.compl)

namespace SncBlowup

theorem not_subset_of_dense_compl {X : Type*} [TopologicalSpace X] [NoetherianSpace X] {T : Set X}
    (hT : Dense Tᶜ) : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ T := fun C hC h => by
  obtain ⟨o, ho, hne, hoC⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  obtain ⟨x, hx, hxT⟩ := hT.inter_open_nonempty o ho hne
  exact hxT (h (hoC hx))

theorem not_subset_of_ne_bot {X : Scheme.{0}} [IsIntegral X] {I : X.IdealSheafData} (hI : I ≠ ⊥) :
    ∀ C ∈ irreducibleComponents X, ¬ C ⊆ (I.support : Set X) := by
  intro C hC hsub
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hC
  subst hC
  apply hI
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  ext x
  simp only [TopologicalSpace.Closeds.coe_top, Set.mem_univ, iff_true]
  exact hsub (Set.mem_univ x)

end SncBlowup

end GlobalTheory.CompanionTheory.Hypotheses₂
