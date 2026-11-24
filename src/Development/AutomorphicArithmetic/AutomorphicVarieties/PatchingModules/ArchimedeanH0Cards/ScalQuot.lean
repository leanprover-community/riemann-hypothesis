module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.scal_quot {R R' V : Type} [CommRing R] [CommRing R'] [AddCommGroup V]
    [Module R V] [Module R' V] (Z B : Submodule R V) (Z' B' : Submodule R' V)
    (hZ : ∀ v, v ∈ Z ↔ v ∈ Z') (hB : ∀ v, v ∈ B ↔ v ∈ B') :
    ∃ e : (Z ⧸ B.comap Z.subtype) ≃+ (Z' ⧸ B'.comap Z'.subtype),
      ∀ (z : Z) (z' : Z'), z.1 = z'.1 → e (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  let f : Z ≃+ Z' :=
    { toFun := fun z => ⟨z.1, (hZ _).1 z.2⟩
      invFun := fun z => ⟨z.1, (hZ _).2 z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hf : (B.comap Z.subtype).toAddSubgroup.map (f : Z →+ Z') = (B'.comap Z'.subtype).toAddSubgroup := by
    ext z'
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hB _).1 hz
    · intro hz
      exact ⟨f.symm z', (hB _).2 hz, rfl⟩
  refine ⟨QuotientAddGroup.congr _ _ f hf, fun z z' h => ?_⟩
  have : z' = f z := Subtype.ext h.symm
  subst this
  rfl

theorem UpperTheory.V.Pa.B2.scal :
    ∀ (A G : Type) [CommRing A] [Group G] [TopologicalSpace G] (M : FRep A G) (N : ℕ) [Module (ZMod N) M.X], ContAction (GlobalTheory.Published.zmodRep N M.ρ) ∧ Nonempty (H0 M.ρ ≃+ H0 (GlobalTheory.Published.zmodRep N M.ρ)) ∧ (∃ e : H1 M.ρ ≃+ H1 (GlobalTheory.Published.zmodRep N M.ρ), ∀ (z : Z1 M.ρ) (z' : Z1 (GlobalTheory.Published.zmodRep N M.ρ)), z.1 = z'.1 → e (Submodule.Quotient.mk z) = Submodule.Quotient.mk z') ∧ ∃ e : H2 M.ρ ≃+ H2 (GlobalTheory.Published.zmodRep N M.ρ), ∀ (z : Z2 M.ρ) (z' : Z2 (GlobalTheory.Published.zmodRep N M.ρ)), z.1 = z'.1 → e (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  intro A G _ _ _ M N _
  refine ⟨M.cont, ⟨?_⟩, ?_, ?_⟩
  · exact
      { toFun := fun z => ⟨z.1, z.2⟩
        invFun := fun z => ⟨z.1, z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
  · exact UpperTheory.V.Pa.B2.scal_quot _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  · exact UpperTheory.V.Pa.B2.scal_quot _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
