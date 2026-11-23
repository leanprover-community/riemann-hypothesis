module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.CoindRetract

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

def adj : restr φ ⊣ coind φ :=
  Adjunction.restrictFullyFaithful
    ((ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (liftHom φ)).whiskerRight (Scheme.{0}ᵒᵖ))
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _) (Iso.refl _) (Iso.refl _)

instance restr_faithful : (restr φ).Faithful :=
  show (sheafCompose (Scheme.etaleTopology.{0}) (ModuleCat.restrictScalars.{1} (liftHom φ))).Faithful from inferInstance

instance coind_preservesMono : (coind φ).PreservesMonomorphisms := by
  haveI : (coind φ).IsRightAdjoint := (adj φ).isRightAdjoint
  infer_instance

theorem coind_retract (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I] :
    ∃ (J : Shv R) (_ : Injective J) (i : I ⟶ (coind φ).obj J) (r : (coind φ).obj J ⟶ I), i ≫ r = 𝟙 I := by
  let J := Injective.under ((restr φ).obj I)
  let i : I ⟶ (coind φ).obj J := (adj φ).unit.app I ≫ (coind φ).map (Injective.ι ((restr φ).obj I))
  haveI : Mono i := mono_comp _ _
  exact ⟨J, inferInstance, i, Injective.factorThru (𝟙 I) i, Injective.comp_factorThru _ _⟩

end GlobalTheory.EtC.CoindRetract
