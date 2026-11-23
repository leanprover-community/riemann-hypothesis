module

public import Development.EtaleCohomology.TateTwists.EtaleTwistExtendsThroughMonoToResolutionZero
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

noncomputable def twGenR {q : ℕ} (A : CommRingCat.{0}) (ζ : Prim q A) : (twF q 1).obj A :=
  Submodule.Quotient.mk (Finsupp.single ζ 1)

def ExistsEtaleMonoMuTwistKillingRootRelations : Prop :=
  ∀ (q : ℕ) [NeZero q], ∃ (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) ∧
    ∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0

def EtaleMuTwistMonoExtendsToTorsorSheaf : Prop :=
  ∀ (q : ℕ) [NeZero q] (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) →
    (∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) →
    ∃ (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j ∧
    ∃ s : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec M U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
        Sec.res g (s U v) = s V (Units.map g.appTop.hom.toMonoidHom v)) ∧
      ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v →
        s U w = s U v + Sec.map j (twGen 1 ζ)

theorem exists_etale_mono_muTwist_into_torsorSheaf (h1 : ExistsEtaleMonoMuTwistKillingRootRelations) (h2 : EtaleMuTwistMonoExtendsToTorsorSheaf) :
    EtaleKummerSectionsIntoTwistEmbeddingExist := by
  intro q _
  obtain ⟨T, τ, hm, hl⟩ := h1 q
  exact h2 q T τ hm hl
end LateralTheory.EtaleFoundations
