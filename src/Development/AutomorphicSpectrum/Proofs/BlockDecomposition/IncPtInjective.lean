module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversalStatement
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ElOnto

variable {l : ℕ} [Fact l.Prime]

theorem elMap_full {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (hu : ∀ A, Function.Injective (u.app A)) : (elMap u).Full := by
  refine ⟨fun {X Y} f => ⟨⟨f.1, ?_⟩, rfl⟩⟩
  apply hu
  exact (NatTrans.naturality_apply u ((testι l).map f.1) X.2).trans f.2

theorem elMap_faithful {P P' : PAlg l ⥤ Type} (u : P ⟶ P') : (elMap u).Faithful := by
  refine ⟨fun {X Y} f g h => Functor.Elements.Hom.ext ?_⟩
  have h' := congrArg (fun f => f.hom) h
  exact h'

variable {O : Type} [CommRing O]

theorem inc_pt_injective {F : Fn O} (κ : O →+* OC l) (V : F.Sub) (A : PAlg l) :
    Function.Injective ((V.inc.pt κ).app A) := by
  intro a b h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  exact h'

theorem onto_subEl : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (S : Set 𝒜.A) (k : Bool) (n : ℕ), n ≠ 0 → Onto (subEl κ (Fn.Sub.inter 𝒜.V S)) fun T => ∀ α ∈ S, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 := by
  intro l _ O _ F κ d 𝒜 S k n hn
  refine ⟨elMap_full _ (inc_pt_injective κ _), elMap_faithful _, ?_, ?_⟩
  · intro T α hα
    exact (𝒜.V α).in_map _ (T.2.1.2 α hα)
  · intro T hT
    obtain ⟨hs, hj⟩ := (GlobalTheory.T.period_ring_base_change_from_universal T.1.obj n).2.2.2.2.2.2 k hn
    refine ⟨⟨⟨⟨T.2.1, fun α hα => 𝒜.jac α _ _ (CommRingCat.ofHom (uJ k T.1.obj n)) T.2.1 hs hj (hT α hα)⟩, T.2.2⟩⟩, ⟨Iso.refl _⟩⟩

end GlobalTheory.CompanionTheory.ElOnto
