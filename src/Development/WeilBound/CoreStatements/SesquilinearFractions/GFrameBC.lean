module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilEndomorphism
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
public import Development.WeilBound.CoreStatements.SesquilinearFractions.FrameBCLin
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GBridge
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.EigenspaceComposition

theorem epi_spMap {K L : Type} [Field K] [Field L] (a : K →+* L) : Epi (spMap a) := by
  apply GlobalTheory.CompanionTheory.Ar.HtEnd.epiSp <;> assumption

theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (Y : Over S) :
    (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

end PositivityTheory.Xgf.EigenspaceComposition

namespace PositivityTheory.Xgf

private theorem isTanAt_base_change_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] {F F' : Type} [Field F] [Field F']
    (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (hx : x' = spMap f ≫ x)
    (w : epsAt x ⟶ G) (w' : epsAt x' ⟶ G) (hw : w'.left = spMap (dualMap f) ≫ w.left) :
    IsTanAt G x' w' ↔ IsTanAt G x w := by
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F' F' F').toRingHom) ≫ spMap (dualMap f) =
      spMap f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F F F).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    simp [dualMap]
  haveI := EigenspaceComposition.epi_spMap f
  show _ = (1 : Over.mk x' ⟶ G).left ↔ _ = (1 : Over.mk x ⟶ G).left
  rw [EigenspaceComposition.one_left', EigenspaceComposition.one_left', hw, ← Category.assoc, key, Category.assoc]
  simp only [Over.mk_hom, hx, Category.assoc]
  constructor
  · intro h
    exact (cancel_epi (spMap f)).mp h
  · intro h
    rw [h]

open PositivityTheory.Xgf.EigenspaceComposition in
theorem tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  intro E _ _ _ H S t F F' _ _ f x x' τ n v hx'
  have hcomp : ∀ w : epsAt x ⟶ t.G, ∃ w' : epsAt x' ⟶ t.G, w'.left = spMap (dualMap f) ≫ w.left := by
    intro w
    refine ⟨Over.homMk (spMap (dualMap f) ≫ w.left) ?_, rfl⟩
    rw [Category.assoc, Over.w w]
    simp only [epsAt, Over.mk_hom, hx', spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    apply RingHom.ext
    intro a
    simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨⟨fun k => Classical.choose (hcomp (v k)), fun k => Classical.choose_spec (hcomp (v k))⟩, ?_⟩
  intro v' hv'
  have htan : ∀ k, IsTanAt t.G x' (v' k) ↔ IsTanAt t.G x (v k) :=
    fun k => isTanAt_base_change_iff t.G f x x' hx' (v k) (v' k) (hv' k)
  by_cases hT : ∀ k, IsTanAt t.G x (v k)
  · obtain ⟨N, M, ρ, hρ, hbc⟩ := lie_model_action_base_change E H S t F x
    obtain ⟨M', ρ', hρ', hpt, hc⟩ := hbc F' f x' hx'
    choose u hu using fun k => M.onto (v k) (hT k)
    have hv'eq : v' = fun k => M'.pt (f ∘ u k) := by
      funext k
      apply Over.OverMorphism.ext
      rw [hv' k, hpt, hu k]
    have hveq : v = fun k => M.pt (u k) := funext fun k => (hu k).symm
    rw [hv'eq, hveq, ((lie_model_eigenvectors_action S F t.G x _ M).2 _ t.act ρ τ hρ).2 n u,
      ((lie_model_eigenvectors_action S F' t.G x' _ M').2 _ t.act ρ' (f.comp τ) hρ').2 n (fun k => f ∘ u k)]
    exact EigenspaceComposition.core (τ := τ) hc u
  · push_neg at hT
    obtain ⟨k, hk⟩ := hT
    constructor
    · intro h
      exact absurd (h.1 k).1 hk
    · intro h
      exact absurd ((htan k).1 (h.1 k).1) hk

end PositivityTheory.Xgf
