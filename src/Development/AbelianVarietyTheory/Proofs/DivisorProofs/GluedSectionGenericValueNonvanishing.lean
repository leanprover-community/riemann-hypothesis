module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl.Glued

theorem valF_resG {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) {U W : X.Opens} (h : W ≤ U) (f : Γ(X, U))
    (hy : ⊤ ≤ y ⁻¹ᵁ W) : valF y W (resG X h f) = valF y U f := by
  have hU : ⊤ ≤ y ⁻¹ᵁ U := fun a ha => h (hy ha)
  unfold valF
  rw [dite_eq_left hy, dite_eq_left hU]
  congr 1
  show (X.presheaf.map (homOfLE h).op ≫ y.appLE W ⊤ hy).hom f = _
  rw [Scheme.Hom.map_appLE]

theorem glued : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S)
    (V : S.Opens) (κ : Type) (N : κ → S.Opens) (s : ∀ k, LocSec G L (N k)) (s' : LocSec G L V)
    (v : SecM G L 1 (Over.mk ξ)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V →
    (∀ k i, resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i) →
    (∀ k, GenIs ξ (s k) v) → (∀ k, FibNz (s k) (N k)) → (Nonempty κ → GenIs ξ s' v) ∧ FibNz s' V := by
  intro S G _ L K _ ξ V κ N s s' v hN hsup hres hgen hnz
  refine ⟨fun ⟨k⟩ => ?_, ?_⟩
  · obtain ⟨hξk, hk⟩ := hgen k
    refine ⟨hξk.trans (hN k), ?_⟩
    rw [← hk]
    funext j
    unfold genPull
    rw [← hres k (j 0)]
    show _ = (G.left.presheaf.map _ ≫ (snd (Over.mk ξ) G).left.appLE _ _ _).hom (s' (j 0))
    rw [Scheme.Hom.map_appLE]
  · intro K' _ _ x hx
    obtain ⟨p⟩ : Nonempty (Sp K') := inferInstance
    have hp : x p ∈ (⨆ k, N k : S.Opens) := hsup ▸ hx ⟨p, rfl⟩
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
    have hxk : Set.range x ⊆ N k := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q p]
      exact hk
    obtain ⟨y, i, hyx, hyr, hval⟩ := hnz k K' x hxk
    refine ⟨y, i, hyx, fun z hz => ⟨(hyr hz).1, hN k (hyr hz).2⟩, ?_⟩
    rw [← hres k i] at hval
    convert hval using 1
    exact (valF_resG y _ (s' i) ((GlobalTheory.ZH.top_le_preimage_iff _ _).2 hyr)).symm

end GlobalTheory.UMin.ThBdl.Glued
