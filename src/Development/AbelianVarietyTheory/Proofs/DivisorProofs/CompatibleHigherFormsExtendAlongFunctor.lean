module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatFamilyExtend
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory

theorem compat_forms_extend : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), ∀ (j : ℕ), (∀ (T : C) (x : (FormExtJ.omjExt F j).obj T), (∀ t (u : T ⟶ G.obj t), mp (FormExtJ.omjExt F j) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (FormExtJ.omjExt F j).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (FormExtJ.omjExt F j) (G.map a) (s t u)) → ∃ x : (FormExtJ.omjExt F j).obj T, ∀ t u, mp (FormExtJ.omjExt F j) u x = s t u) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) j, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F j (G.map a) (η' t)) → ∃ η : W0 F j, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F j φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) := by
  intro R _ C _ C' _ F G j hsep hglue η' hη'
  obtain ⟨g, hg, hgG⟩ := compat_family_extend (FormExtJ.omjExt F j) G hsep hglue
    (fun t ↦ (TrivSqZeroExt.inr (η' t) : (FormExtJ.omjExt F j).obj (G.obj t)))
    (fun t t' a ↦ by rw [FormExtJ.mp_omjExt_inr, ← hη' a])
  refine ⟨fun T ↦ (g T).snd, fun T T' φ ↦ ?_, fun t ↦ ?_⟩
  · show (g T').snd = pOm F j φ (g T).snd
    rw [hg φ, FormExtJ.snd_mp_omjExt]
  · show (g (G.obj t)).snd = η' t
    rw [hgG t]
    rfl

end GlobalTheory
