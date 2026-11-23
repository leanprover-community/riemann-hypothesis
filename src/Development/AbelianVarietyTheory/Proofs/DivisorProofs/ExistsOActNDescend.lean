module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GaloisActDesc

theorem exists_oActN_descend : ∀ (O : Type) [Ring O] (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → (∀ a c, (act.act c).left ≫ ν a = ν a ≫ (act.act c).left) → ∃ act₀ : OActN O A₀, ∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left := by
  intro O _ X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act hπ _ _ hp hφ _ hcomm
  have : Flat π := by have := hπ.etale; infer_instance
  have : Surjective π := hπ.onto
  have eφ : Epi φ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hφ
  have hi : ∀ c, ∃ f : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ f.left := by
    intro c
    obtain ⟨g, hg, -⟩ := hφ.existsUnique_desc ((act.act c).left ≫ φ) (fun a ↦ by
      rw [← Category.assoc, ← hcomm, Category.assoc, hφ.inv])
    have hw : g ≫ A₀.hom = A₀.hom := by
      rw [← cancel_epi φ, reassoc_of% hg, hp.1.w, Over.w_assoc]
    exact ⟨Over.homMk g hw, hg.symm⟩
  choose f hf using hi
  refine ⟨⟨f, fun x ↦ ?_, ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩, hf⟩
  · have := act.hom x
    exact GlobalTheory.ActDescent.isMonHom_descend hp hp (act.act x) (f x) (hf x)
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    let φ₀ : Over.mk (A.hom ≫ π) ⟶ A₀ := Over.homMk φ hp.1.w
    have h := hp.2 A (act.act x) (act.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, act.add, ← h]
    rfl

end GlobalTheory.GaloisActDesc
