module

public import Development.EtaleCohomology.TateTwists.EtaleShortComplexExactIffLocallySurjectiveOnKern
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem stair_loc_bind (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hSP⟩ := hP
  refine ⟨Sieve.bind S.arrows (fun V g hg => Classical.choose (h V g (hSP V g hg))), ?_, ?_⟩
  · exact (Scheme.etaleTopology).bind_covering hS (fun V g hg => (Classical.choose_spec (h V g (hSP V g hg))).1)
  · rintro W f ⟨V, k, g, hg, hk, rfl⟩
    exact (Classical.choose_spec (h V g (hSP V g hg))).2 W k hk

theorem stair_loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

theorem stair_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.map φ (Sec.res g y) = Sec.res g (Sec.map φ y) := by
  have := congrArg (fun m => (ModuleCat.Hom.hom m) y) (φ.hom.naturality g.op)
  simpa using this.symm

theorem stair_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y := by
  simp [Sec.res]

def EtaleTensorCyclesLocallyLiftOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    ∀ (w : ℤ) (U : Scheme.{0}) (x : Tens C J U w), Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ z : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z = Sec.res g (τ.lift U w x)

theorem etale_tensor_complex_locally_exact_of_lifted_sections (hL : EtaleTensorCyclesLocallyLiftOfFlatBounded) : EtaleTensorComplexLocallyExactOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC w U y hy
  refine stair_loc_bind U _ _ (hτ.1 U w y) ?_
  rintro V g ⟨x, hx⟩
  have hcyc : Sec.map (T.sc w).g (τ.lift V w x) = 0 := by
    have h1 := stair_map_res (T.sc w).g g y
    have h2 : Sec.map (T.sc w).g (τ.lift V w x) = Sec.map (T.sc w).g (Sec.res g y) := congrArg _ hx
    refine h2.trans (h1.trans ?_)
    rw [hy]
    simp
  refine stair_loc_mono V _ _ (hL R a b τ hτ hJ hC w V x hcyc) ?_
  rintro W k ⟨z, hz⟩
  refine ⟨z, ?_⟩
  exact hz.trans ((congrArg (Sec.res k) hx).trans (stair_res_res k g y))

end LateralTheory.EtaleFoundations
