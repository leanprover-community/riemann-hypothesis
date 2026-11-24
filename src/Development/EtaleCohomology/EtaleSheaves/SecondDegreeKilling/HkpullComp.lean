module

public import Development.EtaleCohomology.EtaleSheaves.LeafGhostCut
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.SecondDegreeKilling.Comp
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut CochainComplex.HomComplex

theorem hkpull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f' f'' u' e' comm' ≫ rmap R f f' u e comm = rmap R f f'' (u' ≫ u) (e' ≫ e) comm'' := by
  simp only [rmap]
  convert (CochainComplex.mappingCone.map_comp (φ₁ := (chains R).map f'') (φ₂ := (chains R).map f')
    (φ₃ := (chains R).map f) (a := (chains R).map u') (b := (chains R).map e') (a' := (chains R).map u)
    (b' := (chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm'])
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm])).symm using 2 <;> simp [Functor.map_comp]

theorem rpull_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    rpull R f' f'' u' e' comm' F n (rpull R f f' u e comm F n y) = rpull R f f'' (u' ≫ u) (e' ≫ e) comm'' F n y := by
  simp only [rpull]
  rw [← hkpull_comp, rmap_comp]

theorem rpl_comp (q : ℕ) (i : ℤ) {U E U' E' U'' E'' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (n : ℤ) (y : Hrel (ZMod q) (sch.map f) (tw q i) n) :
    rpl q i f' f'' u' e' comm' n (rpl q i f f' u e comm n y) = rpl q i f f'' (u' ≫ u) (e' ≫ e) comm'' n y := by
  simp only [rpl]
  rw [rpull_comp (ZMod q) _ _ _ _ _ _ _ _ _ (by simp only [← Functor.map_comp]; rw [comm''])]
  simp only [Functor.map_comp]
