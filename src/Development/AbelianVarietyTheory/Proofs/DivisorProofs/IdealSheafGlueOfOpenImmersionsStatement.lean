module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersions
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.exists_idealSheafData_glue_of_openImmersions : (∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) → (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)), (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W), (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') → ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W) → ∀ {X : Scheme.{0}} {ι : Type*} (P : ι → Scheme.{0}) (e : ∀ i, P i ⟶ X), (∀ i, IsOpenImmersion (e i)) → (∀ x : X, ∃ i, x ∈ Set.range (e i)) → ∀ (K : ∀ i, (P i).IdealSheafData), (∀ i j (Q : Scheme.{0}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j → (K i).comap a = (K j).comap b) → ∃ I : X.IdealSheafData, ∀ i, I.comap (e i) = K i := by
  first | (exact @GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions) | (exact GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions) | (intros; apply GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions  <;> assumption)
