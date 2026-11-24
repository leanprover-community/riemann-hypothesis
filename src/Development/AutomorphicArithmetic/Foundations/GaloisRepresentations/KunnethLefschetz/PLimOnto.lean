module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.limOnto_holds :
    UpperTheory.Gal.KunnethLefschetz.LimOnto := by
  intro A B _ ra rb f hf z hz hsurj
  let F : ℕ → Type 1 := fun j => {a : A j // f j a = z j}
  let g : ∀ n, F (n + 1) → F n := fun n a =>
    ⟨ra n a.1, by rw [← hf, a.2, hz]⟩
  let G : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence (X := F) (fun n => TypeCat.ofHom (g n))
  haveI : ∀ j : ℕᵒᵖ, Finite (G.obj j) := fun j => (inferInstance : Finite (F j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (G.obj j) := fun j => by
    obtain ⟨a, ha⟩ := hsurj j.unop
    exact ⟨(⟨a, ha⟩ : F j.unop)⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system G
  refine ⟨fun j => (s (Opposite.op j) : F j).1, fun j => ?_, fun j => (s (Opposite.op j) : F j).2⟩
  have h1 := hs (homOfLE (Nat.le_succ j)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h1
  have h2 := congrArg Subtype.val h1
  exact h2
