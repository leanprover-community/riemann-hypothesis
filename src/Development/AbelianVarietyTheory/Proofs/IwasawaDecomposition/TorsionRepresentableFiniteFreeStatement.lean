module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFree
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsion_representable_finite_free : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : Type) [CommRing O] [HenselianLocalRing O] (x : Sp O ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (u : overAt x A ⟶ G), Module.Finite O A ∧ Module.Free O A ∧ u ^ q = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (g : overAt x B ⟶ G), g ^ q = 1 → ∃! φ : A →ₐ[O] B, homAt x φ ≫ u = g := by
  first | exact @GlobalTheory.TorsionRep.exists_finite_free_torsion_rep | exact GlobalTheory.TorsionRep.exists_finite_free_torsion_rep | (intros; apply GlobalTheory.TorsionRep.exists_finite_free_torsion_rep <;> assumption)
