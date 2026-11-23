module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCohomologyContinuousOnConeOfLevelwiseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackLv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagram
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.CcStep

theorem cc_step : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r ∧ ContCone R F ((bc (sch.map r)).mapCone c)) → ContCone R F ((bc p).mapCone c) := by
  intro R _ F S E p I _ _ G c h
  apply GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise R F I (G ⋙ bc p) ((bc p).mapCone c)
  intro k
  obtain ⟨X, r, e, he, hc⟩ := h k
  obtain ⟨φ⟩ := GlobalTheory.EtC.BcLevel.bc_level S E p k X r e he
  have hiso := (GlobalTheory.EtC.eqv_basic R F).1
  refine (GlobalTheory.EtC.ContCone.iff_of_eqv R F I (G ⋙ bc (sch.map r)) ((G ⋙ bc p) ⋙ (evaluation _ PSh).obj k ⋙ disc)
    ((bc (sch.map r)).mapCone c) (((evaluation _ PSh).obj k ⋙ disc).mapCone ((bc p).mapCone c))
    (Functor.whiskerLeft G φ.hom) (φ.hom.app c.pt) ?_ ?_ ?_).1 hc
  · intro i
    exact φ.hom.naturality (c.π.app i)
  · intro i
    exact hiso _ _ _ inferInstance
  · exact hiso _ _ _ inferInstance

end GlobalTheory.EtC.CcStep
