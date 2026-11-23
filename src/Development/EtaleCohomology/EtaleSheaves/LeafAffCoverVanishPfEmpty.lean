module

import Development.EtaleCohomology.EtaleSheaves.LeafVanVPf
public import Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

theorem etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme (R : Type) [CommRing R] (E : Scheme.{0}) [IsEmpty E] :
    IsZero ((free R).obj (yoneda.obj E)) := by
  apply LateralTheory.E.LeafVanVPf.free_empty <;> assumption

theorem leafEmptyVanish : LeafEmptyVanish := by
  intro R _ X F n
  have hE : IsEmpty (((⊥ : X.Opens) : Scheme.{0}) : Type) := by
    change IsEmpty ((⊥ : X.Opens) : Set X); simp
  have hfree := etaleFreeSheafOfRepresentable_isZero_of_isEmpty_scheme R ((⊥ : X.Opens) : Scheme.{0})
  have hN : IsZero ((chainsN R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro j
    refine IsZero.eq_of_src ?_ _ _
    exact hfree
  have hC : IsZero ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) :=
    Functor.map_isZero (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) hN
  have hX : ∀ p, IsZero (((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))).X p) := fun p =>
    Functor.map_isZero (HomologicalComplex.eval _ _ p) hC
  have : Subsingleton (Cochain ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n) :=
    ⟨fun a b => Cochain.ext _ _ fun p q hpq => (hX p).eq_of_src _ _⟩
  have : Subsingleton (Cocycle ((chains R).obj (sch.obj ((⊥ : X.Opens) : Scheme.{0}))) (res R F) n) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  change Subsingleton (CohomologyClass _ _ n)
  unfold CohomologyClass
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [Subsingleton.elim a b]

end LateralTheory.E.E8

end
