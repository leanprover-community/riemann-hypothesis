module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Components
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Assembly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global FiniteSubfield
  IdeleLimit SemiLocal

open scoped Pointwise NumberField.LiesOver

noncomputable section

variable (K : FiniteSubfield)

structure CompatiblePlaces where

  fin : ∀ (v : HeightOneSpectrum (𝓞 K.1)) (p : GLevel K), PlacesOver p.1.1 v
  fin_liesOver : ∀ v {p q : GLevel K} (h : p ≤ q),
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    (fin v q).1.asIdeal.LiesOver (fin v p).1.asIdeal

  inf : ∀ (v : InfinitePlace K.1) (p : GLevel K), v.placesOver p.1.1
  inf_liesOver : ∀ v {p q : GLevel K} (h : p ≤ q),
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    (inf v q).1.LiesOver (inf v p).1

namespace CompatiblePlaces

variable {K} (P : CompatiblePlaces K) (n : ℕ)

def localGroup : Place K.1 → GLevel K → Type
  | .inl v, p => cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer (p.1.1 ≃ₐ[K.1] p.1.1) (P.inf v p).1) ((P.inf v p).1.Completion)ˣ) n
  | .inr v, p => cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer (p.1.1 ≃ₐ[K.1] p.1.1) (P.fin v p).1.asIdeal)
      ((P.fin v p).1.adicCompletion p.1.1)ˣ) n

instance (v : Place K.1) (p : GLevel K) : AddCommGroup (P.localGroup n v p) := by
  rcases v with v | v <;> exact inferInstanceAs (AddCommGroup (cohomology _ n))

def shapiro : ∀ (v : Place K.1) (p : GLevel K), cohomology (placeRep p.1.1 v) n ≃+ P.localGroup n v p
  | .inl v, p => (infiniteShapiroIso v (P.inf v p) n).toLinearEquiv.toAddEquiv
  | .inr v, p => (finiteShapiroIso v (P.fin v p) n).toLinearEquiv.toAddEquiv

def transition : ∀ (v : Place K.1) {p q : GLevel K}, p ≤ q → P.localGroup n v p →+ P.localGroup n v q
  | .inl v, p, q, h =>
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    haveI := P.inf_liesOver v h
    (infLocalTransition K p.1 q.1 (P.inf v p) (P.inf v q) n).hom.toAddMonoidHom
  | .inr v, p, q, h =>
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    haveI := P.fin_liesOver v h
    (localTransition K p.1 q.1 (P.fin v p) (P.fin v q) n).hom.toAddMonoidHom


theorem shapiro_placeProj_inr (v : HeightOneSpectrum (𝓞 K.1)) (p : GLevel K)
    (y : cohomology (ideleRep K.1 p.1.1) n) :
    P.shapiro n (.inr v) p ((cohomologyMap (placeProj (.inr v)) n).hom y) =
      (finiteComponent (P.fin v p) n).hom y := by
  change (finiteShapiroIso v (P.fin v p) n).hom.hom
    ((cohomologyMap (finiteProjAboveRep (K := K.1) (L := p.1.1) v) n).hom y) = _
  rw [← placeProj_comp_finiteShapiroIso (P.fin v p) n]
  rfl


theorem shapiro_placeProj_inl (v : InfinitePlace K.1) (p : GLevel K)
    (y : cohomology (ideleRep K.1 p.1.1) n) :
    P.shapiro n (.inl v) p ((cohomologyMap (placeProj (.inl v)) n).hom y) =
      (infiniteComponent (P.inf v p) n).hom y := by
  change (infiniteShapiroIso v (P.inf v p) n).hom.hom
    ((cohomologyMap (infiniteProjAboveRep (K := K.1) (L := p.1.1) v) n).hom y) = _
  rw [← placeProj_comp_infiniteShapiroIso (P.inf v p) n]
  rfl



def levelDecomposition : LevelDecomposition K n where
  L := P.localGroup n
  e := P.shapiro n
  lt := P.transition n
  compat v p q h y := by
    rcases v with v | v
    · haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      haveI := P.inf_liesOver v h
      rw [shapiro_placeProj_inl, shapiro_placeProj_inl]
      exact congrArg (fun φ => φ.hom y)
        (levelTransition_comp_infiniteComponent (P.inf v p) (P.inf v q) n)
    · haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      haveI := P.fin_liesOver v h
      rw [shapiro_placeProj_inr, shapiro_placeProj_inr]
      exact congrArg (fun φ => φ.hom y)
        (levelTransition_comp_finiteComponent (P.fin v p) (P.fin v q) n)

end CompatiblePlaces

end

end GroundTheory.ProfCoh
