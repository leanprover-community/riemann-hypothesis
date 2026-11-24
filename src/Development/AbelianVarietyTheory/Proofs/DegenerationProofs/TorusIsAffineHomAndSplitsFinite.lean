module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialise
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineHomOfIsAffineHomPullbackSndOfFpqc
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem torus_isAffineHom_and_splits_finite : NaSt.{0} := by
  intro k _ T _ hT
  obtain ⟨Ω, _, _, X, _, _, _, e, he⟩ := hT.splits
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    ⟨fun x => ⟨(default : Spec (.of Ω)), Subsingleton.elim (α := Spec (.of k)) _ _⟩⟩
  have haff : IsAffineHom T.hom := by
    refine isAffineHom_of_isAffineHom_pullback_snd_of_fpqc _ _ _ T.hom _ hsurj hflat inferInstance ?_
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h : IsAffineHom (e.hom.left ≫ (splitTorus (Spec (.of Ω)) X).hom) := inferInstance
    rw [Over.w] at h
    exact h
  refine ⟨haff, ?_⟩
  obtain ⟨k', _, _, _, e', he'⟩ := IsoFinite.exists_finite_iso k Ω T (splitTorus (Spec (.of k)) X)
    haff inferInstance hT.finiteType inferInstance
    ⟨e ≪≫ (Diag.baseChangeIso _ X).symm,
      inferInstanceAs (IsMonHom (e.hom ≫ (Diag.baseChangeIso _ X).inv))⟩
  exact ⟨k', inferInstance, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
    e' ≪≫ Diag.baseChangeIso _ X, inferInstanceAs (IsMonHom (e'.hom ≫ (Diag.baseChangeIso _ X).hom))⟩

end GlobalTheory
