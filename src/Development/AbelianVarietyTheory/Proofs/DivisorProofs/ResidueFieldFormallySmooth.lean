module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
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
public import Mathlib.RingTheory.Smooth.Field
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct

theorem GlobalTheory.residueField_formallySmooth_of_isClosed :
    ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k)
      [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U),
      IsClosed ({x} : Set X) →
        (letI : Algebra k (X.presheaf.stalk x) :=
          ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
         Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
  intro k _ _ X f _ U x hxU _
  letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  have key : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hxU =
      (Sp k).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.germ_stalkMap f ⊤ x trivial]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have hS0 : ∀ p : PrimeSpectrum k, (StructureSheaf.toStalk k p).hom.EssFiniteType := by
    intro p
    have := StructureSheaf.IsLocalization.to_stalk k p
    have := Algebra.EssFiniteType.of_isLocalization (R := k)
      ((Spec.structureSheaf k).presheaf.stalk p) p.asIdeal.primeCompl
    exact RingHom.essFiniteType_algebraMap.mpr this
  have hS : (StructureSheaf.toStalk k (f x)).hom.EssFiniteType := hS0 (f x)
  have hT : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial =
      StructureSheaf.toStalk k (f x) := by
    rw [Scheme.ΓSpecIso_inv]
    exact AlgebraicGeometry.StructureSheaf.algebraMap_germ _ _ _
  have hφ : algebraMap k (X.presheaf.stalk x) =
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial) ≫
        f.stalkMap x).hom := by
    show ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)) = _
    rw [cstOn, ← CommRingCat.hom_comp, Category.assoc, Category.assoc, key]
  have hS' : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Sp k).presheaf.germ ⊤ (f x) trivial).hom.EssFiniteType := hT ▸ hS
  have hR : (IsLocalRing.residue (X.presheaf.stalk x)).FiniteType :=
    RingHom.FiniteType.of_surjective _ IsLocalRing.residue_surjective
  have hE : (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))).EssFiniteType := by
    have h : algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) =
        (IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap k (X.presheaf.stalk x)) := rfl
    rw [h, hφ, CommRingCat.hom_comp]
    exact (hS'.comp (LocallyOfFiniteType.stalkMap f x)).comp hR.essFiniteType
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    RingHom.essFiniteType_algebraMap.mp hE
  exact Algebra.FormallySmooth.of_perfectField
