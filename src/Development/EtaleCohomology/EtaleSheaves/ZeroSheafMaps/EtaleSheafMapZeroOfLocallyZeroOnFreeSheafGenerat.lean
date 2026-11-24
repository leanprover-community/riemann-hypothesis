module

public import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps
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
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShMapZeroPf.Gen
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf

abbrev F0 (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ SShv B q :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q))) ⋙ presheafToSheaf (EtTop B) _

def e0 (B : Scheme.{0}) (q : ℕ) : OU B q ⋙ DerivedCategory.homologyFunctor (SShv B q) 0 ≅ F0 B q :=
  Functor.isoWhiskerLeft (F0 B q) (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0) ≪≫ Functor.rightUnitor _

def EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (H H' : SShv B q) (g : H ⟶ H'),
  (∀ (U : B.Etale) (t : (F0 B q).obj U ⟶ H), Cov U (fun U' a => (F0 B q).map a ≫ t ≫ g = 0)) → g = 0

theorem LeafGen_of (hG : EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators) : LeafGen := by
  intro B q H H' g h
  apply hG B q H H' g
  intro U t
  refine (h U ((e0 B q).hom.app U ≫ t)).mono fun U' a ha => ?_
  have n : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ (e0 B q).hom.app U =
      (e0 B q).hom.app U' ≫ (F0 B q).map a := (e0 B q).hom.naturality a
  rw [← cancel_epi ((e0 B q).hom.app U'), comp_zero, ← Category.assoc, ← n, Category.assoc]
  exact ha

end LateralTheory.E.LeafShMapZeroPf.Gen
