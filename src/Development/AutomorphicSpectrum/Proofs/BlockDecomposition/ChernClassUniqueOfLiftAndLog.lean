module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.MapUgCToUg
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtChern

theorem restrict_id_pull {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (x : H (𝟭 C ⋙ F) 2) (x' : H F 2)
    (h : x = (Mor.restrict F (𝟭 C)).pull 2 x') : x = x' := by
  subst h
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  rfl

theorem chern_class_unique_of_lift_and_log : CrystallineSemistableComparison.E.LiftEx → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.FirstChernUniqueEtale := by
  intro hL hG l _ H O _ X q κ D hE y y' hy hy'
  obtain ⟨Λ⟩ := (hL l H O X q κ (El (PX q κ)) (𝟭 _) D).2 hE
  funext n
  obtain ⟨z, hz, hc, e⟩ := hy (El (PX q κ)) (𝟭 _) Λ n
  obtain ⟨z', hz', hc', e'⟩ := hy' (El (PX q κ)) (𝟭 _) Λ n
  have hzz : z = z' := by
    funext s
    exact (hG l _ n).2.1 _ _ _ (hc s) (hc' s)
  subst hzz
  have e1 := restrict_id_pull _ _ _ e
  have e2 := restrict_id_pull _ _ _ e'
  exact e1.symm.trans e2

end GlobalTheory.CompanionTheory.EtChern
