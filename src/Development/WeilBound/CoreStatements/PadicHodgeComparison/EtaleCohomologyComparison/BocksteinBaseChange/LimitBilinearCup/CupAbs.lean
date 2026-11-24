module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open TensorProduct CategoryTheory

namespace CrystallineSemistableComparison.CupAbs

universe w₁ w₂ w₃ u₁ u₂ u₃

section BC

variable {R : Type} [CommRing R] (A : Type) [CommRing A] [Algebra R A]
  {M : Type u₁} {N : Type u₂} {P : Type u₃} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

end BC

section Lim

variable {R : Type} [CommRing R] {S₁ : Sys.{w₁} R} {S₂ : Sys.{w₂} R} {S₃ : Sys.{w₃} R}

end Lim

section One

theorem mapH_cls' {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w₁} R} {L : Cx.{w₂} R'}
    (φ : Cx.Hom K L σ) (n : ℕ) (a : K.X n) (ha : K.d n a = 0) (b : L.X n) (hb : L.d n b = 0) (e : φ.f n a = b) :
    φ.mapH n (K.cls a ha) = L.cls b hb := by
  subst e
  exact CrystallineSemistableComparison.P.mapH_cls φ n a ha hb

theorem pull_one {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u₁} [Category.{u₂} C]
    {C' : Type u₃} [Category.{w₃} C'] {A : C ⥤ CommAlgCat.{w₁} R} {A' : C' ⥤ CommAlgCat.{w₂} R'}
    (m : CH.Mor (CH.modF A) (CH.modF A') σ) (h1 : ∀ T, m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' :=
  mapH_cls' m.hom 0 _ _ _ _ (funext fun _ => h1 _)

end One

end CrystallineSemistableComparison.CupAbs
