module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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

namespace ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

attribute [local instance] Over.cartesianMonoidalCategory

def extendGenSt : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (eA : Spec (CommRingCat.of K) ⟶ genA V K G), eA ≫ jA V K G = eK V K G →
    ∀ (N : RigLB G) (r : LB.Gen (N.L.pull (jA V K G))), r.IsGen →
    LB.Gen.Corr N.L _ _ _ _ (LB.pullGen N.L _ _ r eA) (LB.pullGen N.L _ _ N.rig (etaK V K)) →
    ∃! r' : LB.Gen N.L, r'.IsGen ∧ LB.genPull N.L r' (jA V K G) = r

def extend_existsSt : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (eA : Spec (CommRingCat.of K) ⟶ genA V K G), eA ≫ jA V K G = eK V K G →
    ∀ (L : LB (genA V K G)), L.IsLB → ∀ (ρ : LB.Gen (L.pull eA)), ρ.IsGen →
    ∃ (L' : RigLB G) (φ : LB.Iso (L'.L.pull (jA V K G)) L), φ.IsGen

def cubical_extendsSt : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (selfLieBasisVector : Spec (CommRingCat.of K) ⟶ pullback (G3 G).hom (etaK V K)),
    selfLieBasisVector ≫ genericFiberCubeInclusion V K G = etaK V K ≫ eSec (G3 G) →
    ∀ (L : RigLB G) (t : LB.Gen (LB.LinComb L.L (fun I => genericFiberCubeInclusion V K G ≫ thφ G (x3 G) I) thε)),
    LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ t selfLieBasisVector) (LB.oneGen L.L) →
    t.IsGen →
    ∃! c : LB.Gen (Theta G L.L), c.IsGen ∧ LB.pullGen L.L _ _ c (genericFiberCubeInclusion V K G) = t

def lemmaBSt : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (N : LB G.left), N.IsLB → ∀ (s : LB.Sec N) (π : V), Irreducible π →
    (∀ i (e : ℕ), s.f i ∈ Ideal.span (Set.singleton ((G.left.presheaf.map (homOfLE (le_top :
        N.U i ≤ ⊤)).op).hom ((G.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom π)))) ^ e) →
    ∀ i, s.f i = 0

end

end ReciprocityTheory.ChartRestriction.G.Semi
