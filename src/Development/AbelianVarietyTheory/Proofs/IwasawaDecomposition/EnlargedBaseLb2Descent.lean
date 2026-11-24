module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.HkCopy

theorem exists_units_copy {T T' Q Q' : Type} {O : T → Type} {O' : T' → Type} [c : ∀ i, CommRing (O i)]
    [c' : ∀ i, CommRing (O' i)] (hT : T = T') (hO : HEq O O') (hc : HEq c c') (hQ : Q = Q')
    (f : ∀ (i : T) (_b : Bool) (_P : Q), (O i)ˣ) :
    ∃ f' : ∀ (i : T') (_b : Bool) (_P : Q'), (O' i)ˣ,
      ∀ (i : T) (i' : T') (b : Bool) (P : Q) (P' : Q'), HEq i i' → HEq P P' → HEq (f' i' b P') (f i b P) := by
  subst hT; cases hO; cases hc; subst hQ
  exact ⟨f, fun i i' b P P' hi hP => by cases hi; cases hP; rfl⟩

theorem plE_eq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') : PlE H = PlE H' := by
  subst hR; cases hH; rfl

theorem exists_cHk_copy {D D' : D7} (h : GlobalTheory.TwistChoice.SameExport D D')
    (f : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) :
    ∃ f' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ,
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (b : Bool) (P : PlE D.host) (P' : PlE D'.host), HEq i i' → HEq P P' →
        HEq (f' i' b P') (f i b P) :=
  exists_units_copy (eq_of_heq h.set.Tw) h.set.O h.set.crO (plE_eq h.gal.R h.gal.host) f

end GlobalTheory.HeightCounting.Up.HkCopy
