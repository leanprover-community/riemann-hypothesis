module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlowUpFibreSemilocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.Int.Geo.jumpsOf :
    UpperTheory.Gal.Int.Geo.JumpsOf := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ρ w Q hQ hJ P AI hT A hA O _ _ _ Bw hBw τ LL' τ' hi lam J hl hJm
  obtain ⟨J', h1, h2⟩ := hJ P AI hT A hA O Bw hBw τ LL' τ' hi
  have e : J = (GlobalTheory.RoadWGeo.wtJumps lam).val :=
    Multiset.map_injective Int.cast_injective (hJm.trans (GlobalTheory.RoadWGeo.wtJumps_val lam).symm)
  refine ⟨J', h1, fun j hj => h2 j (hQ _ (GlobalTheory.CongL.LimAtLU.overPl_of_induced ι hA hBw hi) lam hl j ?_)⟩
  rw [e] at hj
  exact hj
