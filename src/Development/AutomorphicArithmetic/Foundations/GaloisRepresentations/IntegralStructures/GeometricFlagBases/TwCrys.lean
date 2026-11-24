module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwLoc
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

theorem UpperTheory.Gal.Int.Geo.twCrys :
    UpperTheory.Gal.Int.Geo.TwCrys := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hχ hρ P AI hT A h O _ _ _ Bw hj
  obtain ⟨c1, -, -, -⟩ := hχ.2 P AI hT A h O Bw hj
  have c2 := hρ P AI hT A h O Bw hj
  have e1 : (rk1 χ).comp (Dec (F := E) A).subtype = rk1 (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw ρ χ).comp (Dec (F := E) A).subtype =
      tw (ρ.comp (Dec (F := E) A).subtype) (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  rw [e1] at c1
  rw [e2]
  exact (UpperTheory.Gal.TP.Sub.twLoc_holds l P AI hT E Ω A O Bw dd (ρ.comp (Dec (F := E) A).subtype)
    (χ.comp (Dec (F := E) A).subtype)).2 c2 c1
