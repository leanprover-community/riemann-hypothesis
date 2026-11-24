module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwJumps
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

theorem UpperTheory.Gal.Int.Geo.twJ :
    UpperTheory.Gal.Int.Geo.TwJ := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ hρ hχ w c m h1 Q hQ P AI hT A hA O _ _ _ Bw hj τ LL' τ' hi
  obtain ⟨J, hJ, hJQ⟩ := hQ P AI hT A hA O Bw hj τ LL' τ' hi
  obtain ⟨-, -, j1, -⟩ := h1.2 P AI hT A hA O Bw hj
  have e1 : (rk1 χ).comp (Dec (F := E) A).subtype = rk1 (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw ρ χ).comp (Dec (F := E) A).subtype =
      tw (ρ.comp (Dec (F := E) A).subtype) (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  have j2 := j1 τ LL' τ' hi
  rw [e1] at j2
  have cs : Continuous (ρ.comp (Dec (F := E) A).subtype) := hρ.comp continuous_subtype_val
  have cμ : Continuous (χ.comp (Dec (F := E) A).subtype) := hχ.comp continuous_subtype_val
  refine ⟨J.map (· + m (ι.toRingHom.comp τ)), ?_, fun j hj' => ?_⟩
  · rw [e2]
    exact UpperTheory.Gal.TP.Sub.twJumps_holds l P AI hT E Ω A O Bw dd _ _ cs cμ τ J _ hJ j2
  · exact Multiset.mem_map.2 ⟨_, hJQ _ hj', by simp⟩
