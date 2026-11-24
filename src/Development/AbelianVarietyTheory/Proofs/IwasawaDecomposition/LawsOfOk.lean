module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDecoStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditionsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrimeStatement
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC



theorem laws_of_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws := by
  intro B X I h
  have hch := GlobalTheory.T.trueColumn_chains_satisfy_conditions I h
  have hlev := GlobalTheory.T.levelPrimeData_ok_of_trueColumnChoices I h
  have hper := GlobalTheory.T.trueColumns_periodMapDatum_ok_and_over_levelPrime I h
  have hall := fun u a => laws_all (I.chIn u a) (I.atIn u a) B.fields.emb B.embLL (B.hcW u) (base_fOk B) (hch u a).1 (hlev u a)
    (I.perIn u a) (hper u a).1 B.places
  exact
    { pr := (base_fields_primes_ok B X).2.1
      ch := fun u a => (hch u a).1
      lev := hlev
      per := fun u a => (hper u a).1
      ovr := fun u a => (hper u a).2
      atL := fun u a => (hall u a).1
      fmL := fun u a => (hall u a).2
      xi0 := h.trueColumnChoices_heckeChar_reference_eq_one
      idx0 := fun a => (hch B.u₀ a).2.1
      bij0 := fun u a b => (GlobalTheory.T.cl0_bijective_and_deco_eq I h u a b).1
      lat := fun u a => (hch u a).2.2 }

end GlobalTheory.Mem.Col2.TC
