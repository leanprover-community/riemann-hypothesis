module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeBelow
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Untw

theorem exists_below_of_range (D D' : D7) (h : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (v' : D'.what₂.places.Pl) :
    ∃ v : D.what₂.places.Pl, Below D D' v v' := by
  first
  | exact @_root_.GlobalTheory.PrimeBelow.exists_below
  | exact _root_.GlobalTheory.PrimeBelow.exists_below
  | (apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeBelow.exists_below <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeBelow.exists_below ..)

theorem resChar_of_below {D D' : D7} {v : D.what₂.places.Pl} {v' : D'.what₂.places.Pl} (hB : Below D D' v v') :
    D'.what₂.places.resChar v' = D.what₂.places.resChar v := by
  refine GlobalTheory.LvT.Inh.resChar_eq_of_mem_plEq D' v' (D.what₂.places.resChar_prime v) ((hB _ _ ?_).1 (GlobalTheory.LvT.Inh.resChar_mem_plEq D v))
  simp only [map_natCast]

end GlobalTheory.Mem.R3.Rw.Untw

namespace GlobalTheory.Mem.R3.Rw

end GlobalTheory.Mem.R3.Rw

end
