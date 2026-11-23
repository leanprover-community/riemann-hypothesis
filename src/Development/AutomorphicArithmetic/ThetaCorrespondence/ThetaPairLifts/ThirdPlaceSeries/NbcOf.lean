module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutQuot
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
variable {L n}
variable (L n)
variable {L n}
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end GlobalTheory.AutQuot
end
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutQuot
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
open Classical in
def locOf_alt (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) : D.naut.LP w :=
  if h : ∃ x, LocAt π w x then (T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) h.choose)
  else D.naut.lpZero w

def boundaryConditionOfNoLocal (hE : IsEmpty D.nd.Loc) : NBC D.naut where
  AU := fun _ => AUq D.host.E D.R.nV
  multAU := fun _ X => X.rep.mult
  sphAU := fun _ X w => ∃ v, NG.OverPl w v ∧ X.rep.SphAt v
  locAU := fun _ X w => _root_.GlobalTheory.AutQuot.locOf_alt hL D T X.rep w
  satAU := fun _ X w => satOf X.rep w
  satAU_card := fun _ X w => satOf_card X.rep w
  Wt := fun _ => WtQ D.host.E D.R.nV
  infW := fun _ Y τ => NG.infOf (hwOf Y.rep τ)
  infW_card := fun _ Y τ => infOf_card _
  wtAU := fun _ X => wtOf D X.rep
  infW_alg := fun _ Y τ => infOf_nodup_alg (hwOf_antitone Y.rep τ)
  embAV := fun i => isEmptyElim i
  embAV_inj := fun i => isEmptyElim i
  embAV_loc := fun i => isEmptyElim i
  embAV_sat := fun i => isEmptyElim i
  embAV_sph := fun i => isEmptyElim i
  embAV_inf := fun i => isEmptyElim i
end GlobalTheory.AutQuot
end
end
