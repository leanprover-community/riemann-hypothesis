module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedDieudonneFunctorQuasiLogarithmsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleDieudonneBaseByCartierDualityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDieudonneFunctorGluedConnectedEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVerschiebungOfDieudonneFunctorBaseStatement
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

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

def theory (p : ℕ) [Fact p.Prime] : Theory p :=
  let Bc := (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose
  let Be := (GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality p Bc).choose
  let hB := GlobalTheory.T.exists_dieudonneFunctor_glued_connected_etale p Bc Be (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose_spec (GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality p Bc).choose_spec
  let hV := GlobalTheory.T.exists_verschiebung_of_dieudonneFunctorBase p hB.choose
  { base := hB.choose, katz := hB.choose_spec.1, etDual := hB.choose_spec.2, V := hV.choose,
    F_V := hV.choose_spec.1, V_F := hV.choose_spec.2 }

end GlobalTheory.Dieu
