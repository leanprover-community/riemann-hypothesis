module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Final
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.BInEx
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.EndEx
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.PinFixed
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

open CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

theorem cIn (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K) (f : ℕ)
    (hf : 0 < f) : CIn l K r f := by
  obtain ⟨N, h1, h2, F, h3⟩ := CrystallineSemistableComparison.crystallineComparison.pinEx l K r f hf
  obtain ⟨Amp, -, -, -, a1, a2, a3, a4, a5, -⟩ := CrystallineSemistableComparison.crystallineComparison.endEx (fun l _ K _ => UpperTheory.Gal.KunnethLefschetz.Top.etSide_sm_holds l K) l K
  exact ⟨Amp, N, F, a1, a2, a3, a4, a5, h1, h2, fun M hM j => ⟨h3 M hM j, CrystallineSemistableComparison.crystallineComparison.bInEx l K M hM j⟩⟩

end UpperTheory.Ru.crystallineComparison
