module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open Polynomial IsDedekindDomain NumberField IsLocalRing
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcVal.AriEta

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_int (x : 𝓞 F) : Valued.v (((x : F) : v.adicCompletion F)) ≤ 1 := by
  have h : Valued.v (((x : F) : v.adicCompletion F)) = v.valuation F (x : F) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [h]
  exact v.valuation_le_one x

theorem val_int_lt (x : 𝓞 F) (hx : x ∈ v.asIdeal) : Valued.v (((x : F) : v.adicCompletion F)) < 1 := by
  have h : Valued.v (((x : F) : v.adicCompletion F)) = v.valuation F (x : F) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [h]
  exact (v.valuation_lt_one_iff_mem x).mpr hx

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Formalism.L2.SG.Pf.NcVal.AriEta
