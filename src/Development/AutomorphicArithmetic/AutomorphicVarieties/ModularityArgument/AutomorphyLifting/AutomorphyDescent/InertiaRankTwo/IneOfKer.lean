module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.DownCsdK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FinChar
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Z.Win
open UpperTheory.V.Z.Win.Dn

theorem UpperTheory.V.Z.Win.Dn.ineOfKer_of :
    IneOfKer := by
  intro F Ω _ _ _ _ _ l _ n r h v hv A hA
  have hn : ¬ A.valuation (l : Ω) < 1 := fun e => hv ((hA (l : 𝓞 F)).1 (by simpa only [map_natCast] using e))
  obtain ⟨χ, hc, hf, hk⟩ := h A hn
  obtain ⟨j, hj⟩ := UpperTheory.V.Lib.FinChar.charpoly_of_ker r χ (Ine (F := F) A) hf hk
  refine ⟨fun i => (χ.comp (Dec (F := F) A).subtype) ^ j i, fun i => ?_, fun g hg => ?_⟩
  · exact (hc.comp continuous_subtype_val).pow (j i)
  · refine (hj _ hg).trans (Finset.prod_congr rfl fun i _ => ?_)
    simp
